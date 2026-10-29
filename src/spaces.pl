:- dynamic space_primitive/2.

%compiled_row(RowRef, ClauseRef): the stored row owns this exact compiled clause.
%A definition imported into a second space is stored there without one.
:- dynamic compiled_row/2.

%Since both normal add-attom call and function additions needs to add the S-expression:
%Nonempty expressions keep their indexed rows; other atoms are stored separately, so
%no expression value is reserved as a marker. An unbound atom raises an instantiation error.
add_sexp(Space, TermIn) :- add_sexp(Space, TermIn, _).
add_sexp(Space, TermIn, Ref) :-
    ( var(TermIn) ->
        instantiation_error(TermIn)
    ; is_list(TermIn), TermIn = [Rel|Args] ->
        Term =.. [Space, Rel | Args],
        assertz(Term, Ref),
        maybe_cache_type_decl(Space, [Rel|Args])
    ;
        must_be(atom, Space),
        assertz(space_primitive(Space, TermIn), Ref)
    ).

%Same but for removal, of every row the atom unifies with. Removed says whether
%there was one:
remove_sexp(Space, TermIn) :- remove_sexp(Space, TermIn, _).
remove_sexp(Space, TermIn, Removed) :-
    ( var(TermIn) ->
        instantiation_error(TermIn)
    ; is_list(TermIn), TermIn = [Rel|Args] ->
        Term =.. [Space, Rel | Args],
        retract_reporting(Term, Removed),
        maybe_uncache_type_decl(Space, [Rel|Args])
    ;
        must_be(atom, Space),
        retract_reporting(space_primitive(Space, TermIn), Removed)
    ).

%The first retract decides the report atomically, so of several threads removing
%the same row exactly one is told true. Pattern variables stay unbound.
retract_reporting(Term, Removed) :-
    ( \+ \+ retract(Term) -> retractall(Term), Removed = true
                          ; Removed = false ).

%%An unbound atom would match every row, so it is not added:
'add-atom'(_, Term, _) :- var(Term), !, instantiation_error(Term).

%Add a function atom. On failure or exception it rolls back its staged raw
%atom, registration, metadata and compiled-dependency state. It runs under the
%lock that definition changes share (notify_mutations/1), so removals never see
%the interval between staging and cleanup; other observers still can.
'add-atom'(Space, Term, true) :- Term = [Eq,[FAtom|W],_], Eq == (=), atom(FAtom), !,
                                 with_mutex(petta_dependency_graph,
                                            add_function_atom(Space, Term, FAtom, W)).

%Add an atom to the space:
'add-atom'(Space, Term, true) :-
    typed_space_runtime_value_ok(Space, Term),
    add_sexp(Space, Term).

add_function_atom(Space, Term, FAtom, W) :-
    length(W, SourceArity),
    snapshot_runtime_function_add(FAtom, SourceArity, Snapshot),
    catch(
        ( runtime_add_function_tx(Space, Term, FAtom, W, Snapshot)
          -> true
          ; cleanup_runtime_function_add(FAtom, Snapshot),
            fail ),
        Error,
        ( cleanup_runtime_function_add(FAtom, Snapshot),
          throw(Error) )).

runtime_add_function_tx(Space, Term, FAtom, W, Snapshot) :-
    Term = [=, [FAtom|W], TermBody],
    RawTerm =.. [Space, '=', [FAtom|W], TermBody],
    assertz(RawTerm, RawRef),
    % Bindings are undone when a later goal fails or throws, so the staged refs
    % are stored non-backtrackably in the snapshot for the cleanup to erase.
    arg(7, Snapshot, Refs),
    nb_setarg(1, Refs, RawRef),
    maybe_cache_type_decl(Space, Term),
    register_fun(FAtom),
    length(W, N),
    Arity is N + 1,
    assertz(arity(FAtom, Arity)),
    % A runtime clause is translated before its normal mutation notification.
    % Drop any old unified self-summary now so recursive validation cannot
    % consume the pre-add contract from an enclosing batch scope.
    unified_checker_invalidate_event(
        clause_changed(FAtom/N, runtime_preparing)),
    once(translate_clause(Term, Clause, true, Dependencies)),
    assertz(Clause, ClauseRef),
    nb_setarg(2, Refs, ClauseRef),
    assertz(translated_from(ClauseRef, Term)),
    assertz(compiled_row(RawRef, ClauseRef)),
    record_compiled_dependencies(ClauseRef, FAtom/N, Dependencies),
    notify_mutation(clause_changed(FAtom/N, runtime)),
    metta_on_function_changed(FAtom),
    invalidate_specializations(FAtom),
    maybe_print_compiled_clause("added function", Term, Clause).

snapshot_runtime_function_add(F, N,
        runtime_add_snapshot(N, FunFacts, Arities, Recompile,
                             CompiledClauses, CacheEntries,
                             runtime_add_refs(none, none))) :-
    findall(true, fun(F), FunFacts),
    findall(A, arity(F, A), Arities),
    snapshot_recompile_state(F, Recompile),
    snapshot_runtime_function_clauses(F, CompiledClauses),
    unified_checker_cache:unified_summary_cache_snapshot_event(
        clause_changed(F/N, runtime_preparing), CacheEntries).

cleanup_runtime_function_add(F,
        runtime_add_snapshot(N, FunFacts, Arities, Recompile, CompiledClauses,
                             CacheEntries, runtime_add_refs(RawRef, ClauseRef))) :-
    ( ClauseRef \== none
      -> forget_compiled_dependencies(ClauseRef),
         retractall(translated_from(ClauseRef, _)),
         ignore(catch(erase(ClauseRef), _, fail))
    ; true ),
    ( RawRef \== none
      -> retractall(compiled_row(RawRef, _)),
         ignore(catch(erase(RawRef), _, fail))
    ; true ),
    restore_runtime_function_clauses(F, CompiledClauses),
    restore_recompile_state(F, Recompile),
    retractall(fun(F)),
    forall(member(true, FunFacts), assertz(fun(F))),
    retractall(arity(F, _)),
    forall(member(A, Arities), assertz(arity(F, A))),
    % notify_mutation/1 may already have swapped the staged clause and rebuilt
    % callers before a later hook throws.  Replaying the mutation after the
    % exact pre-add source clauses are back brings that dependent cascade into
    % agreement with the restored program.  The cache snapshot is installed
    % afterwards so the original closed contracts survive the failed add.
    ignore(catch(notify_mutation(clause_changed(F/N, runtime)), _, fail)),
    % Recompile analysis may have staged post-add summaries before a later
    % operation failed.  The rollback restored the old program state, so make
    % that failure boundary explicit and conservative.
    unified_checker_cache:unified_summary_cache_store_many(CacheEntries).

snapshot_runtime_function_clauses(F, Clauses) :-
    findall(runtime_compiled_clause(Source, Head, Body, Origin, Dependencies, Owner),
            ( translated_from(Ref, Source),
              runtime_source_key(Source, F/_),
              clause(Head, Body, Ref),
              compiled_dependency_origin(Ref, Origin),
              ( compiled_deps(Ref, _, _, StoredDependencies)
                -> Dependencies = StoredDependencies
              ; Dependencies = [] ),
              ( compiled_row(RowRef, Ref) -> Owner = RowRef ; Owner = none ) ),
            Clauses).

restore_runtime_function_clauses(F, Clauses) :-
    findall(Ref,
            ( translated_from(Ref, Source),
              runtime_source_key(Source, F/_) ),
            CurrentRefs),
    forall(member(Ref, CurrentRefs),
           ( forget_compiled_dependencies(Ref),
             retractall(translated_from(Ref, _)),
             retractall(compiled_row(_, Ref)),
             ignore(catch(erase(Ref), _, fail)) )),
    restore_runtime_compiled_clauses(Clauses).

restore_runtime_compiled_clauses([]).
restore_runtime_compiled_clauses(
        [runtime_compiled_clause(Source, Head, Body, Origin, Dependencies, Owner)
         |Clauses]) :-
    assertz((Head :- Body), Ref),
    assertz(translated_from(Ref, Source)),
    ( Owner == none -> true ; assertz(compiled_row(Owner, Ref)) ),
    runtime_source_key(Source, Key),
    record_compiled_dependencies(Ref, Key, Origin, Dependencies),
    restore_runtime_compiled_clauses(Clauses).

runtime_source_key([Eq, [F|Args], _], F/N) :-
    Eq == (=), atom(F), is_list(Args), length(Args, N).

%%A removal that may take definitions of an unknown function must not erase
%%program rows:
'remove-atom'(_, Term, _) :- may_take_definition(Term, F), var(F), !, instantiation_error(F).

%%Remove atoms that may include definitions. The rows taken from this space
%%decide the answer, as for any atom, and a row takes a clause with it only if
%%it was compiled: (= $h 1) is data, and an imported copy in a second space has
%%no clause. An unbound operator, as in ($op (f 1) 2), takes data and
%%definitions alike. Definition changes share one lock, so a row's clause is
%%never read while a recompilation replaces it:
'remove-atom'(Space, Term, Removed) :- may_take_definition(Term, F), atom(F), !,
                                       Term = [_, [_|Args], Body],
                                       with_mutex(petta_dependency_graph,
                                                  remove_function_atom(Space, Term, F, Args, Body, Removed)).

%Remove all same atoms, reporting whether there were any, as for a function atom:
'remove-atom'(Space, Term, Removed) :-
    typed_space_runtime_value_ok(Space, Term),
    remove_sexp(Space, Term, Removed).

%A pattern may take a definition when it has three elements, its operator is =
%or unbound, and its head is unbound or an expression. F is the function name,
%unbound if unknown. The test binds nothing in the pattern:
may_take_definition(Term, F) :- is_list(Term), Term = [Eq, Head, _], ( var(Eq) -> true ; Eq == (=) ),
                                ( var(Head) -> true ; Head = [F|_] ).

remove_function_atom(Space, Term, F, Args, Body, Removed) :-
    Term = [Rel|RowArgs], Row =.. [Space, Rel|RowArgs],
    findall(ClauseRef-Compiled, take_row(Row, ClauseRef, Compiled), Taken),
    ( Taken == [] -> Removed = false
    ; Removed = true,
      findall(R, member(R-true, Taken), ClauseRefs),
      ( ClauseRefs == [] -> true
      ; forget_function_rows(F, Args, Body, ClauseRefs) ) ).

%Take a row that Row unifies with, and the clause it owns if it was compiled.
%Erasing the row is the claim: of several threads, one takes it.
take_row(Row, ClauseRef, Compiled) :- clause(Row, true, RowRef), erase(RowRef),
                                      ( retract(compiled_row(RowRef, ClauseRef)) -> Compiled = true
                                                                                 ; Compiled = false ).

%Erase the clause a removed row owned, with its record and dependencies:
erase_owned_clause(ClauseRef) :- retractall(translated_from(ClauseRef, _)),
                                 forget_compiled_dependencies(ClauseRef),
                                 erase(ClauseRef).

forget_function_rows(F, Args, Body, ClauseRefs) :-
    ( atom(F), nb_current(F, Prev) -> true ; Prev = [] ),
    (   select(Meta, Prev, Rest),
        Meta = fun_meta(Args0, Body0, _),
        Args0 =@= Args,
        Body0 =@= Body
        -> ( Rest == [] -> nb_delete(F)
                         ; nb_setval(F, Rest) ) ; true ),
    maplist(erase_owned_clause, ClauseRefs),
    metta_on_function_changed(F),
    invalidate_specializations(F),
    length(Args, N),
    ( \+ ( current_predicate(F/A), functor(H2, F, A), clause(H2, _, _) )
      -> retractall(fun(F)), metta_on_function_removed(F)
      ; true ),
    % Callable classification is part of the
    % unified call contract.  Drop the last
    % fun/1 marker before rebuilding callers
    % so they see data syntax, not a stale
    % unknown function call.
    notify_mutation(clause_changed(F/N, runtime)).

%Updates whose row the translator proved against the space's declared schema
%(typed_space_update_goal/4). A function atom keeps its own clause.
'add-atom-proven'(Space, Term, true) :- ( var(Term) -> true ; is_list(Term), Term = [Eq,_,_], Eq == (=) ), !,
                                        'add-atom'(Space, Term, true).
'add-atom-proven'(Space, Term, true) :- add_sexp(Space, Term).

'remove-atom-proven'(Space, Term, Removed) :- may_take_definition(Term, _), !,
                                              'remove-atom'(Space, Term, Removed).
'remove-atom-proven'(Space, Term, Removed) :- remove_sexp(Space, Term, Removed).

%Typed spaces accept open payloads and removal patterns.  At the operation
%boundary reject only a value that has become a definite contradiction; this
%is the runtime counterpart of translator.pl's check_typed_space_value/2, not
%a residual type guard, and it never constrains unresolved fields.
typed_space_runtime_value_ok(Space, Value) :-
    ( atom(Space), declared_space_type(Space, RowT),
      value_definitely_mismatch(Value, RowT)
      -> throw(error(literal_type_mismatch(Value, RowT), typecheck))
    ; true ).

% A space is a predicate per row arity, created by the first add-atom. Reading
% a space before it is written calls an undefined predicate, and every such
% call would search the autoloader before failing. The first call declares the
% space's predicate dynamic instead, so later reads are plain calls on an empty
% predicate; reads of existing spaces pay nothing extra.
space_call(Term) :- catch(Term, E, space_missing(E, Term)).

space_missing(error(existence_error(procedure, Space/Arity), _), Term) :-
    functor(Term, Space, Arity), !,
    dynamic(Space/Arity),
    fail.

%Match for conjunctive pattern
match(_, LComma, OutPattern, Result) :- LComma == [','], !,
                                        Result = OutPattern.
match(Space, [Comma|[Head|Tail]], OutPattern, Result) :- Comma == ',', !,
                                                         ( var(Head) -> 'get-atoms'(Space, Head)
                                                         ; is_list(Head), Head = [_|_] -> append([Space], Head, List), Term =.. List,
                                                                                          space_call(Term)
                                                         ; must_be(atom, Space), space_primitive(Space, Head) ),
                                                         \+ cyclic_term(OutPattern),
                                                         match(Space, [','|Tail], OutPattern, Result).

% When the pattern list itself is a variable -> enumerate all atoms
match(Space, PatternVar, OutPattern, Result) :- var(PatternVar), !,
                                                'get-atoms'(Space, PatternVar),
                                                \+ cyclic_term(OutPattern),
                                                Result = OutPattern.

%Match for pattern:
match(Space, Pattern, OutPattern, Result) :-
    ( is_list(Pattern), Pattern = [Rel|PatArgs] ->
        Term =.. [Space, Rel | PatArgs],
        space_call(Term)
    ;
        must_be(atom, Space),
        space_primitive(Space, Pattern)
    ),
    \+ cyclic_term(OutPattern),
    Result = OutPattern.

%Get all atoms in space, irregard of arity:
'get-atoms'(Space, Pattern) :- space_primitive(Space, Pattern).
'get-atoms'(Space, Pattern) :- current_predicate(Space/Arity),
                               functor(Head, Space, Arity),
                               clause(Head, true),
                               Head =.. [Space | Pattern].
