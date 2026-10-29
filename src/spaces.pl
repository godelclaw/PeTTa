:- dynamic space_primitive/2.

%compiled_row(RowRef, ClauseRef): this stored row supports the compiled clause.
%Imported copies share a clause; explicit duplicate equations have distinct clauses.
:- dynamic compiled_row/2.
:- dynamic source_row/2.

%Nonempty expressions keep their indexed rows; other atoms are stored separately.
%An unbound atom still raises an instantiation error:
add_sexp(Space, Atom) :- add_sexp(Space, Atom, _).
add_sexp(Space, Atom, Ref) :- ( var(Atom) -> instantiation_error(Atom)
                             ; Atom = [Rel|Args] -> Term =.. [Space, Rel | Args], assertz(Term, Ref)
                             ; must_be(atom, Space), assertz(space_primitive(Space, Atom), Ref) ).

%Same but for removal, of one row the atom unifies with, even when the same
%atom is stored twice. Removed says whether there was one: the retract decides
%it atomically, so of several threads removing the same row exactly one is told
%true. Pattern variables stay unbound:
remove_sexp(Space, Atom) :- remove_sexp(Space, Atom, _).
remove_sexp(Space, Atom, Removed) :- ( var(Atom) -> instantiation_error(Atom)
                                    ; Atom = [Rel|Args] -> Term =.. [Space, Rel | Args]
                                    ; must_be(atom, Space), Term = space_primitive(Space, Atom) ),
                                    ( \+ \+ retract(Term) -> Removed = true
                                                          ; Removed = false ).

%Add a function atom. Definitions are added and removed under one lock, so a
%removal never takes a row before its clause support is recorded:
'add-atom'(Space, Term, true) :- Term = [Eq,[FAtom|W],_], Eq == (=), atom(FAtom), !,
                                 with_mutex(petta_definitions, add_function_atom(Space, Term, FAtom, W)).

%Add an atom to the space:
'add-atom'(Space, Term, true) :- add_sexp(Space, Term).

add_function_atom(Space, Term, FAtom, W) :- add_sexp(Space, Term, RowRef),
                                            register_fun(FAtom),
                                            length(W, N),
                                            Arity is N + 1,
                                            assertz(arity(FAtom,Arity)),
                                            once(translate_clause(Term, Clause)),
                                            assertz(Clause, Ref),
                                            assertz(translated_from(Ref, Term)),
                                            assertz(compiled_row(RowRef, Ref)),
                                            notify_function_changed(FAtom),
                                            maybe_print_compiled_clause("added function", Term, Clause).

%%A removal that may take definitions of an unknown function must not erase
%%program rows:
'remove-atom'(_, Term, _) :- may_take_definition(Term, F), var(F), !, instantiation_error(F).

%%Remove an atom that may be a definition. The row taken from this space
%%decides the answer, as for any atom. Its clause goes only when no supporting
%%row remains: (= $h 1) is data, while imported copies share a clause.
%%An unbound operator, as in ($op (f 1) 2), may take data or a definition:
'remove-atom'(Space, Term, Removed) :- may_take_definition(Term, F), atom(F), !,
                                       with_mutex(petta_definitions, remove_function_atom(Space, Term, F, Removed)).

%Remove one same atom, reporting whether there was one, as for a function atom:
'remove-atom'(Space, Term, Removed) :- remove_sexp(Space, Term, Removed).

%A pattern may take a definition when it has three elements, its operator is =
%or unbound, and its head is unbound or an expression. F is the function name,
%unbound if unknown. The test binds nothing in the pattern:
may_take_definition(Term, F) :- is_list(Term), Term = [Eq, Head, _], ( var(Eq) -> true ; Eq == (=) ),
                                ( var(Head) -> true ; Head = [F|_] ).

%Taking the row binds a copy of the pattern, never the pattern itself:
remove_function_atom(Space, Term, F, Removed) :- copy_term(Term, [Rel|Args]), Row =.. [Space, Rel|Args],
                                                 ( take_row(Row, ClauseRef, Compiled)
                                                   -> Removed = true,
                                                      ( Compiled == true
                                                        -> erase_owned_clause(ClauseRef),
                                                           notify_function_changed(F),
                                                           ( \+ ( user_dynamic_head(F, _, H2), clause(H2, _, _) )
                                                             -> retractall(fun(F)), notify_function_removed(F)
                                                             ; true )
                                                      ; true )
                                                 ; Removed = false ).

%Only dynamic predicates defined in user hold compiled MeTTa clauses; static or
%imported built-ins of the same name (such as plus/3 or nl/0) are skipped:
user_dynamic_head(F, A, Head) :- current_predicate(F/A),
                                 functor(Head, F, A),
                                 predicate_property(Head, dynamic),
                                 \+ predicate_property(Head, imported_from(_)).

%Take the first row that Row unifies with and that no other thread took first,
%and whether its clause lost its last support. Erasing the row is the claim.
take_row(Row, ClauseRef, Compiled) :- clause(Row, true, RowRef), erase(RowRef),
                                      retractall(source_row(_, RowRef)),
                                      ( retract(compiled_row(RowRef, ClauseRef))
                                        -> ( compiled_row(_, ClauseRef) -> Compiled = false ; Compiled = true )
                                      ; Compiled = false ).

%Erase the clause whose last supporting row was removed, and its record:
erase_owned_clause(ClauseRef) :- retractall(translated_from(ClauseRef, _)), erase(ClauseRef).

%Compile F's clauses again where they are, each from a supporting row, so
%that a change in how calls compile (memoization) reaches them while the rows,
%their order and their spaces stay as they were. A bound CallArity limits this
%to the clauses taking that many arguments. Existing memo entries stay valid:
recompile_function_rows(F, CallArity) :-
    with_mutex(petta_definitions,
               ( compiled_function_predicate_arities(F, CallArity, Arities),
                 forall(member(A, Arities), recompile_function_arity(F, A)) )).

compiled_function_predicate_arities(F, CallArity, Arities) :-
    findall(A,
            ( compiled_row(_, Ref),
              clause(Head, _, Ref),
              functor(Head, F, A),
              ( var(CallArity) -> true ; A =:= CallArity + 1 ),
              predicate_property(Head, dynamic),
              \+ predicate_property(Head, imported_from(_)) ),
            Arities0),
    sort(Arities0, Arities).

%Translate first, then swap the clauses in one transaction, so that callers in
%other threads see the old clauses or the new ones:
recompile_function_arity(F, A) :-
    functor(Head, F, A),
    findall(Ref, clause(Head, _, Ref), Refs),
    maplist(recompiled_clause, Refs, Items),
    transaction(( forall(member(Ref, Refs), ( retractall(translated_from(Ref, _)), erase(Ref) )),
                  maplist(assert_recompiled_clause, Items) )).

%A supported clause is translated again from a stored row, retaining all its
%support links; any other clause is kept as it is:
recompiled_clause(Ref, row(Rows, Term, Clause)) :- findall(R, compiled_row(R, Ref), Rows),
                                                    Rows = [RowRef|_], clause(Row, true, RowRef), !,
                                                    Row =.. [_|Term],
                                                    once(translate_clause(Term, Clause)).
recompiled_clause(Ref, kept((Head :- Body), Source)) :- clause(Head, Body, Ref),
                                                      ( translated_from(Ref, Source) -> true ; Source = none ).

assert_recompiled_clause(row(Rows, Term, Clause)) :- assertz(Clause, Ref),
                                                      assertz(translated_from(Ref, Term)),
                                                      forall(member(RowRef, Rows),
                                                             ( retractall(compiled_row(RowRef, _)),
                                                               assertz(compiled_row(RowRef, Ref)) )).
assert_recompiled_clause(kept(Clause, Source)) :- assertz(Clause, Ref),
                                                 ( Source == none -> true ; assertz(translated_from(Ref, Source)) ).

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
                                                         ; Head = [_|_] -> Term =.. [Space|Head], space_call(Term)
                                                         ; must_be(atom, Space), space_primitive(Space, Head) ),
                                                         \+ cyclic_term(OutPattern),
                                                         match(Space, [','|Tail], OutPattern, Result).

% When the pattern list itself is a variable -> enumerate all atoms
match(Space, PatternVar, OutPattern, Result) :- var(PatternVar), !,
                                                'get-atoms'(Space, PatternVar),
                                                \+ cyclic_term(OutPattern),
                                                Result = OutPattern.

%Match for pattern:
match(Space, Pattern, OutPattern, Result) :- ( Pattern = [Rel|PatArgs]
                                             -> Term =.. [Space, Rel | PatArgs], space_call(Term)
                                              ; must_be(atom, Space), space_primitive(Space, Pattern) ),
                                             \+ cyclic_term(OutPattern),
                                             Result = OutPattern.

%Get all atoms in space, irregard of arity:
'get-atoms'(Space, Pattern) :- space_primitive(Space, Pattern).
'get-atoms'(Space, Pattern) :- current_predicate(Space/Arity),
                               functor(Head, Space, Arity),
                               clause(Head, true),
                               Head =.. [Space | Pattern].
