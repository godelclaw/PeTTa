:- dynamic space_primitive/2.

%compiled_row(RowRef, ClauseRef): this stored row owns this exact compiled clause.
%A definition imported into a second space is stored there without one.
:- dynamic compiled_row/2.

%Nonempty expressions keep their indexed rows; other atoms are stored separately.
%An unbound atom still raises an instantiation error:
add_sexp(Space, Atom) :- add_sexp(Space, Atom, _).
add_sexp(Space, Atom, Ref) :- ( var(Atom) -> instantiation_error(Atom)
                             ; Atom = [Rel|Args] -> Term =.. [Space, Rel | Args], assertz(Term, Ref)
                             ; must_be(atom, Space), assertz(space_primitive(Space, Atom), Ref) ).

%Same but for removal, of every row the atom unifies with. Removed says whether
%there was one: the first retract decides it atomically, so of several threads
%removing the same row exactly one is told true. Pattern variables stay unbound:
remove_sexp(Space, Atom) :- remove_sexp(Space, Atom, _).
remove_sexp(Space, Atom, Removed) :- ( var(Atom) -> instantiation_error(Atom)
                                    ; Atom = [Rel|Args] -> Term =.. [Space, Rel | Args]
                                    ; must_be(atom, Space), Term = space_primitive(Space, Atom) ),
                                    ( \+ \+ retract(Term) -> retractall(Term), Removed = true
                                                          ; Removed = false ).

%Add a function atom. Definitions are added and removed under one lock, so a
%removal never takes a row before the clause it owns is recorded:
'add-atom'(Space, Term, true) :- Term = [=,[FAtom|W],_], atom(FAtom), !,
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
                                            metta_on_function_changed(FAtom),
                                            maybe_print_compiled_clause("added function", Term, Clause).

%%A removal with an unknown function name must not erase program rows:
'remove-atom'(_, Term, _) :- Term = [=,[F|_],_], var(F), !, instantiation_error(F).

%%Remove a function atom. The rows it takes from this space decide the answer,
%%as for any atom, and a row takes a clause with it only if it was compiled:
%%(= $h 1) is data, and an imported copy in a second space has no clause.
'remove-atom'(Space, Term, Removed) :- Term = [=,[F|_],_], atom(F), !,
                                       with_mutex(petta_definitions, remove_function_atom(Space, Term, F, Removed)).

%Remove all same atoms, reporting whether there were any, as for a function atom:
'remove-atom'(Space, Term, Removed) :- remove_sexp(Space, Term, Removed).

remove_function_atom(Space, Term, F, Removed) :- Term = [Rel|Args], Row =.. [Space, Rel|Args],
                                                 findall(ClauseRef-Compiled, take_row(Row, ClauseRef, Compiled), Taken),
                                                 ( Taken == [] -> Removed = false
                                                 ; Removed = true,
                                                   findall(R, member(R-true, Taken), ClauseRefs),
                                                   ( ClauseRefs == [] -> true
                                                   ; maplist(erase_owned_clause, ClauseRefs),
                                                     metta_on_function_changed(F),
                                                     ( \+ ( current_predicate(F/A), functor(H2, F, A), clause(H2, _, _) )
                                                       -> retractall(fun(F)), metta_on_function_removed(F)
                                                       ; true ) ) ).

%Take a row that Row unifies with, and the clause it owns if it was compiled.
%Erasing the row is the claim: of several threads, one takes it.
take_row(Row, ClauseRef, Compiled) :- clause(Row, true, RowRef), erase(RowRef),
                                      ( retract(compiled_row(RowRef, ClauseRef)) -> Compiled = true
                                                                                 ; Compiled = false ).

%Erase the clause a removed row owned, and its record:
erase_owned_clause(ClauseRef) :- retractall(translated_from(ClauseRef, _)), erase(ClauseRef).

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
