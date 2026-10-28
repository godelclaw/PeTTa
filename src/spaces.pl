:- dynamic space_primitive/2.
:- dynamic created_space/1.

% A new empty space is a fresh first-class name, including before any row is
% added. Never select an existing predicate or a previously returned space.
'new-space'(Space) :- with_mutex(metta_space_creation, fresh_space_name(Fresh)),
                      Space = Fresh.

fresh_space_name(Space) :- gensym('&space_', Candidate),
    ( (current_predicate(Candidate/_) ; created_space(Candidate) ; space_primitive(Candidate, _))
      -> fresh_space_name(Space)
       ; assertz(created_space(Candidate)), Space = Candidate ).

%Nonempty expressions keep their indexed rows; other atoms are stored separately.
%An unbound atom still raises an instantiation error:
add_sexp(Space, Atom) :- ( var(Atom) -> instantiation_error(Atom)
                        ; Atom = [Rel|Args] -> Term =.. [Space, Rel | Args], assertz(Term)
                        ; must_be(atom, Space), assertz(space_primitive(Space, Atom)) ).

%Same but for removal:
remove_sexp(Space, Atom) :- ( var(Atom) -> instantiation_error(Atom)
                           ; Atom = [Rel|Args] -> Term =.. [Space, Rel | Args], retractall(Term)
                           ; must_be(atom, Space), retractall(space_primitive(Space, Atom)) ).

%Arrow declarations alter the code emitted for a named space's stored functions
%(&self's are revised by revise_arrow_declarations/2 below).
'add-atom'(Space, Term, true) :- atom(Space), Space \== '&self',
                                 function_type_annotation_term(Term, F, _), !,
                                 revise_function_type(Space, F, add_sexp(Space, Term)).

%Add a function atom to its owner's compiled program:
'add-atom'(Space, Term, true) :- Term = [=,[FAtom|_],_], atom(Space), atom(FAtom), !,
                                 install_function_definition(Space, Term, Ref),
                                 ( silent(true) -> true
                                 ; clause(Head, Body, Ref),
                                   maybe_print_compiled_clause("added function", Term, (Head :- Body)) ).

%Add an arrow declaration, which changes how calls to its function are translated:
'add-atom'(Space, Term, true) :- is_arrow_declaration(Space, Term, Fun), !,
                                 revise_arrow_declarations([Fun], add_sexp(Space, Term)).

%Add an atom to the space:
'add-atom'(Space, Term, true) :- add_sexp(Space, Term).

%%A removal with an unknown function name must not erase program rows:
'remove-atom'(_, Term, _) :- Term = [=,[F|_],_], var(F), !, instantiation_error(F).
'remove-atom'(Space, Term, true) :- atom(Space), Space \== '&self',
                                    nonvar(Term), Term = [Colon, Function, _],
                                    (Colon == ':' ; var(Colon), atom(Function)), !,
                                    findall(F,
                                      ( copy_term(Term, [':', F, Type]),
                                        match(Space, [':', F, Type], Type, Type),
                                        function_type_annotation_term([':', F, Type], F, _) ),
                                      Funs0),
                                    sort(Funs0, Funs),
                                    revise_function_types(Space, Funs, remove_sexp(Space, Term)).

%%Remove a function atom:
'remove-atom'(Space, Term, Removed) :- Term = [=,[F|Args],Body],
                                       atom(Space), atom(F), !,
                                       revise_function_definition(Space, F,
                                       (remove_sexp(Space, Term),
                                       space_pred(Space, F, Pred),
                                       ( retract(function_metadata(Pred, fun_meta(Args, Body))) -> true ; true ),
                                       uninstall_function_clauses(Space, Term, Refs),
                                       notify_function_changed(Pred),
                                       (current_predicate(invalidate_specializations/1) -> invalidate_specializations(Pred) ; true),
                                       ( \+ ( current_predicate(Pred/A), functor(H2, Pred, A), clause(H2, _, _) )
                                         -> retractall(fun(Pred)),
                                            retractall(space_fun(Space, F, Pred)),
                                            notify_function_removed(Pred)
                                         ; true ),
                                       ( Refs = [] -> Removed = false ; Removed = true ))).

%Remove the type atoms matching a pattern, which may be arrow declarations of several functions:
'remove-atom'(Space, Term, true) :- Space == '&self', nonvar(Term), Term = [Colon, Function, _],
                                    (Colon == ':' ; var(Colon), atom(Function)), !,
                                    findall(Fun, ( copy_term(Term, [_, Fun, TypeChain]),
                                                   catch('&self'(:, Fun, TypeChain), _, fail),
                                                   is_arrow_declaration(Space, [':', Fun, TypeChain], Fun) ), Funs0),
                                    sort(Funs0, Funs),
                                    ( Funs == [] -> remove_sexp(Space, Term)
                                                  ; revise_arrow_declarations(Funs, remove_sexp(Space, Term)) ).

%Remove all same atoms:
'remove-atom'(Space, Term, true) :- remove_sexp(Space, Term).

% A space is a predicate per row arity, created by the first add-atom. Reading
% a space before it is written calls an undefined predicate, and every such
% call would search the autoloader before failing. The first call declares the
% space's predicate dynamic instead, so later reads are plain calls on an empty
% predicate; reads of existing spaces pay nothing extra.
space_call(Term) :- catch(Term, E, space_missing(E, Term)).

space_missing(error(existence_error(procedure, Missing), _), Term) :-
    strip_module(Term, Module, Plain), functor(Plain, Space, Arity),
    ( Missing == Space/Arity ; Missing == Module:Space/Arity ),
    \+ current_predicate(Module:Space/Arity), !,
    dynamic(Module:Space/Arity),
    fail.
space_missing(Error, _) :- throw(Error).
%Recognize (: Fun (-> ...)) in the space whose declarations the translator reads:
is_arrow_declaration(Space, Term, Fun) :- Space == '&self',
                                          nonvar(Term), Term = [Colon, Fun, TypeChain], Colon == ':',
                                          atom(Fun),
                                          nonvar(TypeChain), TypeChain = [Arrow|_], Arrow == '->'.

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
