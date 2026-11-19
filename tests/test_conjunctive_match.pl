:- ensure_loaded('../src/metta').
:- use_module(library(plunit)).
:- use_module(library(aggregate)).

%A conjunctive match reads all its patterns in the state of the space at
%the call.

:- begin_tests(conjunctive_match).

space(S, Atoms) :- user:'new-space'(S), forall(member(A, Atoms), user:'add-atom'(S, A, _)).

test(added_atom_not_seen, Answers == [[a,b,c]]) :-
    space(S, [[e,a,b], [e,b,c]]),
    findall([X,Y,Z], ( user:match(S, [',', [e,X,Y], [e,Y,Z]], [X,Y,Z], _),
                       user:'add-atom'(S, [e,c,d], _) ), Answers).

test(removed_atom_still_seen, Answers == [[a,b,c], [b,c,d]]) :-
    space(S, [[e,a,b], [e,b,c], [e,c,d]]),
    findall([X,Y,Z], ( user:match(S, [',', [e,X,Y], [e,Y,Z]], [X,Y,Z], _),
                       ignore(user:'remove-atom'(S, [e,c,d], _)) ), Answers).

test(all_atoms_of_a_relation_removed, Answers == [[a,b], [a,c], [b,b], [b,c]]) :-
    space(S, [[p,a], [p,b], [q,b], [q,c]]),
    findall([X,Y], ( user:match(S, [',', [p,X], [q,Y]], [X,Y], _),
                     forall(member(T, [b,c]), ignore(user:'remove-atom'(S, [q,T], _))) ), Answers).

test(unbound_pattern, N == 2) :-
    space(S, [[e,a,b], [f,c]]),
    aggregate_all(count, ( user:match(S, [',', [e,a,_], V], V, _),
                           user:'add-atom'(S, [g,new], _) ), N).

test(same_answers_without_writes, Answers == Nested) :-
    space(S, [[e,a,b], [e,b,c], [e,b,d], [e,c,a], [e,d,b]]),
    findall(X-Z, user:match(S, [',', [e,X,Y], [e,Y,Z]], X-Z, _), Answers),
    findall(X-Z, ( user:match(S, [e,X,Y], x, _), user:match(S, [e,Y,Z], x, _) ), Nested).

test(first_answer_is_lazy, true(R \== inference_limit_exceeded)) :-
    space(S, []),
    forall(between(1, 2000, I), ( user:'add-atom'(S, [l,I], _), user:'add-atom'(S, [r,I], _) )),
    call_with_inference_limit(once(user:match(S, [',', [l,_], [r,_]], x, _)), 100000, R).

test(exception_in_answer, Rows == [[a]]) :-
    space(S, [[p,a], [p,b], [q,x]]),
    catch(( user:match(S, [',', [p,_], [q,_]], x, _), throw(stop) ), stop, true),
    findall([X], user:match(S, [',', [p,X], [q,x]], x, _), [First|_]),
    Rows = [First].

:- end_tests(conjunctive_match).
