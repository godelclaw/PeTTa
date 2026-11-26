:- ensure_loaded('../src/metta').
:- use_module(library(plunit)).
:- use_module(library(aggregate)).

%A conjunctive match reads each pattern when it is reached: a lookup that is
%already running keeps the rows it started with, and a later one sees the space
%as it is then.

:- begin_tests(conjunctive_match).

space(S, Atoms) :- user:'new-space'(S), forall(member(A, Atoms), user:'add-atom'(S, A, _)).

test(a_later_lookup_sees_an_added_atom, Answers == [[a,b,c], [b,c,d]]) :-
    space(S, [[e,a,b], [e,b,c]]),
    findall([X,Y,Z], ( user:match(S, [',', [e,X,Y], [e,Y,Z]], [X,Y,Z], _),
                       user:'add-atom'(S, [e,c,d], _) ), Answers).

test(a_later_lookup_misses_a_removed_atom, Answers == [[a,b,c]]) :-
    space(S, [[e,a,b], [e,b,c], [e,c,d]]),
    findall([X,Y,Z], ( user:match(S, [',', [e,X,Y], [e,Y,Z]], [X,Y,Z], _),
                       ignore(user:'remove-atom'(S, [e,c,d], _)) ), Answers).

test(a_running_lookup_keeps_its_rows, Answers == [[a,b], [a,c]]) :-
    space(S, [[p,a], [p,b], [q,b], [q,c]]),
    findall([X,Y], ( user:match(S, [',', [p,X], [q,Y]], [X,Y], _),
                     forall(member(T, [b,c]), ignore(user:'remove-atom'(S, [q,T], _))) ), Answers).

%Rows of one arity: the unbound pattern is one running lookup.
test(unbound_pattern_keeps_its_rows, N == 2) :-
    space(S, [[e,a,b], [f,c,d]]),
    aggregate_all(count, ( user:match(S, [',', [e,a,_], V], V, _),
                           user:'add-atom'(S, [g,n,m], _) ), N).

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
