:- multifile metta_memoized_dispatch_call/4.
:- multifile metta_on_function_changed/1.
:- multifile metta_on_function_removed/1.
:- multifile metta_on_call/2.
:- multifile metta_worker_context/1.

metta_memoized_dispatch_call(_, _, _, _) :- fail.
metta_on_function_changed(_).
metta_on_function_removed(_).
metta_on_call(_, _) :- fail.
metta_worker_context(_) :- fail.

notify_function_changed(Fun) :- forall(metta_on_function_changed(Fun), true).
notify_function_removed(Fun) :- forall(metta_on_function_removed(Fun), true).
observe_function_call(Fun, Arity) :- forall(metta_on_call(Fun, Arity), true).

:- meta_predicate parallel_answers(0, 0).
:- meta_predicate with_worker_context(+, 0).
parallel_answers(Generator, Goal) :-
    findall(Wrapper, metta_worker_context(Wrapper), Context),
    concurrent_and(Generator, with_worker_context(Context, Goal)).
with_worker_context([], Goal) :- call(Goal).
with_worker_context([Wrapper|Rest], Goal) :-
    call(Wrapper, with_worker_context(Rest, Goal)).
