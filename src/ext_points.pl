:- multifile metta_memoized_dispatch_call/4.
:- multifile metta_on_function_changed/1.
:- multifile metta_on_function_removed/1.
:- multifile metta_on_call/2.

metta_memoized_dispatch_call(_, _, _, _) :- fail.
metta_on_function_changed(_).
metta_on_function_removed(_).
metta_on_call(_, _) :- fail.

notify_function_changed(Fun) :- forall(metta_on_function_changed(Fun), true).
notify_function_removed(Fun) :- forall(metta_on_function_removed(Fun), true).
observe_function_call(Fun, Arity) :- forall(metta_on_call(Fun, Arity), true).
