:- multifile metta_memoized_dispatch_call/4.
:- multifile metta_on_function_changed/1.
:- multifile metta_on_function_removed/1.

metta_memoized_dispatch_call(_, _, _, _) :- fail.
metta_on_function_changed(_).
metta_on_function_removed(_).

% Run every registered hook clause once, even under with_mutex/2, without
% leaving choice points that duplicate a caller's answer:
notify_function_changed(F) :- forall(metta_on_function_changed(F), true).
notify_function_removed(F) :- forall(metta_on_function_removed(F), true).
