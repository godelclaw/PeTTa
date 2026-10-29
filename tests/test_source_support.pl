:- ensure_loaded('../src/metta').
:- use_module(library(plunit)).
:- prolog_load_context(directory, D),
   directory_file_path(D, '../examples/imports/shared_support_single.metta', P),
   absolute_file_name(P, File), assertz(support_test_file(File)).

:- begin_tests(source_support).
test(concurrent_load_and_remove_preserve_remaining_imports) :-
    support_test_file(File),
    thread_create(support_churn(File, '&support-a'), A, []),
    thread_create(support_churn(File, '&support-b'), B, []),
    thread_join(A, SA), thread_join(B, SB),
    assertion(SA == true), assertion(SB == true),
    user:load_metta_file(File, _, '&support-last'),
    assertion(user:reduce([source_support_worker], 17)),
    user:'remove-atom'('&support-last', [=,[source_support_worker],17], true),
    assertion(\+ user:fun(source_support_worker)),
    assertion(\+ (user:source_row(_, R), \+ user:clause(_, true, R))),
    assertion(\+ (user:compiled_row(_, R), \+ user:clause(_, _, R))).

support_churn(File, Space) :-
    user:retractall(silent(_)), user:assertz(silent(true)),
    forall(between(1, 40, _),
           (user:load_metta_file(File, _, Space),
            user:reduce([source_support_worker], 17),
            user:'remove-atom'(Space, [=,[source_support_worker],17], true))).
:- end_tests(source_support).
