:- ensure_loaded('../src/metta').
:- use_module(library(plunit)).
:- use_module(library(prolog_wrap)).

:- begin_tests(loader_display).

test(concurrent_removal_does_not_break_non_silent_loading) :-
    thread_self(Loader), message_queue_create(Q),
    nb_setval('$test_loader_display_pause', false),
    thread_create((thread_get_message(Q, remove, [timeout(5)]),
                   user:'remove-atom'('&self', [=,[loader_display_probe,1],2], true),
                   thread_send_message(Q, removed)), Worker, []),
    setup_call_cleanup(
        wrap_predicate(user:metta_on_function_changed(F), loader_display_test, Wrapped,
            ((thread_self(Current), Current == Loader, F == loader_display_probe,
              nb_current('$test_loader_display_pause', false))
             -> nb_setval('$test_loader_display_pause', true),
                thread_send_message(Q, remove),
                thread_get_message(Q, removed, [timeout(5)]), call(Wrapped)
             ; call(Wrapped))),
        with_output_to(string(Output),
                  (user:retractall(silent(_)), user:assertz(silent(false)),
                   user:process_metta_string("(= (loader_display_probe 1) 2)", _))),
        (unwrap_predicate(user:metta_on_function_changed(_), loader_display_test),
         thread_join(Worker, WorkerStatus), message_queue_destroy(Q),
         nb_delete('$test_loader_display_pause'))),
    assertion(WorkerStatus == true),
    assertion(sub_string(Output, _, _, _, "loader_display_probe(1, 2)")),
    assertion(\+ user:clause('&self'(=,[loader_display_probe,1],2), true)).

:- end_tests(loader_display).
