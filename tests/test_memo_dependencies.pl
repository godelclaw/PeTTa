:- begin_tests(memo_dependencies).
:- ensure_loaded('../src/metta.pl').
:- ensure_loaded('../lib/lib_memo.pl').

quiet_cache :- retractall(silent(_)), assertz(silent(true)), cache_clear.

:- dynamic notice/1.
:- multifile metta_on_function_changed/1.
metta_on_function_changed(md_notice) :- assertz(notice(first)).
metta_on_function_changed(md_notice) :- assertz(notice(second)).
metta_on_function_changed(md_fault) :- throw(error(resource_error(md_handler), test)).

test(notifications_reach_every_handler, [setup(retractall(notice(_)))]) :-
    notify_function_changed(md_notice),
    findall(N, notice(N), [first, second]).

test(notification_fault_is_not_absence,
     [throws(error(resource_error(md_handler), test))]) :-
    notify_function_changed(md_fault).

test(nonmemoized_chain_invalidates_parent_and_retains_unrelated_cache,
     [setup(quiet_cache)]) :-
    process_metta_string(
        "(= (md_child $x) (+ $x 1))\n\c
         (= (md_middle $x) (md_child $x))\n\c
         (= (md_parent $x) (md_middle $x))\n\c
         (= (md_unrelated $x) (+ $x 100))", _),
    enable_memoization(md_parent), enable_memoization(md_unrelated),
    once(eval([md_parent, 5], 6)),
    once(eval([md_unrelated, 5], 105)),
    once(metta_memo_entry(md_unrelated, 2, Gen, [5], Retained)),
    'add-atom'('&self', [=, [md_child, X], [+, X, 2]], true),
    findall(R, eval([md_parent, 5], R), [6, 7]),
    once(metta_memo_entry(md_unrelated, 2, Gen, [5], Retained)).

test(absent_head_is_observed_before_an_argument_defines_it,
     [setup(quiet_cache)]) :-
    process_metta_string(
        "(= (md_setter) (let $u (add-atom &self (= (md_late $x) (+ $x 10))) 5))\n\c
         (= (md_dynamic $f) ($f (md_setter)))", _),
    enable_memoization(md_dynamic),
    once(eval([md_dynamic, md_late], [md_late, 5])),
    % The first call captured absence. Its argument changed that observation,
    % so its data result must not be published as a reusable cache entry.
    \+ metta_memo_entry(md_dynamic, _, _, _, _),
    once(eval([md_dynamic, md_late], 15)).

test(named_owner_absence_and_definitions_do_not_alias,
     [setup(quiet_cache)]) :-
    A = '&md_left', B = '&md_right',
    'add-atom'(A, [=, [md_dispatch, F, X], [F, X]], true),
    'add-atom'(B, [=, [md_dispatch, F, X], [F, X]], true),
    space_pred(A, md_dispatch, PA), space_pred(B, md_dispatch, PB),
    enable_memoization(PA), enable_memoization(PB),
    once(eval([md_dispatch, md_target, 5], A, [md_target, 5])),
    once(eval([md_dispatch, md_target, 5], B, [md_target, 5])),
    once(metta_memo_entry(PB, 3, Gen, [md_target, 5], Retained)),
    'add-atom'(A, [=, [md_target, Y], [+, Y, 10]], true),
    once(eval([md_dispatch, md_target, 5], A, 15)),
    once(metta_memo_entry(PB, 3, Gen, [md_target, 5], Retained)),
    once(eval([md_dispatch, md_target, 5], B, [md_target, 5])).

test(cached_lambda_call_follows_its_callee,
     [setup(quiet_cache)]) :-
    process_metta_string(
        "(= (md_leaf $x) (+ $x 1))\n\c
         (= (md_apply $f $x) ($f $x))", _),
    once(eval(['|->', [X], [md_leaf, X]], Lambda)),
    enable_memoization(md_apply),
    once(eval([md_apply, Lambda, 5], 6)),
    'add-atom'('&self', [=, [md_leaf, Y], [+, Y, 2]], true),
    findall(R, eval([md_apply, Lambda, 5], R), [6, 7]).

:- end_tests(memo_dependencies).
