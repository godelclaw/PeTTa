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

test(clauseless_type_revision_invalidates_dynamic_and_reduce_callers,
     [setup(quiet_cache)]) :-
    process_metta_string(
        "(= (md_builtin_dynamic $f $x) ($f $x))\n\c
         (= (md_builtin_reduce $x) (reduce (id $x)))", _),
    enable_memoization(md_builtin_dynamic), enable_memoization(md_builtin_reduce),
    once(eval([md_builtin_dynamic, id, "hello"], "hello")),
    once(eval([md_builtin_reduce, "hello"], "hello")),
    Type = [':', id, ['->', 'Number', 'Number']],
    setup_call_cleanup('add-atom'('&self', Type, true),
        ( \+ eval([md_builtin_dynamic, id, "hello"], _),
          \+ eval([md_builtin_reduce, "hello"], _) ),
        'remove-atom'('&self', Type, true)).

test(argument_type_mutation_prevents_publication_of_the_old_observation,
     [setup(quiet_cache)]) :-
    process_metta_string(
        "(= (md_guard_setter) (let $u (add-atom &self (: id (-> Atom Atom))) 3))\n\c
         (= (md_guard_dynamic $f) ($f (md_guard_setter)))", _),
    enable_memoization(md_guard_dynamic),
    setup_call_cleanup(true,
        ( once(eval([md_guard_dynamic, id], 3)),
          \+ metta_memo_entry(md_guard_dynamic, _, _, _, _),
          once(eval([md_guard_dynamic, id], [md_guard_setter])) ),
        'remove-atom'('&self', [':', id, ['->', 'Atom', 'Atom']], true)).

test(named_clauseless_type_and_partial_shadow_revisions,
     [setup(quiet_cache)]) :-
    S = '&md_builtin_owner',
    'add-atom'(S, [=, [md_builtin_apply, F, X], [F, X]], true),
    space_pred(S, md_builtin_apply, Pred), enable_memoization(Pred),
    once(eval([md_builtin_apply, id, "hello"], S, "hello")),
    'add-atom'(S, [':', id, ['->', 'Number', 'Number']], true),
    \+ eval([md_builtin_apply, id, "hello"], S, _),
    once(eval([+, 2], S, Partial)),
    once(eval([md_builtin_apply, Partial, 10], S, 12)),
    'add-atom'(S, [=, [+, A, B], [*, A, B]], true),
    once(eval([md_builtin_apply, Partial, 10], S, 20)).

test(parallel_static_and_runtime_branches_retain_parent_dependencies,
     [setup(quiet_cache)]) :-
    process_metta_string(
        "(= (md_parallel_child $x) (+ $x 1))\n\c
         (= (md_parallel_static $x) (hyperpose ((md_parallel_child $x))))\n\c
         (= (md_parallel_runtime) (let $xs (quote ((md_parallel_child 5))) (hyperpose $xs)))", _),
    enable_memoization(md_parallel_static), enable_memoization(md_parallel_runtime),
    findall(R, eval([md_parallel_static, 5], R), [6]),
    findall(R, eval([md_parallel_runtime], R), [6]),
    'add-atom'('&self', [=, [md_parallel_child, X], [+, X, 10]], true),
    findall(R, eval([md_parallel_static, 5], R), Static), msort(Static, [6, 15]),
    findall(R, eval([md_parallel_runtime], R), Runtime), msort(Runtime, [6, 15]).

test(explicit_call_observes_its_callee, [setup(quiet_cache)]) :-
    process_metta_string(
        "(= (md_call_child $x) (+ $x 1))\n\c
         (= (md_call_parent $x) (call (md_call_child $x)))", _),
    enable_memoization(md_call_parent), once(eval([md_call_parent, 5], 6)),
    'add-atom'('&self', [=, [md_call_child, X], [+, X, 10]], true),
    findall(R, eval([md_call_parent, 5], R), [6, 15]).

test(prolog_registration_invalidates_an_observed_absence, [setup(quiet_cache)]) :-
    process_metta_string("(= (md_import_parent $f $x) ($f $x))", _),
    enable_memoization(md_import_parent),
    once(eval([md_import_parent, succ, 5], [succ, 5])),
    import_prolog_function(succ, true),
    once(eval([md_import_parent, succ, 5], 6)).

test(translator_rule_body_and_role_changes_invalidate_eval_cache,
     [setup(quiet_cache)]) :-
    process_metta_string(
        "(= (md_eval_rule $x) (quote (+ $x 1)))\n\c
         (= (md_rule_parent $e) (eval $e))", _),
    'add-translator-rule!'(md_eval_rule, true), enable_memoization(md_rule_parent),
    once(eval([md_rule_parent, [quote, [md_eval_rule, 5]]], 6)),
    'add-atom'('&self', [=, [md_eval_rule, X], [quote, [+, X, 100]]], true),
    findall(R, eval([md_rule_parent, [quote, [md_eval_rule, 5]]], R), [6, 105]),
    'remove-translator-rule!'(md_eval_rule, true),
    findall(R, eval([md_rule_parent, [quote, [md_eval_rule, 5]]], R),
            [[+, 5, 1], [+, 5, 100]]).

test(list_valued_head_observes_inner_absence, [setup(quiet_cache)]) :-
    process_metta_string("(= (md_data_parent $e) (eval $e))", _),
    enable_memoization(md_data_parent),
    Expression = [[quote, [md_data_late, 5]], 1],
    once(eval([md_data_parent, [quote, Expression]], [[md_data_late, 5], 1])),
    'add-atom'('&self', [=, [md_data_late, X], [+, X, 10]], true),
    once(eval([md_data_parent, [quote, Expression]], [15, 1])).

:- end_tests(memo_dependencies).
