:- ensure_loaded('../src/metta').
:- set_prolog_flag(optimise_debug,false).
:- use_module(library(plunit)).
:- set_test_options([load(always)]).

runtime_host_hold(X,X).
runtime_host_echo(X,X).
runtime_local_used(Used) :- statistics(localused,Used).
runtime_wrap_once(X,_) :- user:ri_wrap(X,[_]).
runtime_stack_delta(F,Extra,N,Delta) :-
    append([N|Extra],[AtBase],Args),Goal=..[F|Args],statistics(localused,Before),
    once(user:call(Goal)),Delta is AtBase-Before.
runtime_input_barrier(Events,Release) :-
    thread_send_message(Events,entered),
    (thread_get_message(Release,resume,[timeout(5)])->true;throw(runtime_barrier_timeout)).

:- begin_tests(runtime_types).
program(Source,Results) :- user:process_metta_string(Source,Results).

test(a_failed_first_typing_transaction_can_export_state_constraints) :-
    program("!(collapse (transaction (let $_ (add-atom &self (: rt_escaped (-> Number Number))) (let $_ (add-atom &self (= (rt_escaped $x) $x)) (let $x (eval (rt_escaped $y)) (let $_ (change-state! rt_escape_cell $x) (empty))))))) !(collapse (let $x (get-state rt_escape_cell) (let $x \"bad\" 7)))",R),
    assertion(R == [[],[]]).
test(callee_checks_direct_and_indirect) :-
    program("(: rt_id (-> Number Number)) (= (rt_id $x) $x) !(collapse (rt_id \"bad\")) !(collapse (let $f rt_id ($f \"bad\")))", R),
    assertion(R == [[],[]]).
test(indirect_atom_arguments_are_held) :-
    program("(: rt_hold (-> Atom Atom)) (= (rt_hold $x) $x) !(rt_hold (/ 1 0)) !(let $f rt_hold ($f (/ 1 0)))", R),
    assertion(R == [[/,1,0],[/,1,0]]).
test(open_inputs_remain_constrained) :-
    program("(: rt_open (-> Number Number)) (= (rt_open $x) $x) !(collapse (let $y (rt_open $x) (let $x \"bad\" $y)))", R),
    assertion(R == [[]]).
test(whole_overload_waits_for_binding) :-
    program("(: rt_over (-> Number Number)) (: rt_over (-> String String)) (= (rt_over $x) $x) !(collapse (let $y (rt_over $x) (let $x \"ok\" $y)))", R),
    assertion(R == [["ok"]]).
test(shared_parameters_reject_mixed_values) :-
    program("(: rt_same (-> $a $a Number)) (= (rt_same $x $y) 1) !(collapse (rt_same 2 \"bad\"))",R),
    assertion(R == [[]]).
test(shared_open_parameters_reject_later_mismatch) :-
    program("(: rt_joint (-> $a $a Number)) (= (rt_joint $x $y) 1) !(collapse (let $_ (rt_joint $x \"ok\") (let $x 2 7)))",R),
    assertion(R == [[]]).
test(result_can_select_another_symbolic_instance) :-
    program("(: rt_Nil (List $a)) (: rt_Cons (-> $a (List $a) (List $a))) (: rt_poly (-> $a $a)) (= (rt_poly $x) (rt_Cons \"ok\" rt_Nil)) !(rt_poly rt_Nil)",R),
    assertion(R == [[rt_Cons,"ok",rt_Nil]]).
test(hidden_constraints_are_not_answer_values) :-
    program("(: rt_hidden (-> Number Number)) (= (rt_hidden $x) 7) !(collapse (rt_hidden $x))",R),
    assertion(R == [[7]]).
test(findall_copies_visible_constraints) :-
    program("(: rt_copy (-> Number Number)) (= (rt_copy $x) $x) !(collapse (let ($y) (collapse (rt_copy $x)) (let $y \"bad\" 7)))",R),
    assertion(R == [[]]).
test(late_declaration_refreshes_existing_function) :-
    program("(= (rt_late $x) $x) (= (rt_late_caller $x) (rt_late $x)) (: rt_late (-> Number Number)) !(collapse (rt_late_caller \"bad\"))",R),
    assertion(R == [[]]).
test(removing_a_declaration_restores_plain_equations) :-
    program("(: rt_remove (-> Number Number)) (= (rt_remove $x) $x) !(remove-atom &self (: rt_remove (-> Number Number))) !(rt_remove \"ok\")",R),
    assertion(R == [true,"ok"]).
test(output_membership_is_live) :-
    program("(: rt_live (-> Number rt_Type)) (= (rt_live $x) (let $_ (add-atom &self (: rt_new rt_Type)) rt_new)) !(rt_live 1)",R),
    assertion(R == [rt_new]).
test(input_evidence_survives_a_body_edit) :-
    program("(: rt_old rt_Old) (: rt_edit (-> $a $a)) (= (rt_edit $x) (let $_ (remove-atom &self (: rt_old rt_Old)) rt_other)) (: rt_other rt_Old) !(rt_edit rt_old)",R),
    assertion(R == [rt_other]).
test(known_bad_constructor_head_fails_before_open_tail) :-
    program("(: rt_Z rt_Nat) (: rt_S (-> rt_Nat rt_Nat)) (: rt_nat (-> rt_Nat Number)) (= (rt_nat $x) 1) !(collapse (rt_nat (rt_S \"bad\")))",R),
    assertion(R == [[]]).
test(variable_mode_observed_before_head_matching) :-
    program("(: rt_variable (-> Variable Number)) (= (rt_variable 2) 7) !(rt_variable $x) !(collapse (rt_variable 2))",R),
    assertion(R == [7,[]]).
test(metatype_modes_observe_the_value_shape) :-
    program("(: rt_expr (-> Expression Number)) (= (rt_expr $a) 1)
      (: rt_sym (-> Symbol Number)) (= (rt_sym $a) 1)
      (: rt_gr (-> Grounded Number)) (= (rt_gr $a) 1)
      (: rt_mkexpr (-> Number Expression)) (= (rt_mkexpr $n) (a $n))
      (: rt_mksym (-> Number Symbol)) (= (rt_mksym $n) (a $n))
      !(collapse (rt_expr (a b))) !(collapse (rt_expr foo))
      !(collapse (rt_sym foo)) !(collapse (rt_sym (a b)))
      !(collapse (rt_gr 3)) !(collapse (rt_gr foo))
      !(collapse (rt_mkexpr 1)) !(collapse (rt_mksym 1))",R),
    assertion(R == [[1],[],[1],[],[1],[],[[a,1]],[]]).
test(repeated_nominal_pattern) :-
    program("(: (rt_Pair $x $x) rt_Same) (: rt_pair_check (-> rt_Same Number)) (= (rt_pair_check $x) 7) !(rt_pair_check (rt_Pair 1 1)) !(collapse (rt_pair_check (rt_Pair 1 2)))",R),
    assertion(R == [7,[]]).
test(body_fault_is_not_suppressed_by_result_check) :-
    program("(: rt_fault (-> Number Number)) (= (rt_fault $x) (bad (/ 1 0))) !(catch (rt_fault 1))",R),
    assertion(R = [['Error',evaluation_error(zero_divisor),_]]).
test(real_equation_multiplicity_is_retained) :-
    program("(: rt_multi (-> Number Number)) (: rt_multi (-> Number Number)) (= (rt_multi $x) 1) (= (rt_multi $x) 2) !(collapse (rt_multi 0))",R),
    assertion(R == [[1,2]]).
test(checkfree_functions_have_no_runtime_wrapper) :-
    program("(: rt_free (-> Atom %Undefined%)) (= (rt_free $x) $x)",_),
    assertion(\+ user:type_wrapper(rt_free,_,_)).
test(mode_edits_refresh_existing_indirect_callers) :-
    program("(= (rt_mode_id $x) $x) (= (rt_mode_call $f) ($f (/ 1 0))) (: rt_mode_id (-> Atom Atom)) !(rt_mode_call rt_mode_id)",R),
    assertion(R == [[/,1,0]]).

test(open_primitive_accepts_a_later_number) :-
    program("(: rt_accept (-> Number Number)) (= (rt_accept $x) $x) !(collapse (let $y (rt_accept $x) (let $x 42 $y)))",R),
    assertion(R == [[42]]).
test(first_declaration_can_arrive_inside_collection) :-
    program("(= (rt_first $x) $x) !(collapse (let $_ (add-atom &self (: rt_first (-> Number Number))) (let $y (rt_first $x) (let $x 42 $y))))",R),
    assertion(R == [[42]]).
test(primitive_declarations_on_native_calls_are_enforced) :-
    program("(: + (-> Number Number Number)) !(collapse (+ \"bad\" 1)) !(collapse (let $f + ($f \"bad\" 1)))",R),
    assertion(R == [[],[]]),
    program("!(remove-atom &self (: + (-> Number Number Number)))",_).
test(copied_state_keeps_native_constraints) :-
    program("(: rt_state (-> Number Number)) (= (rt_state $x) $x) !(let $x (rt_state $y) (change-state! rt_cell $x)) !(collapse (let $x (get-state rt_cell) (let $x \"bad\" 7)))",R),
    assertion(R == [true,[]]).
test(space_assertions_create_fresh_untyped_variables) :-
    program("(: rt_stored (-> Number Number)) (= (rt_stored $x) $x) !(let $x (rt_stored $y) (add-atom &rt_space (row $x))) !(collapse (match &rt_space (row $x) (let $x \"bad\" 7)))",R),
    assertion(R == [true,[7]]).
test(memo_hits_check_current_membership) :-
    program("!(import! &self (library lib_memo)) (: rt_memo_value rt_Member) (: rt_memo (-> rt_Member Number)) (= (rt_memo $x) 7) !(memoize rt_memo) !(rt_memo rt_memo_value) !(remove-atom &self (: rt_memo_value rt_Member)) !(collapse (rt_memo rt_memo_value))",R),
    assertion(R == [true,true,7,true,[]]).

test(partial_applications_hold_the_supplied_raw_argument) :-
    program("(: rt_partial (-> Atom Number Atom)) (= (rt_partial $raw $x) $raw) !((rt_partial (/ 1 0)) 2)",R),
    assertion(R == [[/,1,0]]).
test(partial_application_checks_the_remaining_argument_positions) :-
    program("(: ri_mixed_partial (-> Number String Number)) (= (ri_mixed_partial $x $y) $x) !((ri_mixed_partial 1) \"ok\") !(collapse ((ri_mixed_partial 1) 2)) !(collapse ((ri_mixed_partial \"bad\") \"ok\")) !(let $f (ri_mixed_partial 1) ($f \"ok\"))",R),
    assertion(R == [1,[],[],1]).

test(identity_does_not_reuse_a_changed_membership) :-
    program("(: rt_same_atom rt_A) (: rt_mutate (-> $a $a)) (= (rt_mutate $x) (let $_ (remove-atom &self (: rt_same_atom rt_A)) (let $_ (add-atom &self (: rt_same_atom rt_B)) $x))) !(collapse (rt_mutate rt_same_atom))",R),
    assertion(R == [[]]).
test(binding_records_evidence_before_a_later_edit) :-
    program("(: rt_bound_atom rt_C) (: rt_bound_other rt_C) (: rt_bind_edit (-> $a $a)) (= (rt_bind_edit $x) (let $x rt_bound_atom (let $_ (remove-atom &self (: rt_bound_atom rt_C)) rt_bound_other))) !(rt_bind_edit $x)",R),
    assertion(R == [rt_bound_other]).
test(shared_mismatch_precedes_a_later_body_fault) :-
    program("(: rt_fail_early (-> $a $a Number)) (= (rt_fail_early $x $y) (let $x 2 (let $y \"bad\" (/ 1 0)))) !(collapse (rt_fail_early $x $y))",R),
    assertion(R == [[]]).
test(open_constructor_head_is_a_constraint) :-
    program("(: rt_Zero rt_Nat2) (: rt_Succ (-> rt_Nat2 rt_Nat2)) (: rt_unknown_head (-> rt_Nat2 Number)) (= (rt_unknown_head $x) 7)",_),
    user:rt_unknown_head([H,rt_Zero],7),
    assertion(\+ (H=wrong)),H=rt_Succ.
test(open_constructor_arguments_preserve_shape_and_field_types) :-
    program("(: rt_Z3 rt_Nat3) (: rt_S3 (-> rt_Nat3 rt_Nat3)) (: rt_unknown_args (-> rt_Nat3 Number)) (= (rt_unknown_args $x) 7)",_),
    user:rt_unknown_args([rt_S3|Args],7),
    assertion(\+ (Args=["bad"])),Args=[rt_Z3].
test(indirect_quote_is_held_even_without_argument_goals) :-
    program("(: rt_quote_hold (-> Atom Atom)) (= (rt_quote_hold $x) $x) !(let $f rt_quote_hold ($f (quote (+ 1 2))))",R),
    assertion(R == [[quote,[+,1,2]]]).
test(runtime_function_addition_activates_raw_indirect_plans) :-
    program("(: rt_added_hold (-> Atom Atom)) (= (rt_dynamic_call $f) ($f (/ 1 0))) !(add-atom &self (= (rt_added_hold $x) $x)) !(rt_dynamic_call rt_added_hold)",R),
    assertion(R == [true,[/,1,0]]).
test(compiled_nominal_membership_is_live) :-
    program("(: rt_allowed rt_Set) (: rt_set_id (-> rt_Set rt_Set)) (= (rt_set_id $x) $x) !(rt_set_id rt_allowed) !(remove-atom &self (: rt_allowed rt_Set)) !(collapse (rt_set_id rt_allowed)) !(add-atom &self (: rt_next rt_Set)) !(rt_set_id rt_next)",R),
    assertion(R == [rt_allowed,true,[],true,rt_next]).
test(compiled_constructor_can_become_a_function_and_return_to_data) :-
    program("(: rt_Z4 rt_Nat4) (: rt_C4 (-> rt_Nat4 rt_Nat4)) (: rt_n4 (-> rt_Nat4 Number)) (= (rt_n4 $x) 1) !(rt_n4 (rt_C4 rt_Z4)) !(add-atom &self (= (rt_C4 $x) \"bad\")) !(collapse (rt_n4 (quote (rt_C4 rt_Z4)))) !(remove-atom &self (= (rt_C4 $x) \"bad\")) !(rt_n4 (rt_C4 rt_Z4))",R),
    assertion(R == [1,true,[],true,1]).
test(declaration_updates_roll_back_with_the_transaction) :-
    program("(= (rt_tx $x) $x) !(collapse (transaction (let $_ (add-atom &self (: rt_tx (-> Number Number))) (empty)))) !(rt_tx \"ok\")",R),
    assertion(R == [[],"ok"]),assertion(\+user:type_declaration(rt_tx,_)).
test(space_enumeration_keeps_native_assertion_behavior) :-
    program("(: rt_row (-> Number Number)) (= (rt_row $x) $x) !(let $x (rt_row $y) (add-atom &rt_rows (row $x))) !(collapse (let (row $x) (get-atoms &rt_rows) (let $x \"bad\" 1)))",R),
    assertion(R == [true,[1]]).
test(a_polymorphic_identity_leaves_no_watcher) :-
    program("(: rt_poly_id (-> $a $a)) (= (rt_poly_id $x) $x)",_),
    user:rt_poly_id(X,Y),assertion(X==Y),assertion(\+ attvar(X)).
% A slot whose only requirement is that its value has some type checks nothing.
test(unshared_and_wildcard_slots_check_nothing) :-
    program("(: rt_unshared (-> $a Number Number)) (= (rt_unshared $x $n) $n)
      (: rt_wild (-> _ Number Number)) (= (rt_wild $x $n) $n)",_),
    user:rt_unshared(X,1,R1),assertion(R1==1),assertion(\+ attvar(X)),
    user:rt_wild(Y,1,R2),assertion(R2==1),assertion(\+ attvar(Y)),
    Cyclic=f(Cyclic),user:rt_unshared(Cyclic,2,R3),assertion(R3==2),
    assertion(\+ user:rt_unshared(_,"bad",_)),assertion(\+ user:rt_wild(_,"bad",_)).
test(duplicate_signatures_do_not_repeat_effects) :-
    program("(: rt_effect (-> Number Number)) (: rt_effect (-> $a Number)) (= (rt_effect $x) (let $n (get-state rt_effects) (let $_ (change-state! rt_effects (+ $n 1)) 7))) !(change-state! rt_effects 0) !(rt_effect 1) !(get-state rt_effects)",R),
    assertion(R == [true,7,1]).

test(copy_term_preserves_shared_polymorphic_constraints) :-
    program("(: rt_copy_group (-> $a $a $a)) (= (rt_copy_group $x $y) $x)",_),
    user:rt_copy_group(X,"ok",X),copy_term(X,C),
    assertion(var(X)),assertion(\+(C=2)),C="later",assertion(var(X)),X="ok".
test(variable_aliasing_merges_obligation_cells) :-
    program("(: rt_alias (-> $a $a Number)) (= (rt_alias $x $y) 7)",_),
    user:rt_alias(X,Y,7),X=Y,X=42.
test(explicit_residual_goal_copy_replays_the_same_constraint) :-
    user:rt_copy_group(X,"ok",X),copy_term(X,C,Goals),
    maplist(call,Goals),assertion(\+(C=2)),C="ok".
test(nonprimitive_constructor_cannot_supply_a_numeric_type_parameter) :-
    program("(: rt_anyctor (-> $a)) (: rt_kind (-> $a $a Number)) (= (rt_kind $x $y) 7) !(collapse (rt_kind (rt_anyctor) 2))",R),
    assertion(R == [[]]).

test(importing_an_annotated_native_function_updates_indirect_modes) :-
    program("(: runtime_host_hold (-> Atom Atom)) (= (rt_import_call $f) ($f (/ 1 0))) !(import_prolog_function runtime_host_hold) !(rt_import_call runtime_host_hold)",R),
    assertion(R == [true,[/,1,0]]).
test(already_entered_native_caller_uses_the_new_contract) :-
    program("!(import_prolog_function runtime_host_echo) (: runtime_host_echo (-> Number Number)) (= (rt_live_native $x) (let $_ (remove-atom &self (: runtime_host_echo (-> Number Number))) (runtime_host_echo $x))) !(rt_live_native \"ok\")",R),
    assertion(R == [true,"ok"]).
test(already_entered_memo_caller_uses_the_new_contract) :-
    program("!(import! &self (library lib_memo)) (: rt_live_memo (-> Number Number)) (= (rt_live_memo $x) $x) !(memoize rt_live_memo) (= (rt_live_memo_caller $x) (let $_ (remove-atom &self (: rt_live_memo (-> Number Number))) (rt_live_memo $x))) !(rt_live_memo_caller \"ok\")",R),
    assertion(R == [true,true,"ok"]).
test(an_entered_call_retains_its_own_signature) :-
    program("(: rt_self_edit (-> Number Number)) (= (rt_self_edit $x) (let $_ (remove-atom &self (: rt_self_edit (-> Number Number))) \"bad\")) !(collapse (rt_self_edit 1)) !(rt_self_edit 1)",R),
    assertion(R == [[],"bad"]).
test(freshly_asserted_rows_can_be_removed) :-
    program("(: rt_store_remove (-> Number Number)) (= (rt_store_remove $x) $x) !(let $x (rt_store_remove $y) (add-atom &rt_remove_space (row $x))) !(remove-atom &rt_remove_space (row $x)) !(collapse (get-atoms &rt_remove_space))",R),
    assertion(R == [true,true,[]]).
test(explicit_residuals_survive_a_second_native_copy) :-
    user:rt_copy_group(X,"ok",X),copy_term(X,C,Goals),maplist(call,Goals),copy_term(C,D),
    assertion(\+(D=2)),D="ok".

test(constructor_fields_are_value_types_not_call_modes) :-
    program("(: rt_quoted_atom Atom) (: rt_BoxAtom (-> Atom rt_AtomBox)) (: rt_box_atom (-> rt_AtomBox Number)) (= (rt_box_atom $x) 7) !(rt_box_atom (rt_BoxAtom rt_quoted_atom)) !(collapse (rt_box_atom (rt_BoxAtom 2)))",R),
    assertion(R == [7,[]]).
test(a_type_parameter_cannot_gain_argument_holding_power) :-
    program("(: rt_label_atom Atom) (: rt_mode_poly (-> $a $a)) (= (rt_mode_poly $x) 2) !(collapse (rt_mode_poly rt_label_atom))",R),
    assertion(R == [[]]).

test(preexisting_output_constraints_precede_a_field_fault) :-
    program("(: rt_output_num (-> Number Number)) (= (rt_output_num $x) $x) (: rt_bad_fields (-> Number %Undefined%)) (= (rt_bad_fields $x) (rt_Data (/ 1 0)))",_),
    user:rt_output_num(X,Out),assertion(X==Out),
    assertion(\+user:rt_bad_fields(1,Out)).
test(state_preserves_a_shared_polymorphic_constraint) :-
    user:rt_copy_group(X,"ok",X),user:'change-state!'(rt_poly_state,X,true),
    user:'get-state'(rt_poly_state,C),assertion(\+(C=2)),C="ok".
test(thread_messages_preserve_shared_constraints) :-
    user:rt_copy_group(X,"ok",X),
    setup_call_cleanup(message_queue_create(Q),
      (thread_send_message(Q,value(X)),thread_get_message(Q,value(C)),assertion(\+(C=2)),C="ok"),
      message_queue_destroy(Q)).
test(space_assertion_does_not_change_the_original_variable_constraint) :-
    user:rt_copy_group(X,"ok",X),user:'add-atom'('&rt_opaque',opaque(X),true),
    once(user:'get-atoms'('&rt_opaque',opaque(C))),assertion(\+(X=2)),C=2,
    user:'remove-atom'('&rt_opaque',opaque(_),true).

test(held_partial_arguments_remain_valid_function_values) :-
    program("(: rt_capture (-> Atom Number Number)) (= (rt_capture $raw $x) $x) (: rt_apply_one (-> (-> Number Number) Number Number)) (= (rt_apply_one $f $x) ($f $x)) !(rt_apply_one (rt_capture (/ 1 0)) 7)",R),
    assertion(R == [7]).

test(opaque_nominal_patterns_watch_their_open_fields) :-
    user:'add-atom'('&self',[:,opaque(4),rt_OpaqueFour],true),
    program("(: rt_opaque_four (-> rt_OpaqueFour Number)) (= (rt_opaque_four $x) 7)",_),
    user:rt_opaque_four(opaque(X),7),assertion(\+(X=5)),X=4.

test(private_wildcard_cannot_be_asserted_as_a_type_witness) :-
    user:'add-atom'('&self',[:,rt_spoof,'$any'(true)],true),
    program("(: rt_no_spoof (-> $a $a Number)) (= (rt_no_spoof $x $y) 7)",_),
    findall(R,user:rt_no_spoof(rt_spoof,2,R),Results),assertion(Results==[]).

test(eta_expansion_keeps_polymorphic_and_wildcard_inputs_checked) :-
    program("(: rt_eta_add (-> Number Number Number)) (= (rt_eta_add $x $y) (+ $x $y)) (: rt_eta_poly (-> Number $r)) (= (rt_eta_poly $x) (rt_eta_add $x)) (: rt_eta_open (-> Number %Undefined%)) (= (rt_eta_open $x) (rt_eta_add $x)) !(rt_eta_poly 1 2) !(collapse (rt_eta_poly \"bad\" 2)) !(collapse (rt_eta_open \"bad\" 2))",R),
    assertion(R == [3,[],[]]).
test(eta_expanded_partial_has_the_projected_function_interface) :-
    program("(: rt_eta_typed (-> Number (-> Number Number))) (= (rt_eta_typed $x) (rt_eta_add $x)) !(rt_apply_one (rt_eta_typed 1) 2)",R),
    assertion(R == [3]).
test(a_nonfunction_result_keeps_its_declared_arity) :-
    program("(: rt_eta_invalid (-> Number Number)) (= (rt_eta_invalid $x) (rt_eta_add $x)) !(collapse (rt_eta_invalid 1))",R),
    assertion(R == [[]]).
test(result_holding_uses_the_same_unanimous_policy) :-
    program("(: rt_mixed_result (-> Number Number)) (: rt_mixed_result (-> String Atom)) (= (rt_mixed_result $x) (+ 1 2)) !(rt_mixed_result 0) !(rt_mixed_result \"ok\")",R),
    assertion(R == [3,3]).

test(arity_only_changes_do_not_reuse_an_old_function_interface) :-
    program("(: rt_change_eta (-> Number $r)) (= (rt_change_eta $x) (rt_eta_add $x)) (= (rt_change_eta $x $y) (+ $x $y)) (: rt_fn_identity (-> (-> Number Number) $a (-> Number Number))) (= (rt_fn_identity $f $ignored) (let $_ (remove-atom &self (= (rt_change_eta $x) (rt_eta_add $x))) $f)) !(collapse (rt_fn_identity (rt_change_eta $n) 0))",R),
    assertion(R == [[]]).

test(predefined_list_types_cannot_be_forged_by_nominal_facts) :-
    program("(: rt_fake_list (ListOf Number)) (: rt_list_guard (-> (ListOf Number) Number)) (= (rt_list_guard $x) 7) !(collapse (rt_list_guard rt_fake_list)) !(collapse (let $_ (rt_list_guard $x) (let $x rt_fake_list 7)))",R),
    assertion(R == [[],[]]).
test(an_unanchored_constructor_is_not_a_universal_cast) :-
    program("(: rt_cast (-> $a)) (: rt_cast_same (-> $a $a Number)) (= (rt_cast_same $x $y) 7) !(collapse (rt_cast_same (rt_cast) 1))",R),
    assertion(R == [[]]).
test(ill_kinded_annotations_do_not_remove_a_values_canonical_type) :-
    program("(: rt_bad_kind (rt_Family ListOf)) (: rt_unused_param (-> $a Number)) (= (rt_unused_param $x) 7) (: rt_shared_param (-> $a $a Number)) (= (rt_shared_param $x $y) 7) !(rt_unused_param rt_bad_kind) !(rt_shared_param rt_bad_kind rt_bad_kind)",R),
    assertion(R == [7,7]).
test(primitive_values_keep_nominal_evidence_as_an_alternative) :-
    program("(: 2 rt_Even) (: rt_even_alias rt_Even) (: rt_even_id (-> rt_Even rt_Even)) (= (rt_even_id $x) $x) (: rt_even_poly (-> $a $a)) (= (rt_even_poly $x) rt_even_alias) !(rt_even_id 2) !(rt_even_poly 2)",R),
    assertion(R == [2,rt_even_alias]).
test(typing_updates_do_not_invent_an_unbound_space) :-
    catch(user:'add-atom'(_Space,[:,rt_no_space,rt_T],_),Error,true),
    assertion(nonvar(Error)),assertion(\+user:type_declaration(rt_no_space,_)).

test(compiled_membership_agrees_with_the_general_relation) :-
    program("(: oc_red oc_Colour) (: oc_blue oc_Colour)
      (: oc_Z oc_Nat) (: oc_S (-> oc_Nat oc_Nat))
      (: oc_Nil (oc_List $a)) (: oc_Cons (-> $a (oc_List $a) (oc_List $a)))
      (: oc_Box (-> $a oc_Boxed)) (: (oc_Pair $x $x) oc_Same)
      (: oc_bad_list (ListOf Number)) (: oc_cast (-> $a))
      (: 2 oc_Even) (: true oc_Enabled) (: \"s\" oc_Text)
      (: oc_inc (-> Number Number)) (= (oc_inc $x) (+ $x 1))",_),
    Values=[1,0,2,-2,2.5,"s",true,false,oc_red,oc_blue,unknown,oc_Z,
      [oc_S,oc_Z],[oc_S,[oc_S,oc_Z]],[oc_S,"bad"],oc_Nil,
      [oc_Cons,1,oc_Nil],[oc_Cons,"s",oc_Nil],
      [oc_Cons,1,[oc_Cons,"s",oc_Nil]],[oc_Box,1],[oc_Box,"s"],
      [oc_Pair,1,1],[oc_Pair,1,2],[],[1],[1,2],["s"],
      [oc_red,1],[oc_red|1],host(1),partial(oc_inc,[]),partial(oc_inc,[1]),
      oc_inc,oc_bad_list,[oc_cast]],
    Types=['Number','String','Bool','Symbol',oc_Colour,oc_Nat,oc_Boxed,oc_Same,oc_Even,oc_Enabled,oc_Text,
      [oc_List,'Number'],[oc_List,'String'],['ListOf','Number'],['ListOf','String'],
      ['TupleOf'],['TupleOf','Number'],['TupleOf',oc_Colour,'Number'],
      ['PairOf',oc_Colour,'Number'],['Opaque',host,1],['Opaque',partial,2],
      [->,'Number','Number'],[->,'Number'],[],['Number'],['Number','Number'],
      ['ListOf','ListOf'],['PairOf','Number','ListOf'],[oc_List,'TupleOf']],
    forall((member(V,Values),member(T,Types)),
      ((user:type_ground_check(T,V)->General=true;General=false),
       user:type_code_goal(T,V,[],Goal),(user:call(Goal)->Compiled=true;Compiled=false),
       assertion(General==Compiled))).

test(undeclared_data_heads_do_not_accumulate_compiler_entries) :-
    forall(between(1,100,I),
      (format(atom(H),'rt_undeclared_data_~d',[I]),
       once(user:type_member([H],_,[])),
       assertion(\+user:type_constructor_cache(known(H),_)))).

test(nominal_patterns_bind_the_parameters_they_share_with_their_type) :-
    program("(: (rt_Tag $t $v) (rt_Tagged $t)) (: rt_same_tag (-> (rt_Tagged $t) (rt_Tagged $t) Number)) (= (rt_same_tag $x $y) 7) (: rt_payload (-> (rt_Tagged $t) $t)) (= (rt_payload (rt_Tag $t $v)) $v) !(collapse (rt_same_tag (rt_Tag Number 1) (rt_Tag String 2))) !(rt_same_tag (rt_Tag Number 1) (rt_Tag Number 2)) !(rt_payload (rt_Tag Number 1)) !(collapse (rt_payload (rt_Tag String 1)))",R),
    assertion(R == [[],7,1,[]]).
test(open_nominal_patterns_stay_jointly_constrained) :-
    program("(: (rt_OTag $t $v) (rt_OTagged $t)) (: rt_open_tags (-> (rt_OTagged $t) (rt_OTagged $t) Number)) (= (rt_open_tags $x $y) 7) !(collapse (let $r (rt_open_tags (rt_OTag $a 1) (rt_OTag $b 2)) (let $a Number (let $b String $r)))) !(collapse (let $r (rt_open_tags (rt_OTag $a 1) (rt_OTag $b 2)) (let $a Number (let $b Number $r)))) !(collapse (let $r (rt_open_tags (rt_OTag $a 1) (rt_OTag String 2)) (let $a Number $r)))",R),
    assertion(R == [[],[7],[]]).
test(curried_declarations_guard_and_describe_the_function) :-
    program("(: rt_cur (-> Number (-> Number Number))) (= (rt_cur $x $y) (+ $x $y)) (: rt_takes_cur (-> (-> Number (-> Number Number)) Number)) (= (rt_takes_cur $g) (($g 1) 2)) (: rt_takes_flat (-> (-> Number Number Number) Number)) (= (rt_takes_flat $g) ($g 1 2)) !(rt_takes_cur rt_cur) !(rt_takes_flat rt_cur) !(collapse (rt_cur \"bad\" 2)) !(collapse (rt_takes_cur (rt_cur 0)))",R),
    assertion(R == [3,3,[],[]]).
test(ill_kinded_checks_give_ground_and_open_values_the_same_answer) :-
    program("(: kg_top (-> (ListOf ListOf) Number)) (= (kg_top $x) 7)
      (: kg_Box (-> (ListOf ListOf) kg_BoxT)) (: kg_field (-> kg_BoxT Number)) (= (kg_field $b) 7)
      (: kg_nested (-> (ListOf _) Number)) (= (kg_nested $x) 7)
      !(collapse (kg_top ())) !(collapse (let $r (kg_top $x) (let $x () $r)))
      !(collapse (kg_field (kg_Box ()))) !(collapse (let $r (kg_field (kg_Box $x)) (let $x () $r)))
      !(collapse (kg_nested ())) !(collapse (let $r (kg_nested $x) (let $x () $r)))",R),
    assertion(R == [[],[],[],[],[],[]]).
test(nested_families_compile_to_indexed_membership) :-
    T=['ListOf',['ListOf','Number']],user:type_code_goal(T,_,[],_),
    assertion(user:type_member_code('ListOf',['ListOf','Number'],_)),
    forall(user:type_member_code('ListOf',T,Name),
      (Head=..[Name,_],forall(clause(user:Head,Body),assertion(\+ (sub_term(S,Body),compound(S),S=type_ground_check(_,_)))))),
    forall(member(V-Expected,[[]-true,[[]]-true,[[1,2],[3]]-true,[[1,"s"]]-false,[1]-false]),
      ((user:type_ground_check(T,V)->General=true;General=false),
       user:type_code_goal(T,V,[],Goal),(user:call(Goal)->Compiled=true;Compiled=false),
       assertion(General-Compiled == Expected-Expected))).

test(typed_tail_recursion_runs_in_constant_space) :-
    program("!(import_prolog_function runtime_local_used) (: rt_stack_num (-> Number Number)) (= (rt_stack_num $n) (if (== $n 0) (runtime_local_used) (rt_stack_num (- $n 1))))",_),
    maplist(user:runtime_stack_delta(rt_stack_num,[]),[50,50000],[Short,Long]),
    assertion(Short=:=Long).
test(boolean_tail_guards_leave_no_choicepoints) :-
    program("(: rt_stack_bool (-> Number Bool Number)) (= (rt_stack_bool $n $b) (if (== $n 0) (runtime_local_used) (rt_stack_bool (- $n 1) $b)))",_),
    maplist(user:runtime_stack_delta(rt_stack_bool,[true]),[50,50000],[Short,Long]),
    assertion(Short=:=Long).
test(singleton_type_parameters_need_no_joint_frame) :-
    program("(: rt_stack_poly (-> $a Number)) (= (rt_stack_poly $n) (if (== $n 0) (runtime_local_used) (rt_stack_poly (- $n 1))))",_),
    maplist(user:runtime_stack_delta(rt_stack_poly,[]),[50,50000],[Short,Long]),
    assertion(Short=:=Long).
test(tail_calls_check_inputs_and_the_entry_checks_the_result) :-
    program("(: rt_tail_in (-> Number Number)) (= (rt_tail_in $n) (if (== $n 0) 0 (rt_tail_in \"bad\"))) (: rt_tail_out (-> Number Number)) (= (rt_tail_out $n) (if (== $n 0) \"bad\" (rt_tail_out (- $n 1)))) !(collapse (rt_tail_in 1)) !(collapse (rt_tail_out 3)) !(rt_tail_in 0)",R),
    assertion(R == [[],[],0]).
test(an_open_value_keeps_one_copy_of_each_delayed_test) :-
    program("(: rt_rel (-> Number Number Number)) (= (rt_rel 0 $x) $x) (= (rt_rel $n $x) (if (> $n 0) (rt_rel (- $n 1) $x) (empty)))",_),
    once(user:rt_rel(1000,X,R)),assertion(X==R),get_attr(X,freeze,Goals),
    aggregate_all(count,(sub_term(G,Goals),compound(G),G=number(_)),Copies),assertion(Copies =< 2),
    assertion(\+ X="bad"),X=7.
test(deferred_input_evidence_survives_a_function_definition) :-
    program("(: rt_def_g (-> Number Number)) (: rt_def_h (-> Number Number)) (: rt_def_keep (-> $a $a)) (= (rt_def_keep $x) (let $_ (add-atom &self (= (rt_def_g $p $q) $p)) rt_def_h)) !(rt_def_keep rt_def_g)",R),
    assertion(R == [rt_def_h]).

test(edit_in_a_failed_branch_keeps_input_evidence) :-
    program("(: ri_g (-> Number Number)) (: ri_h (-> Number Number)) (: ri_keep (-> $a $a)) (= (ri_keep $x) (superpose ((let $_ (add-atom &self (= (ri_g $p $q) $p)) (empty)) ri_h))) !(collapse (ri_keep ri_g))",R),
    assertion(R == [[ri_h]]).
test(edit_inside_collection_keeps_input_evidence) :-
    program("(: ri_cg (-> Number Number)) (: ri_ch (-> Number Number)) (: ri_collect (-> $a $a)) (= (ri_collect $x) (let $_ (collapse (let $_ (add-atom &self (= (ri_cg $p $q) $p)) (empty))) ri_ch)) !(collapse (ri_collect ri_cg))",R),
    assertion(R == [[ri_ch]]).
test(vacuous_open_tuple_releases_its_frame) :-
    program("(: ri_wrap (-> $a ($a))) (= (ri_wrap $x) ($x))",_),
    user:ri_wrap(X,[_]),assertion(\+get_attr(X,type_obligations,_)),
    assertion(\+ attvar(X)),X=7.
test(tail_call_observes_a_tightened_input_contract) :-
    program("(: ri_tight (-> Number Number)) (= (ri_tight $n) (if (== $n 0) 7 (let $_ (remove-atom &self (: ri_tight (-> Number Number))) (let $_ (add-atom &self (: ri_tight (-> String Number))) (ri_tight 0))))) !(collapse (ri_tight 1))",R),
    assertion(R == [[]]).
test(tail_call_observes_a_newly_admitted_input) :-
    program("(: ri_wide (-> Number Number)) (= (ri_wide $n) (if (== $n 0) (let $_ (remove-atom &self (: ri_wide (-> Number Number))) (let $_ (add-atom &self (: ri_wide (-> String Number))) (ri_wide \"ok\"))) 7)) !(collapse (ri_wide 0))",R),
    assertion(R == [[7]]).
test(tail_call_observes_a_changed_result_contract) :-
    program("(: ri_result (-> Number Number)) (= (ri_result $n) (if (== $n 0) 7 (let $_ (remove-atom &self (: ri_result (-> Number Number))) (let $_ (add-atom &self (: ri_result (-> Number String))) (ri_result 0))))) !(collapse (ri_result 1))",R),
    assertion(R == [[]]).
test(disjoint_nominal_evidence_does_not_generate_type_lists) :-
    call_with_time_limit(2,program("(: ri_a ri_A) (: ri_b ri_B) (: ri_disjoint (-> $a $a)) (= (ri_disjoint $x) ri_b) !(collapse (ri_disjoint ri_a))",R)),
    assertion(R == [[]]).
test(tail_call_observes_retired_eta_signature) :-
    program("(= (ri_add $x $y) (+ $x $y)) (: ri_eta (-> Number %Undefined%)) (= (ri_eta 0) (ri_add 0)) (= (ri_eta $n $x) (if (== $n \"ok\") 7 (let $_ (remove-atom &self (= (ri_eta 0) (ri_add 0))) (ri_eta \"ok\" $x)))) !(collapse (ri_eta 1 1))",R),
    assertion(R == [[7]]).

test(repeated_vacuous_calls_leave_no_frame_watchers) :-
    numlist(1,1000,Ns),maplist(user:runtime_wrap_once(X),Ns),
    assertion(\+get_attr(X,type_obligations,_)),assertion(\+ attvar(X)),X=7.
test(input_evidence_survives_another_threads_definition_edit) :-
    program("(: ri_thread_g (-> Number Number)) (: ri_thread_h (-> Number Number)) (: ri_thread_keep (-> $a $a))",_),
    setup_call_cleanup(message_queue_create(Events),
      setup_call_cleanup(message_queue_create(Release),
        (Term=[=,[ri_thread_keep,_],[let,_,[translatePredicate,[runtime_input_barrier,Events,Release]],ri_thread_h]],
         user:'add-atom'('&self',Term,_),
         setup_call_cleanup(
           thread_create((findall(R,user:ri_thread_keep(ri_thread_g,R),Rows),thread_send_message(Events,result(Rows))),Id,[]),
           (thread_get_message(Events,entered,[timeout(5)]),
            user:'add-atom'('&self',[=,[ri_thread_g,P,_],P],_),
            thread_send_message(Release,resume),thread_get_message(Events,result(Rows),[timeout(5)]),
            assertion(Rows==[ri_thread_h])),
           (thread_send_message(Release,resume),thread_join(Id,_)))),
        message_queue_destroy(Release)),message_queue_destroy(Events)).

:- end_tests(runtime_types).
