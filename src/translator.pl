:- use_module(library(nb_set), [empty_nb_set/1, add_nb_set/3]).
:- use_module(library(terms), [term_factorized/3]).
:- use_module(library(pairs), [group_pairs_by_key/2, pairs_values/2]).
:- use_module(library(varnumbers), [varnumbers/2]).

%Pattern matching, structural and functional/relational constraints on arguments:
constrain_args(X, X, []) :- (var(X); atomic(X)), !.
constrain_args([F, A, B], Out, Goals) :- nonvar(F),
                                         F == cons,
                                         constrain_args(A, A1, G1),
                                         constrain_args(B, B1, G2),
                                         Out = [A1|B1],
                                         append(G1, G2, Goals), !.
constrain_args([F|Args], Var, Goals) :- atom(F),
                                        note_translation_use(F, pattern),
                                        fun(F), !,
                                        translate_expr([F|Args], GoalsExpr, Var),
                                        flatten(GoalsExpr, Goals).
constrain_args(In, Out, Goals) :- ( In = [F|_], atom(F) -> note_translation_use(F, pattern) ; true ),
                                  maplist(constrain_args, In, Out, NestedGoalsList),
                                  flatten(NestedGoalsList, Goals), !.

%Flatten (= Head Body) MeTTa function into Prolog Clause:
translate_clause(Input, (Head :- BodyConj)) :- translate_clause(Input, (Head :- BodyConj), true).
translate_clause(Input, Clause, ConstrainArgs) :-
    translate_clause(Input, Clause, ConstrainArgs, auto).
translate_clause(Input, Clause, ConstrainArgs, Pos) :-
    Input = [=, [F|_], _],
    ( Pos == first -> LaterClause = false
    ; Pos == later -> LaterClause = true
    ; equation_arity(F, _, _) -> LaterClause = true
    ; LaterClause = false ),
    ( LaterClause == true, may_edit(F) -> StretchBody = true ; StretchBody = false ),
    in_unit(stored(Token, Used), Cut,
            translate_equation(Input, Clause0, ConstrainArgs, StretchBody),
            Edits, CutUsed),
    ( Edits > 0, \+ may_edit(F) -> assertz(may_edit(F)) ; true ),
    ( Used == true -> flag(petta_unit_token, Token, Token + 1), note_unit_token(Token) ; true ),
    ( CutUsed == true -> prepend_clause_cut(Clause0, Cut, Clause) ; Clause = Clause0 ).

prepend_clause_cut((Head :- true), Cut, (Head :- prolog_current_frame(CF), clause_cut_point(CF, Cut))) :- !.
prepend_clause_cut((Head :- Body), Cut, (Head :- prolog_current_frame(CF), clause_cut_point(CF, Cut), Body)).

translate_equation(Input, (Head :- BodyConj), ConstrainArgs, StretchBody) :-
                                               Input = [=, [F|Args0], BodyExpr],
                                               ( ConstrainArgs -> maplist(constrain_args, Args0, Args1, GoalsA),
                                                                  flatten(GoalsA,GoalsPrefix)
                                                                ; Args1 = Args0, GoalsPrefix = [] ),
                                               length(Args0, SourceArity),
                                               ( declared_output_type(F, SourceArity, 'Atom')
                                                 -> GoalsBody = [],
                                                    ExpOut = BodyExpr
                                                  ; translate_expr(BodyExpr, Gs0, Out0),
                                                    ( StretchBody == true
                                                      -> stretch(BodyExpr, Gs0, Out0, GoalsBody, ExpOut)
                                                       ; GoalsBody = Gs0, ExpOut = Out0 ) ),
                                               (  nonvar(ExpOut), ExpOut = partial(Base,Bound),
                                                  length(Bound, N),
                                                  eta_expansion_arity(Base, N, Arity)
                                               -> M is (Arity - N) - 1,
                                                  length(ExtraArgs, M), append(Bound, ExtraArgs, CallInArgs),
                                                  resolve_memoization(Base, CallInArgs, Out, Goal),
                                                  append(GoalsBody,[Goal],FinalGoals), append(Args1,ExtraArgs,HeadArgs)
                                               ; FinalGoals= GoalsBody , HeadArgs = Args1, Out = ExpOut ),
                                               append(HeadArgs, [Out], FinalArgs),
                                               Head =.. [F|FinalArgs],
                                               length(FinalArgs, CompiledArity),
                                               (arity(F, CompiledArity) -> true ; assertz(arity(F, CompiledArity))),
                                               append(GoalsPrefix, FinalGoals, Goals),
                                               goals_list_to_conj(Goals, BodyConj).

%Native procedures keep their existing primary arity (notably / and yall's
%extra / arities). A MeTTa function with several larger arities stays partial.
eta_mode(F, native) :- native_function(F), \+ equation_arity(F, _, _),
                      \+ pending_signature(F, _, _), !.
eta_mode(_, source).

eta_expansion_arity(F, N, A) :-
    findall(M, (arity(F, M), M > N + 1), Ms), sort(Ms, [A|Rest]),
    ( Rest == [] -> true ; eta_mode(F, native) ).

% Dependencies describe translation decisions, not occurrences in quoted data.
% A nested lambda records its own decisions, independently of its creator.
:- dynamic translated_from/2, translation_use/4, translation_decision/3, pending_signature/3,
           no_equations_clause/3, native_function/1, native_arity/2, equation_arity/3.

compile_equation(Term, Clause, Uses) :- compile_equation(Term, Clause, Uses, auto).
compile_equation(Term, Clause, Uses, Pos) :-
    ( nb_current(petta_translation_uses, Previous) -> true ; Previous = '$absent' ),
    Box = uses([]),
    setup_call_cleanup(nb_linkval(petta_translation_uses, Box),
        ( copy_term(Term, Input), once(translate_clause(Input, Clause, true, Pos)), arg(1, Box, Raw), sort(Raw, Uses) ),
        ( Previous == '$absent' -> nb_delete(petta_translation_uses)
        ; nb_linkval(petta_translation_uses, Previous) )).

note_translation_use(F, Use) :-
    ( atom(F), nb_current(petta_translation_uses, Box), Box = uses(Old)
      -> translation_key(F, Use, Key), nb_setarg(1, Box, [use(F, Use, Key)|Old])
    ; true ).

translation_key(F, data, Key) :-
    ( translator_rule(F) -> Key = translator
    ; fun(F) -> Key = function
    ; Key = data ).
translation_key(F, pattern, Key) :-
    ( fun(F) -> findall(A, arity(F, A), As), sort(As, Key) ; Key = data ).
translation_key(F, call(N), Key) :-
    ( translator_rule(F) -> Key = translator
    ; \+ fun(F) -> Key = data
    ; A is N + 1,
      ( edits_world(F) -> Edit = edits ; Edit = pure ),
      findall(T, catch(match('&self', [':', F, T], T, T), _, fail), Ts), sort(Ts, Types),
      ( arity(F, A)
        -> length(Args, N), resolve_memoization(F, Args, Out, Goal),
           ( Goal =.. [F|Direct], append(Args, [Out], Direct) -> Memo = direct ; Memo = memo ),
           Key = call(Memo, Types, Edit)
      ; findall(M, (arity(F, M), M > A), Ms), sort(Ms, More),
        ( More \= [] -> eta_mode(F, Mode), Key = partial(More, Types, Mode, Edit)
        ; arity(F, _) -> Key = over(Types, Edit)
        ; Key = partial_any(Types, Edit) ) ) ).

translation_use_valid(F, Use, Key) :- translation_key(F, Use, Now),
    ( Now =@= Key -> true
    % An old complete, untyped call can keep calling a data-returning fallback.
    ; Now == data, Use = call(N), Key == call(direct, [], pure), A is N + 1,
      no_equations_clause(F, A, _) ).

record_translation(Ref, Term, Uses) :- assertz(translated_from(Ref, Term)),
    forall(member(use(F, Use, Key), Uses),
        ( assertz(translation_use(F, Ref, Use, Key)),
          ( translation_decision(F, Use, Stored), Stored =@= Key -> true
          ; assertz(translation_decision(F, Use, Key)) ) )).
forget_translation(Ref) :-
    ( retract(clause_unit(Ref, Token)) -> retractall(live_unit(Token)) ; true ),
    findall(use(F, Use, Key), translation_use(F, Ref, Use, Key), Uses),
    retractall(translated_from(Ref, _)), retractall(translation_use(_, Ref, _, _)),
    retractall(equation_arity(_, _, Ref)),
    forall(member(use(F, Use, Key), Uses),
        ( translation_use(F, _, Use, Remaining), Remaining =@= Key -> true
        ; forall((clause(translation_decision(F, Use, Stored), true, R), Stored =@= Key), erase(R)) )).

% Only registration/publication changes the program. Compiled calls have no
% runtime lookup added to them. SWI's logical update view still applies at
% each callee entry, including in an already-running caller.
register_signature(Owner, F, A) :-
    assertz(pending_signature(F, A, Owner)),
    ( fun(F) -> true ; assertz(fun(F)) ),
    ( arity(F, A) -> true ; assertz(arity(F, A)) ),
    no_equations_answer(F, A).

register_file_signatures(space_only, _, space_only) :- !.
register_file_signatures(compile_functions, Forms, compile_functions(Owner)) :-
    flag(metta_file_signatures, Owner, Owner + 1),
    with_mutex(petta_definitions, transaction(
        ( findall(F-A, ( member(parsed(function, _, [=, [F|Args], _]), Forms),
                         length(Args, N), A is N + 1 ), Signatures),
          forall(member(F-A, Signatures), register_signature(Owner, F, A)),
          findall(F, member(F-_, Signatures), Fs), sort(Fs, Functions),
          forall(member(F, Functions), refresh_users(F, [])), bump_interface ) )).

% A failed/aborted load must not leave provisional arities for forms it never
% reached. Nested imports have independent owners.
finish_file_signatures(space_only) :- !.
finish_file_signatures(compile_functions(Owner)) :- with_mutex(petta_definitions, transaction(
    ( findall(F, pending_signature(F, _, Owner), Raw), sort(Raw, Fs),
      retractall(pending_signature(_, _, Owner)),
      forall(member(F, Fs), (sync_function_arities(F), refresh_users(F, []))) ) )).

install_definition(Space, Term, Owner, Clause) :-
    with_mutex(petta_definitions, transaction(
        ( Term = [=, [F|Args], _], length(Args, N), A is N + 1,
          ( Owner == runtime -> register_signature(Owner, F, A) ; true ),
          add_sexp(Space, Term),
          compile_equation(Term, Clause, Uses),
          assert_equation(Term, Clause, Uses, _),
          once(retract(pending_signature(F, A, Owner))),
          sync_function_arities(F), refresh_users(F, []), bump_interface,
          notify_translation_change(F) ) )).

assert_equation(Term, Clause, Uses, Ref) :-
    Clause = (Head :- _), functor(Head, F, A),
    ( retract(no_equations_clause(F, A, Empty)) -> erase(Empty) ; true ),
    assertz(Clause, Ref), assertz(equation_arity(F, A, Ref)), record_translation(Ref, Term, Uses),
    ( memberchk(token(Token), Uses) -> assertz(live_unit(Token)), assertz(clause_unit(Ref, Token)) ; true ).

install_lambda(Term, Clause) :- with_mutex(petta_definitions, transaction(
    ( compile_equation(Term, Clause, Uses), assert_equation(Term, Clause, Uses, _),
      Term = [=, [F|_], _], sync_function_arities(F) ) )).

user_dynamic_head(F, A, H) :- current_predicate(F/A), functor(H, F, A),
    predicate_property(H, dynamic), \+ predicate_property(H, imported_from(_)).

has_equations(F, A) :- equation_arity(F, A, _), !.

no_equations_answer(F, A) :-
    ( native_arity(F, A) ; has_equations(F, A) ; no_equations_clause(F, A, _) ), !.
no_equations_answer(F, A) :-
    N is A - 1, length(Args, N),
    append(Args, [[F|Args]], HeadArgs), Head =.. [F|HeadArgs],
    assertz(Head, Ref), assertz(no_equations_clause(F, A, Ref)).

sync_function_arities(F) :-
    % Registration/translation add candidate arities. Probe each candidate once
    % rather than enumerating every equation of a large multi-clause function.
    forall(arity(F, A),
        ( (native_arity(F, A); pending_signature(F, A, _); equation_arity(F, A, _))
          -> true ; retractall(arity(F, A)) )),
    ( ( native_function(F) ; arity(F, _) )
      -> ( fun(F) -> true ; assertz(fun(F)) )
    ; retractall(fun(F)) ).

refresh_users(F, Path) :-
    % Check each distinct decision once, even when thousands of callers share it.
    findall(G, ( translation_decision(F, Use, Key), \+ translation_use_valid(F, Use, Key),
                 translation_use(F, Ref, Use, Stored), Stored =@= Key,
                 translated_from(Ref, [=, [G|_], _]) ), Raw),
    sort(Raw, Users),
    forall(member(G, Users),
        ( memberchk(G, Path) -> throw(error(domain_error(finite_application_interface, [G|Path]), none))
        ; recompile_function(G), refresh_users(G, [G|Path]) )).

% Rebuild a whole predicate in clause order; publication and its metadata are
% one transaction. Never inspect native or imported clauses with clause/3.
recompile_function(F) :-
    %Source records preserve order even when clauses move between arities.
    findall(Ref-Term, ( Term = [=, [F|_], _], translated_from(Ref, Term),
                       clause(H, _, Ref), functor(H, F, A), user_dynamic_head(F, A, H) ), Pairs),
    findall(A, equation_arity(F, A, _), OldArities),
    recompile_equations(Pairs, first, Compiled),
    forall(member(Ref-_, Pairs), ( erase(Ref), forget_translation(Ref) )),
    forall(member(compiled(Term, Clause, Uses), Compiled),
           assert_equation(Term, Clause, Uses, _)),
    forall(member(A, OldArities), no_equations_answer(F, A)),
    sync_function_arities(F), notify_translation_change(F).

notify_translation_change(F) :-
    forall(metta_on_function_changed(F), true).

recompile_equations([], _, []).
recompile_equations([_-Term|Rest], Pos, [compiled(Term, Clause, Uses)|Cs]) :-
    compile_equation(Term, Clause, Uses, Pos),
    recompile_equations(Rest, later, Cs).

removed_equations(F, Refs) :-
    forall(member(Ref-A, Refs), ( erase(Ref), forget_translation(Ref), no_equations_answer(F, A) )),
    sync_function_arities(F),
    ( fun(F) -> true ; retractall(may_edit(F)) ),
    refresh_users(F, []), bump_interface,
    notify_translation_change(F),
    ( fun(F) -> true ; forall(metta_on_function_removed(F), true) ).

%%% Deciding code when it is reached %%%
%Code reached after the program may have changed is a stretch: it is translated ahead
%as usual and checked on entry; if a decision it relied on no longer holds, the stretch
%is translated fresh there, with its variables standing for their already-computed values.
%A stored equation's stretches stay valid while caller refresh keeps its token live;
%transient queries and evals while the interface revision is unchanged.
:- dynamic may_edit/1, live_unit/1, clause_unit/2.

may_change_interface(Atom) :- ( var(Atom) -> true ; Atom = [E|_], ( var(E) ; E == (=) ; E == (:) ) ).

edits_world(F) :- ( may_edit(F) ; memberchk(F, ['import!', import_prolog_function, 'add-translator-rule!', 'remove-translator-rule!']) ), !.

bump_interface :- flag(petta_iface_rev, R, R + 1).
interface_is(Revision) :- flag(petta_iface_rev, Revision, Revision).

%A translation unit u(Kind, Edits, Cut, CutUsed) tracks whether translated code may
%change the program, and whether a stretch in a stored clause contains a direct cut.
%b_setval trails the outer unit so failure or exception restores it automatically.
in_unit(Kind, Cut, Goal, Edits, CutUsed) :-
    ( nb_current(petta_unit, Prev) -> true ; Prev = none ),
    Unit = u(Kind, 0, Cut, false),
    b_setval(petta_unit, Unit),
    call(Goal),
    arg(2, Unit, Edits), arg(4, Unit, CutUsed),
    b_setval(petta_unit, Prev).

note_edit :- ( nb_current(petta_unit, U), U = u(_, N, _, _) -> N1 is N + 1, nb_setarg(2, U, N1) ; true ).
counting(Goal, Edited) :-
    ( nb_current(petta_unit, U), U = u(_, N0, _, _)
      -> call(Goal), arg(2, U, N1), ( N1 > N0 -> Edited = true ; Edited = false )
       ; call(Goal), Edited = false ).
without_cut(Goal) :-
    ( nb_current(petta_unit, U), U = u(_, _, Cut, _), Cut \== none
      -> setup_call_cleanup(nb_setarg(3, U, none), call(Goal), nb_setarg(3, U, Cut))
       ; call(Goal) ).

%An eval of a literal expression edits only if its text may edit; record named heads
%so a late-defined editor inside eval still refreshes the enclosing equation:
note_eval(Expr) :- ( var(Expr) -> note_edit
                   ; compound(Expr) -> ( text_edits(Expr) -> note_edit ; true )
                   ; true ).
text_edits([H|T]) :-
    ( var(H) -> true
    ; H == quote -> fail
    ; atom(H) -> ( is_list(T), length(T, N), note_translation_use(H, call(N)), fail
                 ; text_edit_head(H, T) -> true
                 ; member(A, T), compound(A), text_edits(A), ! )
    ; member(A, [H|T]), compound(A), text_edits(A), ! ).
text_edit_head('add-atom', [_, Atom]) :- !, may_change_interface(Atom).
text_edit_head('remove-atom', [_, Atom]) :- !, may_change_interface(Atom).
text_edit_head(eval, [E]) :- !, ( var(E) -> true ; compound(E), text_edits(E) ).
text_edit_head(H, _) :- edits_world(H).

translate_transient(Expr, Goals, Out) :- translate_transient(Expr, none, Goals, Out).
translate_transient(Expr, Cut, Goals, Out) :-
    in_unit(transient, Cut, translate_expr(Expr, Goals, Out), _, _).
note_unit_token(Token) :- ( nb_current(petta_translation_uses, Box), Box = uses(Old)
                            -> nb_setarg(1, Box, [token(Token)|Old]) ; true ).

stretch_check(Check) :- ( nb_current(petta_unit, u(Kind, _, _, _)) -> true ; Kind = none ),
                        ( Kind = stored(Token, Used) -> Used = true, Check = live_unit(Token)
                        ; Kind == transient -> flag(petta_iface_rev, Revision, Revision), Check = interface_is(Revision)
                        ; Check = fail ).

%Wrap ahead-of-time goals Gs (producing Fast) for Source as a revalidated stretch.
%Variables, literals and quotes are already values and never need retranslation.
%Source is stored ground (via numbervars), so the slow path adds no clause variables;
%Fast is aliased to Out only when it is a fresh output variable not shared with Vs.
stretch(Source, Gs, Fast, Gs, Fast) :- ( var(Source) ; atomic(Source) ; Source = [Q, _], Q == quote ), !.
stretch(Source, Gs, Fast, [( Check -> Ahead ; Late )], Out) :-
    term_variables(Source, Vs), copy_term_nat(Vs-Source, Template), numbervars(Template, 0, _),
    goals_list_to_conj(Gs, Conj), stretch_check(Check),
    ( var(Fast), \+ memberchk_eq(Fast, Vs) -> Out = Fast, Ahead = Conj ; Ahead = (Out = Fast, Conj) ),
    ( stretch_cut(Source, Cut) -> Late = late_call(Template, Vs, Out, Cut)
                                ; Late = late_call(Template, Vs, Out) ).
stretch_conj(Source, Gs, Fast, Conj, Out) :- stretch(Source, Gs, Fast, Goals, Out), goals_list_to_conj(Goals, Conj).

maybe_stretch(true, Expr, Gs0, Out0, _, Gs, Out, none) :- !, stretch(Expr, Gs0, Out0, Gs, Out).
maybe_stretch(false, _, Gs, Out, Ev, Gs, Out, Ev).
maybe_stretch_conj(true, Expr, Gs, Fast, Conj, Out) :- !, stretch_conj(Expr, Gs, Fast, Conj, Out).
maybe_stretch_conj(false, _, Gs, Out, Conj, Out) :- goals_list_to_conj(Gs, Conj).
either_true(false, false, false) :- !.
either_true(_, _, true).

%A body run once per element of a loop; cut is local to the element callback.
live_conj(PriorEdited, Body, Conj, Out) :-
    without_cut(counting(translate_expr(Body, Gs, Fast), BodyEdits)),
    either_true(PriorEdited, BodyEdits, Live),
    maybe_stretch_conj(Live, Body, Gs, Fast, Conj, Out).

stretch_cut(Source, Cut) :-
    nb_current(petta_unit, U), U = u(_, _, Cut, _), Cut \== none,
    contains_direct_cut(Source),
    nb_setarg(4, U, true).

contains_direct_cut(X) :- is_list(X), X = [H|T],
    ( H == cut, T == [] -> true
    ; atom(H), ( H == quote ; cut_opaque_head(H) ) -> fail
    ; ( contains_direct_cut(H) ; member(Arg, T), contains_direct_cut(Arg) ), ! ).

cut_opaque_head(H) :- memberchk(H, [collapse, test, once, hyperpose, with_mutex, transaction,
                                    catch, forall, foldall, 'foldl-atom', 'map-atom', 'filter-atom', '|->']).

%Capture the choice point immediately outside ClauseFrame in O(1) so a (cut) inside
%a freshly translated stretch commits that clause without cutting the caller.
clause_cut_point(ClauseFrame, Cut) :-
    prolog_current_choice(Ch),
    choice_above_frame(Ch, ClauseFrame, Cut).

choice_above_frame(Ch, Frame, Cut) :-
    ( prolog_choice_attribute(Ch, frame, CF), CF >= Frame
      -> prolog_choice_attribute(Ch, parent, Parent),
         choice_above_frame(Parent, Frame, Cut)
       ; Cut = Ch ).

late_call(Template, Vars, Out) :- late_call(Template, Vars, Out, none).
late_call(Template, Vars, Out, Cut) :-
    varnumbers(Template, TemplateVars-Source),
    translate_transient(Source, Cut, Goals, Value),
    TemplateVars = Vars, Out = Value,
    call_goals(Goals).

%Translate arguments left-to-right once, stopping right after the first argument that may edit.
split_args_at_edit([], [], [], [], false).
split_args_at_edit([A|As], Gs, [V|Vs], Rest, Edited) :-
    counting(translate_expr(A, GsA, V), AEdited),
    ( AEdited == true
      -> Gs = GsA, Vs = [], Rest = As, Edited = true
       ; split_args_at_edit(As, GsRest, Vs, Rest, Edited),
         append(GsA, GsRest, Gs) ).

%Build a single revalidated stretch for [Head | PrefixVars ++ Rest] where already-evaluated
%PreVals bind PrefixVars only after the residual template is captured (never re-evaluated).
stretch_applied(Head, PreVals, Rest, StretchGs, Out) :-
    length(PreVals, K), length(PrefixVars, K),
    append(PrefixVars, Rest, ResidualArgs),
    ( ( atom(Head) ; nonvar(Head), Head = partial(_, _) )
      -> Residual = [Head|ResidualArgs], BindHead = true
       ; Residual = [HeadVar|ResidualArgs], BindHead = (HeadVar = Head) ),
    translate_expr(Residual, FastGs, FastOut),
    stretch(Residual, FastGs, FastOut, StretchGs, Out),
    call(BindHead),
    PrefixVars = PreVals.

stretch_wrapped(Wrapper, F, PreVals, Rest, StretchGs, Out) :-
    length(PreVals, K), length(PrefixVars, K),
    append(PrefixVars, Rest, ResidualArgs),
    Residual = [Wrapper, [F|ResidualArgs]],
    translate_expr(Residual, FastGs, FastOut),
    stretch(Residual, FastGs, FastOut, StretchGs, Out),
    PrefixVars = PreVals.

%Print compiled clause:
maybe_print_compiled_clause(_, _, _) :- silent(true), !.
maybe_print_compiled_clause(Label, FormTerm, Clause) :-
    swrite(FormTerm, FormStr),
    format("\e[33m-->  ~w  -->~n\e[36m~w~n\e[33m--> prolog clause -->~n\e[32m", [Label, FormStr]),
    portray_clause(current_output, Clause),
    format("\e[33m^^^^^^^^^^^^^^^^^^^^^~n\e[0m").

%Conjunction builder, turning goals list to a flat conjunction:
goals_list_to_conj([], true)      :- !.
goals_list_to_conj([G], G)        :- !.
goals_list_to_conj([G|Gs], (G,R)) :- goals_list_to_conj(Gs, R).

resolve_memoization(Fun, Args, Out, Goal) :-
    ( metta_memoized_dispatch_call(Fun, Args, Out, Goal)
    -> true
    ; append(Args, [Out], DirectArgs),
      Goal =.. [Fun|DirectArgs]
    ).
incomplete_application_kind(Fun, Arity, partial) :- ( arity(Fun, KnownArity), KnownArity >= Arity
                                                     ; \+ arity(Fun, _) ), !.
incomplete_application_kind(_, _, overapplied).

throw_function_overapplication(Fun, ActualInputArity) :-
    findall(InputArity, (arity(Fun, Arity), InputArity is Arity - 1), InputArities),
    sort(InputArities, KnownInputArities),
    throw(error(domain_error(function_input_arities(Fun, KnownInputArities), ActualInputArity), none)).

% Runtime dispatcher: call F if it's a registered fun/1, else keep as list:
reduce([F|Args], Out) :- nonvar(F), atom(F), fun(F)
                         -> % --- Case 1: callable predicate ---
                            length(Args, N),
                            Arity is N + 1,
                            ( ( arity(F, Arity)
                              ; native_function(F), current_predicate(F/Arity),
                                \+ no_equations_clause(F, Arity, _) ),
                              \+ (current_op(_, _, F), Arity =< 2)
                              -> resolve_memoization(F, Args, Out, Goal),
                                 catch(call(Goal), _, fail)
                            ; incomplete_application_kind(F, Arity, partial)
                              -> Out = partial(F,Args)
                            ; throw_function_overapplication(F, N) )
                          ; % --- Case 2: partial closure ---
                            compound(F), F = partial(Base, Bound) -> append(Bound, Args, NewArgs),
                                                                     reduce([Base|NewArgs], Out)
                          ; % --- Case 3: leave unevaluated ---
                            Out = [F|Args],
                            \+ cyclic_term(Out).

%Calling reduce from aggregate function foldall needs this argument wrapping
agg_reduce(AF, Acc, Val, NewAcc) :- reduce([AF, Acc, Val], NewAcc).

%Combined expr translation to goals list
translate_expr_to_conj(Input, Conj, Out) :- translate_expr_to_conj(Input, Conj, Out, _).
translate_expr_to_conj(Input, Conj, Out, Evidence) :- translate_expr(Input, Goals, Out, Evidence),
                                                      goals_list_to_conj(Goals, Conj).

%Special stream operation rewrite rules before main translation
rewrite_streamops(['trace!', Arg1, Arg2],
                  [progn, ['println!', Arg1], Arg2]).
rewrite_streamops([unique, Arg],
                  [call, [superpose, ['unique-atom', [collapse, Arg]]]]).
rewrite_streamops(['alpha-unique', Arg],
                  [call, [superpose, ['alpha-unique-atom', [collapse, Arg]]]]).
rewrite_streamops([union, [superpose|A], [superpose|B]],
                  [call, [superpose, ['union-atom', [collapse, [superpose|A]],
                                                    [collapse, [superpose|B]]]]]).
rewrite_streamops([intersection, [superpose|A], [superpose|B]],
                  [call, [superpose, ['intersection-atom', [collapse, [superpose|A]],
                                                           [collapse, [superpose|B]]]]]).
rewrite_streamops([subtraction, [superpose|A], [superpose|B]],
                  [call, [superpose, ['subtraction-atom', [collapse, [superpose|A]],
                                                          [collapse, [superpose|B]]]]]).
rewrite_streamops(X, X).

%Guarded stream ops rewrite rule application, successfully avoiding copy_term:
safe_rewrite_streamops(In, Out) :- ( compound(In), In = [Op|_], atom(Op) -> rewrite_streamops(In, Out)
                                                                          ; Out = In).

%Turn MeTTa code S-expression into goals list:
translate_expr(In, Goals, Out) :- translate_expr(In, Goals, Out, _).
translate_expr(X, [], X, none)          :- ((var(X) ; atomic(X)) ; X = partial(_,_)), !.
translate_expr([H0|T0], Goals, Out, Evidence) :-
        safe_rewrite_streamops([H0|T0],[H|T]),
        ( atom(H) -> GsH = [], HV = H, HeadEvidence = none, HeadEdited = false
                   ; counting(translate_expr(H, GsH, HV, HeadEvidence), HeadEdited) ),
        %--- Translator rules ---:
        ( nonvar(HV), translator_rule(HV) -> note_translation_use(HV, data),
                                             ( catch(match('&self', [':', HV, TypeChain], TypeChain, TypeChain), _, fail)
                                               -> TypeChain = [->|Xs],
                                                  append(ArgTypes, [_], Xs),
                                                  translate_args_by_type(T, ArgTypes, GsT, T1)
                                                ; translate_args(T, GsT, T1) ),
                                             append(T1,[Gs],Args),
                                             HookCall =.. [HV|Args],
                                             call(HookCall),
                                             translate_expr(Gs, GsE, Out, Evidence),
                                             append([GsH,GsT,GsE],Goals)
        %--- Non-determinism ---:
        ; HV == superpose, T = [Args], is_list(Args) -> build_superpose_branches(Args, Out, Branches),
                                                        disj_list(Branches, Disj),
                                                        append(GsH, [Disj], Goals)
        ; HV == collapse, T = [E] -> without_cut(translate_expr_to_conj(E, Conj, EV)),
                                     append(GsH, [findall(EV, Conj, Out)], Goals)
        ; HV == cut, T = [] -> ( nb_current(petta_unit, u(transient, _, Cut, _)), Cut \== none
                                 -> CutGoal = prolog_cut_to(Cut)
                                  ; CutGoal = (!) ),
                               append(GsH, [CutGoal], Goals),
                               Out = true
        ; HV == test, T = [Expr, Expected] -> without_cut(counting(translate_expr_to_conj(Expr, Conj, Val), EE)),
                                              counting(translate_expr(Expected, GsE0, ExpVal0), XE),
                                              either_true(EE, XE, ELive),
                                              maybe_stretch(ELive, Expected, GsE0, ExpVal0, _, GsE, ExpVal, _),
                                              Goal1 = ( findall(Val, Conj, Results),
                                                        (Results = [Actual] -> true
                                                                             ; Actual = Results ) ),
                                              append(GsH, [Goal1], G1),
                                              append(G1, GsE, G2),
                                              append(G2, [test(Actual, ExpVal, Out)], Goals)
        ; HV == once, T = [X] -> without_cut(translate_expr_to_conj(X, Conj, Out, Evidence)),
                                 append(GsH, [once(Conj)], Goals)
        ; HV == hyperpose, T = [L]
          -> ( nonvar(L), is_list(L)
               -> without_cut(build_hyperpose_branches(L, Branches)),
                  append(GsH, [concurrent_and(member((Goal,Res), Branches), (call(Goal), Out = Res))], Goals)
               ; translate_expr(L, GsL, LV),
                 append(GsH, GsL, Inner),
                 append(Inner, [hyperpose_runtime(LV, Out)], Goals),
                 note_edit )
        ; HV == with_mutex, T = [M,X] -> without_cut(translate_expr_to_conj(X, Conj, Out, Evidence)),
                                         append(GsH, [with_mutex(M,Conj)], Goals)
        ; HV == transaction, T = [X] -> without_cut(translate_expr_to_conj(X, Conj, Out, Evidence)),
                                        append(GsH, [transaction(Conj)], Goals)
        %--- Sequential execution ---:
        ; HV == progn, T = Exprs -> translate_progn(Exprs, GsList, Out, Evidence),
                                    append(GsH, GsList, Goals)
        ; HV == prog1, T = [First|Rest] -> counting(translate_expr(First, GsF, Out, Evidence), FEdits),
                                           ( Rest == [] -> GsRest = []
                                           ; counting(translate_progn(Rest, GsR0, ROut0, _), REdits),
                                             either_true(FEdits, REdits, RLive),
                                             maybe_stretch(RLive, [progn|Rest], GsR0, ROut0, _, GsRest, _, _) ),
                                           append([GsH, GsF, GsRest], Goals)
        %--- Conditionals ---:
        ; HV == if, T = [Cond, Then] -> counting(translate_expr_to_conj(Cond, ConC, Cv), CE),
                                        counting(translate_expr(Then, GThen, ThenV), TE),
                                        either_true(CE, TE, Live),
                                        maybe_stretch_conj(Live, Then, GThen, ThenV, ConT, Tv),
                                        build_branch(ConT, Tv, Out, BT),
                                        ( ConC == true -> append(GsH, [ ( Cv == true -> BT ) ], Goals)
                                                        ; append(GsH, [ ( ConC, ( Cv == true -> BT ) ) ], Goals) )
        ; HV == if, T = [Cond, Then, Else] -> counting(translate_expr_to_conj(Cond, ConC, Cv), CE),
                                              counting(translate_expr(Then, GThen, ThenV), TE),
                                              counting(translate_expr(Else, GElse, ElseV), EE),
                                              either_true(CE, TE, L0), either_true(L0, EE, Live),
                                              maybe_stretch_conj(Live, Then, GThen, ThenV, ConT, Tv),
                                              maybe_stretch_conj(Live, Else, GElse, ElseV, ConE, Ev),
                                              build_branch(ConT, Tv, Out, BT),
                                              build_branch(ConE, Ev, Out, BE),
                                              ( ConC == true -> append(GsH, [ (Cv == true -> BT ; BE) ], Goals)
                                                              ; append(GsH, [ (ConC, (Cv == true -> BT ; BE)) ], Goals) )
        ; HV == case, T = [KeyExpr, PairsExpr] -> ( select(Found0, PairsExpr, Rest0),
                                                    subsumes_term(['Empty', _], Found0),
                                                    Found0 = ['Empty', DefaultExpr],
                                                    NormalCases = Rest0
                                                    -> counting(translate_expr_to_conj(KeyExpr, GkConj, Kv), KE),
                                                       translate_case(NormalCases, KE, Kv, Out, CaseGoal, KeyGoal),
                                                       counting(translate_expr(DefaultExpr, GDef, DOut0), DE),
                                                       either_true(KE, DE, DLive),
                                                       maybe_stretch_conj(DLive, DefaultExpr, GDef, DOut0, ConD, DOut),
                                                       build_branch(ConD, DOut, Out, DefaultThen),
                                                       case_with_empty(GkConj, CaseGoal, DefaultThen, Combined),
                                                       append([GsH, KeyGoal, [Combined]], Goals)
                                                     ; counting(translate_expr(KeyExpr, Gk, Kv), KE),
                                                       translate_case(PairsExpr, KE, Kv, Out, IfGoal, KeyGoal),
                                                       append([GsH, Gk, KeyGoal, [IfGoal]], Goals) )
        %--- Short-circuit boolean operators ---:
        ; HV == 'and-then', T = [A, B] -> counting(translate_expr_to_conj(A, ConjA, Av), AE),
                                           counting(translate_expr(B, GB, Bv0), BE),
                                           either_true(AE, BE, Live),
                                           maybe_stretch_conj(Live, B, GB, Bv0, ConjB, Bv),
                                           append(GsH, [(ConjA, (Av == true -> (ConjB, Out = Bv) ; Out = false))], Goals)
        ; HV == 'or-else', T = [A, B] -> counting(translate_expr_to_conj(A, ConjA, Av), AE),
                                          counting(translate_expr(B, GB, Bv0), BE),
                                          either_true(AE, BE, Live),
                                          maybe_stretch_conj(Live, B, GB, Bv0, ConjB, Bv),
                                          append(GsH, [(ConjA, (Av == true -> Out = true ; (ConjB, Out = Bv)))], Goals)
        %--- Unification constructs ---:
        ; (HV == let ; HV == chain), T = [Pat, Val, In] -> counting(translate_expr(Pat, Gp, Pv), PatEdits),
                                                           counting(translate_expr(Val, Gv, V), ValEdits),
                                                           counting(translate_expr(In, Gi0, Out0, Ev0), InEdits),
                                                           either_true(PatEdits, ValEdits, L0), either_true(L0, InEdits, Live),
                                                           maybe_stretch(Live, In, Gi0, Out0, Ev0, Gi, Out, Evidence),
                                                           append([GsH,[(Pv=V)],Gp,Gv,Gi], Goals)
        ; HV == 'let*', T = [Binds, Body] -> letstar_to_rec_let(Binds,Body,RecLet),
                                             translate_expr(RecLet, Goals, Out, Evidence)
        ; HV == sealed, T = [Vars, Expr] -> translate_expr_to_conj(Expr, Con, Val),
                                            Goals = [copy_term(Vars,[Con,Val],_,[Ncon,Out]),Ncon]
        %--- Iterating over non-deterministic generators without reification ---:
        ; HV == 'forall', T = [GF, TF]
          -> without_cut((
               ( is_list(GF) -> GF = [GFH|GFA],
                                translate_expr(GFH, GsGFH, GFHV),
                                translate_args(GFA, GsGFA, GFAv),
                                append(GsGFH, GsGFA, GsGF),
                                GenList = [GFHV|GFAv]
                              ; translate_expr(GF, GsGF, GFHV),
                                GenList = [GFHV] ),
               translate_expr(TF, GsTF, TFHV) )),
             TestList = [TFHV, V],
             goals_list_to_conj(GsGF, GPre),
             GenGoal = (GPre, reduce(GenList, V)),
             append(GsH, GsTF, Tmp0),
             append(Tmp0, [( forall(GenGoal, ( reduce(TestList, Truth), Truth == true )) -> Out = true ; Out = false )], Goals),
             note_edit
        ; HV == 'foldall', T = [AF, GF, InitS]
          -> without_cut((
               translate_expr_to_conj(InitS, ConjInit, Init),
               translate_expr(AF, GsAF, AFV),
               ( GF = [M|_], (M==match ; M==let ; M=='let*') -> LambdaGF = ['|->', [], GF],
                                                                translate_expr(LambdaGF, GsGF, GFHV),
                                                                GenList = [GFHV]
               ; is_list(GF) -> GF = [GFH|GFA],
                                translate_expr(GFH, GsGFH, GFHV),
                                translate_args(GFA, GsGFA, GFAv),
                                append(GsGFH, GsGFA, GsGF),
                                GenList = [GFHV|GFAv]
                              ; translate_expr(GF, GsGF, GFHV),
                                GenList = [GFHV] ) )),
             append(GsH, GsAF, Tmp1),
             append(Tmp1, GsGF, Tmp2),
             append(Tmp2, [ConjInit, foldall(agg_reduce(AFV, V), reduce(GenList, V), Init, Out)], Goals),
             note_edit
        %--- Higher-order functions with pseudo-lambdas and lambdas ---:
        ; HV == 'foldl-atom', T = [List, Init, AccVar, XVar, Body]
          -> counting(translate_expr_to_conj(List, ConjList, L), LE),
             counting(translate_expr_to_conj(Init, ConjInit, InitV), IE),
             ( ( LE == true ; IE == true ) -> PreE = true ; PreE = false ),
             live_conj(PreE, Body, BodyConj, BG),
             exclude(==(true), [ConjList, ConjInit], CleanConjs),
             append(GsH, CleanConjs, GsMid),
             append(GsMid, [foldl([XVar, AccVar, NewAcc]>>(BodyConj, ( number(BG) -> NewAcc is BG ; NewAcc = BG )), L, InitV, Out)], Goals)
        ; HV == 'map-atom', T = [List, XVar, Body]
          -> counting(translate_expr_to_conj(List, ConjList, L), LE),
             live_conj(LE, Body, BodyCallConj, BodyCall),
             exclude(==(true), [ConjList], CleanConjs),
             append(GsH, CleanConjs, GsMid),
             append(GsMid, [maplist([XVar, Y]>>(BodyCallConj, ( number(BodyCall) -> Y is BodyCall ; Y = BodyCall )), L, Out)], Goals)
        ; HV == 'filter-atom', T = [List, XVar, Cond]
          -> counting(translate_expr_to_conj(List, ConjList, L), LE),
             live_conj(LE, Cond, CondConj, CondGoal),
             exclude(==(true), [ConjList], CleanConjs),
             append(GsH, CleanConjs, GsMid),
             append(GsMid, [include([XVar]>>(CondConj, CondGoal), L, Out)], Goals)
        ; HV == '|->', T = [Args, Body] -> next_lambda_name(F),
                                           % find free (non-argument) variables in Body
                                           term_variables(Body, AllVars),
                                           term_variables(Args, ArgVars),
                                           exclude({ArgVars}/[V]>>memberchk_eq(V, ArgVars), AllVars, FreeVars),
                                           append(FreeVars, Args, FullArgs),
                                           % compile clause with all bound + free vars
                                           Lambda = [=, [F|FullArgs], Body],
                                           install_lambda(Lambda, Clause),
                                           ( FreeVars == [] -> true ; note_translation_use(F, pattern) ),
                                           format(atom(Label), "metta lambda (~w)", [F]),
                                           maybe_print_compiled_clause(Label, ['|->', Args, Body], Clause),
                                           % emit closure capturing the environment (free vars)
                                           ( FreeVars == [] -> Out = F
                                                             ; Out = partial(F, FreeVars) ),
                                           Goals = GsH
        %--- Spaces ---:
        ; ( HV == 'add-atom' ; HV == 'remove-atom' ), T = [Space,Atom] ->
                                                                   translate_expr(Space, G1, S),
                                                                   Goal =.. [HV,S,Atom,Out],
                                                                   append([GsH,G1,[Goal]], Goals),
                                                                   ( may_change_interface(Atom) -> note_edit ; true )
        ; HV == match, T = [Space, Pattern, Body] -> counting(translate_expr(Space, G1, S), SE),
                                                     counting(translate_expr(Body, GsB0, Out0, Ev0), BodyEdits),
                                                     either_true(SE, BodyEdits, Live),
                                                     maybe_stretch(Live, Body, GsB0, Out0, Ev0, GsB, Out, Evidence),
                                                     append(G1, [match(S, Pattern, Out, Out)], G2),
                                                     append(G2, GsB, Goals)
        %--- Predicate to compiled goal ---:
        ; HV == translatePredicate, T = [Expr] -> Expr = [S|Args],
                                                  split_args_at_edit(Args, PreGs, PreVals, RestArgs, ArgEdited),
                                                  ( ArgEdited == true
                                                    -> stretch_wrapped(translatePredicate, S, PreVals, RestArgs, StretchGs, Out),
                                                       append([GsH, PreGs, StretchGs], Goals)
                                                     ; Goal =.. [S|PreVals],
                                                       append(GsH, PreGs, Inner),
                                                       append(Inner, [Goal], Goals) )
        %--- Manual dispatch options: ---
        %Generate a predicate call on compilation, translating Args for nesting:
        ; HV == call,  T = [Expr] -> Expr = [F|Args],
                                     ( atom(F) -> length(Args, FN), note_translation_use(F, call(FN)),
                                                  ( edits_world(F) -> note_edit ; true )
                                                ; note_edit ),
                                     split_args_at_edit(Args, PreGs, PreVals, RestArgs, ArgEdited),
                                     ( ArgEdited == true
                                       -> stretch_wrapped(call, F, PreVals, RestArgs, StretchGs, Out),
                                          append([GsH, PreGs, StretchGs], Goals)
                                        ; append(GsH, PreGs, Inner),
                                          append(PreVals, [Out], CallArgs),
                                          Goal =.. [F|CallArgs],
                                          append(Inner, [Goal], Goals) )
        %Produce a dynamic dispatch, translating Args for nesting:
        ; HV == reduce, T = [Expr] -> ( var(Expr) -> translate_expr(Expr, GsH, ExprOut),
                                                     Goals = [reduce(ExprOut, Out)|GsH], note_edit
                                                   ; Expr = [F|Args],
                                                     ( atom(F) -> length(Args, FN), note_translation_use(F, call(FN)),
                                                                  ( edits_world(F) -> note_edit ; true )
                                                                ; note_edit ),
                                                     split_args_at_edit(Args, PreGs, PreVals, RestArgs, ArgEdited),
                                                     ( ArgEdited == true
                                                       -> stretch_wrapped(reduce, F, PreVals, RestArgs, StretchGs, Out),
                                                          append([GsH, PreGs, StretchGs], Goals)
                                                        ; append(GsH, PreGs, Inner),
                                                          ExprOut = [F|PreVals],
                                                          append(Inner, [reduce(ExprOut, Out)], Goals) ) )
        %Invoke translator to evaluate MeTTa code as data/list:
        ; HV == eval, T = [Arg] -> append(GsH, [], Inner),
                                   Goal = eval(Arg, Out),
                                   append(Inner, [Goal], Goals),
                                   note_eval(Arg)
        %Force arg to remain data/list:
        ; HV == quote, T = [Expr] -> append(GsH, [], Inner),
                                     Out = Expr,
                                     Goals = Inner
        ; HV == 'catch', T = [Expr] ->
          without_cut(translate_expr(Expr, GsExpr, ExprOut)),
          append(GsH, [], Inner),
          goals_list_to_conj(GsExpr, Conj),
          Goal = catch((Conj, Out = ExprOut),
                       Exception,
                       (Exception = error(Type, Ctx) -> Out = ['Error', Type, Ctx]
                                                      ; Out = ['Error', Exception])),
          append(Inner, [Goal], Goals)
        %--- Automatic 'smart' dispatch, translator deciding when to create a predicate call, data list, or dynamic dispatch: ---
        ; is_list(T),
          ( atom(HV), fun(HV), Fun = HV, Bound = [], IsPartial = false
          ; compound(HV), HV = partial(Fun, Bound), IsPartial = true )
          -> length(Bound, NB), length(T, NT), InputArity is NB + NT,
             note_translation_use(Fun, call(InputArity)),
             ( edits_world(Fun) -> note_edit ; true ),
             findall(TypeChain, catch(match('&self', [':', Fun, TypeChain], TypeChain, TypeChain), _, fail), TypeChains),
             list_to_set(TypeChains, DeclaredChains),
             exclude(type_chain_too_short(InputArity), DeclaredChains, LongEnoughChains),
             Arity is InputArity + 1,
             ( arity(Fun, Arity)
               -> exclude(type_chain_too_long(InputArity), LongEnoughChains, UniqueTypeChains)
                ; UniqueTypeChains = LongEnoughChains ),
             ( UniqueTypeChains \= []
               -> ( incomplete_application_kind(Fun, Arity, ApplicationKind), ApplicationKind == overapplied
                    -> split_args_at_edit(T, PreGs, PreVals, RestArgs, ArgEdited),
                       ( ( HeadEdited == true ; ArgEdited == true )
                         -> stretch_applied(HV, PreVals, RestArgs, StretchGs, Out),
                            append([GsH, PreGs, StretchGs], Goals)
                          ; append(GsH, [throw_function_overapplication(Fun, InputArity)], Goals) )
                     ; typed_functioncall(Fun, UniqueTypeChains, T, HeadEdited, GsH, IsPartial, Bound, HeadEvidence, Out, Goal, Evidence),
                       Goals = [Goal] )
                ; HeadEdited == true
                  -> stretch_applied(HV, [], T, StretchGs, Out),
                     append(GsH, StretchGs, Goals)
                ; split_args_at_edit(T, PreGs, PreVals, RestArgs, ArgEdited),
                  ( ArgEdited == true
                    -> stretch_applied(HV, PreVals, RestArgs, StretchGs, Out),
                       append([GsH, PreGs, StretchGs], Goals)
                     ; ( IsPartial == true -> append(Bound, PreVals, AllAVs) ; AllAVs = PreVals ),
                       append(GsH, PreGs, Inner),
                       build_call_or_partial(Fun, AllAVs, Out, Inner, [], Goals) ) )
        ; HeadEdited == true, is_list(T) ->
            stretch_applied(HV, [], T, StretchGs, Out),
            append(GsH, StretchGs, Goals)
        ; split_args_at_edit(T, PreGs, PreVals, RestArgs, ArgEdited),
          ( ArgEdited == true
            -> stretch_applied(HV, PreVals, RestArgs, StretchGs, Out),
               append([GsH, PreGs, StretchGs], Goals)
             ; append(GsH, PreGs, Inner),
               %Literals (numbers, strings, etc.), known non-function atom => data:
               ( ( atomic(HV), \+ atom(HV) ; atom(HV), \+ fun(HV) ) -> note_translation_use(HV, data),
                                                                       Out = [HV|PreVals],
                                                                       Goals = Inner
               %The head is already translated; re-evaluation would run quoted data.
               ; is_list(HV) -> Out = [HV|PreVals], Goals = Inner
               %Unknown head (var/compound) => runtime dispatch:
               ; append(Inner, [reduce([HV|PreVals], Out)], Goals), note_edit ) ) ),
        %Other expressions conservatively recheck captured values.
        ( var(Evidence) -> Evidence = none ; true ).

%Generate actual function call or partial if arity not complete:
build_call_or_partial(Fun, AVs, Out, Inner, Extra, Goals) :- length(AVs, N),
                                                             Arity is N + 1,
                                                             ( arity(Fun, Arity)
                                                               -> resolve_memoization(Fun, AVs, Out, Goal),
                                                                  append(Inner, [Goal|Extra], Goals)
                                                                ; incomplete_application_kind(Fun, Arity, partial)
                                                               -> Out = partial(Fun, AVs),
                                                                  append(Inner, Extra, Goals)
                                                                ; append(Inner, [throw_function_overapplication(Fun, N)], Goals)
                                                             ).

%A declaration with fewer inputs than the call has arguments does not describe that call:
type_chain_too_short(N, TypeChain) :- is_list(TypeChain), TypeChain = [Arrow|Xs], Arrow == (->),
                                      length(Xs, L), L =< N.

%A declaration with more inputs than a complete call has arguments does not describe that call:
type_chain_too_long(N, TypeChain) :- is_list(TypeChain), TypeChain = [Arrow|Xs], Arrow == (->),
                                     length(Xs, L), L > N + 1.

%A typed call runs its body once for each tuple of argument values: the declarations
%decide whether it runs and which results it keeps, but never multiply them.
%Only a complete, non-partial call with one ground declaration keeps the direct translation:
typed_functioncall(Fun, [TypeChain], T, Live0, GsH, false, _, _, Out, Goal, _) :-
    ground(TypeChain), length(T, NA), Arity is NA + 1, arity(Fun, Arity), !,
    typed_functioncall_branch(Fun, TypeChain, T, Live0, GsH, Out, Goal).
%Otherwise each argument is evaluated once and checked at that point, carrying the
%surviving declarations and type-variable bindings forward to the call and output check:
typed_functioncall(Fun, TypeChains, T, Live0, GsH, IsPartial, Bound, TypeEvidence, Out, Goal, Evidence) :-
    maplist(initial_type_chain, TypeChains, Chains0),
    ( ground(TypeChains) -> GroundChains = true ; GroundChains = false ),
    length(Bound, NB), length(T, NA), Arity is NB + NA + 1,
    ( arity(Fun, Arity) -> Complete = true ; Complete = false ),
    maplist(drop_arg_specs(NB), Chains0, RemainingChains),
    ( TypeEvidence = evidence(Partial, EvidenceChains, Seen1), Partial == partial(Fun, Bound)
      -> CapturedGoals = [evidence_chains_for_call(RemainingChains, EvidenceChains, CapturedChains)]
       ; captured_type_checks(Bound, GroundChains, Chains0, [], Seen1, CapturedChains, CapturedGoals) ),
    translate_args_chain(T, Live0, 0, GroundChains, RemainingChains, CapturedChains, Seen1, SeenFinal, GsT, AVs0, FinalChains),
    ( IsPartial -> append(Bound, AVs0, AVs) ; AVs = AVs0 ),
    append(GsH, CapturedGoals, HeadGoals), append(HeadGoals, GsT, Inner),
    ( Complete == false -> Extra = []
     ; forall(member(chain(_, OutSpec), Chains0), unchecked_spec(OutSpec))
       -> Extra = []
        ; Extra = [output_chains_accept(Out, SeenFinal, FinalChains)] ),
    build_call_or_partial(Fun, AVs, Out, Inner, Extra, GoalsList),
    goals_list_to_conj(GoalsList, Goal),
    ( Complete == false
      -> Evidence = evidence(Out, FinalChains, SeenFinal)
       ; true ).

initial_type_chain([->|Xs], chain(ArgSpecs, OutSpec)) :-
    append(ArgTypes, [OutType], Xs),
    maplist(type_spec, ArgTypes, ArgSpecs),
    type_spec(OutType, OutSpec).

drop_arg_specs(N, chain(ArgSpecs, OutSpec), chain(Rest, OutSpec)) :-
    length(Captured, N), append(Captured, Rest, ArgSpecs).

evidence_chains_for_call(RemainingChains, EvidenceChains, CapturedChains) :-
    maplist(chain_remaining_arity, RemainingChains, Arities0),
    sort(Arities0, Arities),
    include(evidence_remaining_arity(Arities), EvidenceChains, CapturedChains),
    CapturedChains = [_|_].

chain_remaining_arity(chain(Specs, _), N) :- length(Specs, N).
evidence_remaining_arity(Arities, Chain) :- chain_remaining_arity(Chain, N), memberchk(N, Arities).

%Captured expressions were evaluated when the closure was created. At completion,
%recheck their values to restore declaration correlations before checking new args.
captured_type_checks([], _, Chains, Seen, Seen, Chains, []).
captured_type_checks([AV|AVs], GroundChains, InChains, Seen0, SeenFinal, OutChains, [StepGoal|Goals]) :-
    ( Seen0 == [] -> Seen1 = AV ; Seen1 = [AV|Seen0] ),
    ( GroundChains == true
      -> StepGoal = step_ground_type_chains(AV, Seen1, InChains, NextChains)
       ; StepGoal = step_type_chains(AV, Seen1, InChains, NextChains) ),
    captured_type_checks(AVs, GroundChains, NextChains, Seen1, SeenFinal, OutChains, Goals).

type_spec(T, atom) :- T == 'Atom', !.
type_spec(T, unchecked) :- ( T == '%Undefined%' ; T == '_' ), !.
type_spec(T, checked(T)).

unchecked_spec(atom).
unchecked_spec(unchecked).

%Each argument is evaluated once and steps the surviving declaration chains in place;
%arguments after one that may edit are stretched while keeping earlier type evidence:
translate_args_chain([], _, _, _, _, Chains, Seen, Seen, [], [], Chains).
translate_args_chain([A|As], Live, I, GroundChains, Chains0, InChains, Seen0, SeenFinal, Gs, [AV|AVs], OutChains) :-
    ( forall(member(chain(ArgSpecs, _), Chains0), ( nth0(I, ArgSpecs, Spec), Spec == atom ))
      -> AV = A, GsA = [], AEdited = false
       ; counting(translate_expr(A, GsA0, AV0), AEdited),
         maybe_stretch(Live, A, GsA0, AV0, _, GsA, AV, _) ),
    either_true(Live, AEdited, Live1),
    ( Seen0 == [] -> Seen1 = AV ; Seen1 = [AV|Seen0] ),
    ( GroundChains == true
      -> StepGoal = step_ground_type_chains(AV, Seen1, InChains, NextChains)
       ; StepGoal = step_type_chains(AV, Seen1, InChains, NextChains) ),
    I1 is I + 1,
    translate_args_chain(As, Live1, I1, GroundChains, Chains0, NextChains, Seen1, SeenFinal, GsRest, AVs, OutChains),
    append(GsA, [StepGoal|GsRest], Gs).

step_ground_type_chains(AV, SeenAVs, Chains, NextChains) :-
    ground(SeenAVs), !,
    filter_ground_chains(Chains, AV, NextChains),
    NextChains = [_|_].
step_ground_type_chains(AV, SeenAVs, Chains, NextChains) :-
    step_open_type_chains(AV, SeenAVs, Chains, NextChains).

step_type_chains(AV, SeenAVs, Chains, NextChains) :-
    ground(SeenAVs), ground(Chains), !,
    filter_ground_chains(Chains, AV, NextChains),
    NextChains = [_|_].
step_type_chains(AV, SeenAVs, Chains, NextChains) :-
    ground(SeenAVs), !,
    findall(chain(Specs, OutSpec),
            ( member(chain([Spec|Specs], OutSpec), Chains),
              value_type_matches(AV, Spec) ),
            NextChains0),
    NextChains0 = [_|_],
    unique_chains(SeenAVs, NextChains0, NextChains).
step_type_chains(AV, SeenAVs, Chains, NextChains) :-
    step_open_type_chains(AV, SeenAVs, Chains, NextChains).

step_open_type_chains(AV, SeenAVs, Chains, NextChains) :-
    findall(SeenAVs-chain(Specs, OutSpec),
            ( member(chain([Spec|Specs], OutSpec), Chains),
              value_type_matches(AV, Spec) ),
            Pairs),
    group_arg_chains(Pairs, SeenAVs, NextChains0),
    unique_chains(SeenAVs, NextChains0, NextChains).

filter_ground_chains([], _, []).
filter_ground_chains([chain([Spec|Specs], OutSpec)|Chains], AV, Next) :-
    ( value_type_matches(AV, Spec)
      -> Next = [chain(Specs, OutSpec)|Rest]
       ; Next = Rest ),
    filter_ground_chains(Chains, AV, Rest).

group_arg_chains([AV-Chain], AV, [Chain]) :- !.
group_arg_chains(Pairs, AV, Chains) :-
    Pairs = [_|_],
    key_arg_pairs(Pairs, 0, Keyed),
    ordered_arg_groups(Keyed, Groups),
    member(_-Group, Groups),
    bind_arg_chains(Group, AV, Chains).

% Hash only the keys; retain the original payloads and restore first-seen
% order after grouping. Exact variant checks separate any hash collisions.
key_arg_pairs([], _, []).
key_arg_pairs([AV-Chain|Pairs], I, [Hash-(I-(AV-Chain))|Keyed]) :-
    variant_key_hash(AV, Hash), J is I+1,
    key_arg_pairs(Pairs, J, Keyed).

ordered_arg_groups(Keyed, Groups) :-
    keysort(Keyed, Sorted), group_pairs_by_key(Sorted, Buckets),
    maplist(arg_bucket_groups, Buckets, GroupLists), append(GroupLists, Unordered),
    keysort(Unordered, Groups).

arg_bucket_groups(_-[], []) :- !.
arg_bucket_groups(Hash-[I-(AV-Chain)|Pairs], [I-[AV-Chain|Same]|Groups]) :-
    partition(same_arg_variant(AV), Pairs, Matches, Rest),
    pairs_values(Matches, Same),
    arg_bucket_groups(Hash-Rest, Groups).

same_arg_variant(AV, _-(Other-_)) :- AV =@= Other.

bind_arg_chains([], _, []).
bind_arg_chains([AV-Chain|Pairs], AV, [Chain|Chains]) :-
    bind_arg_chains(Pairs, AV, Chains).

variant_key_hash(Key, Hash) :-
    ( acyclic_term(Key)
      -> variant_hash(Key, Hash)
       ; term_factorized(Key, Skeleton, Substitution),
         variant_hash(Skeleton+Substitution, Hash) ).

unique_chains(_, [], []) :- !.
unique_chains(_, [C], [C]) :- !.
unique_chains(Context, Chains, Unique) :-
    empty_nb_set(Seen),
    keep_unique_chains(Chains, Context, Seen, Unique).

keep_unique_chains([], _, _, []).
keep_unique_chains([C|Cs], Context, Seen, Unique) :-
    add_nb_set(Context-C, Seen, New),
    ( New == true -> Unique = [C|Rest] ; Unique = Rest ),
    keep_unique_chains(Cs, Context, Seen, Rest).

output_chains_accept(Out, SeenAVs, Chains) :-
    ( ground(Out), ground(SeenAVs)
      -> ( member(chain(_, OutSpec), Chains),
           value_type_matches(Out, OutSpec) -> true )
       ; OutAVs = Out-SeenAVs,
         findall(OutAVs,
                 ( member(chain(_, OutSpec), Chains),
                   value_type_matches(Out, OutSpec) ),
                 OutAVs0),
         unique_chains([], OutAVs0, UniqueOutAVs),
         member(OutAVs, UniqueOutAVs) ).

value_type_matches(_, atom) :- !.
value_type_matches(_, unchecked) :- !.
value_type_matches(V, checked(T)) :-
    ( ground(V), ground(T)
      -> ('get-type'(V, T) -> true ; 'get-metatype'(V, T))
       ; ('get-type'(V, T) *-> true ; 'get-metatype'(V, T)) ).

ground_type_check(V, T, (ground(V) -> ('get-type'(V, T) -> true ; 'get-metatype'(V, T))
                                    ; unique_type_match(V, T))).

unique_type_match(V, T) :-
    findall(V, ('get-type'(V, T) *-> true ; 'get-metatype'(V, T)), Vs0),
    unique_chains([], Vs0, Vs),
    member(V, Vs).

%Type function call generation, returns function call plus typechecks for input and output:
typed_functioncall_branch(Fun, TypeChain, T, Live0, GsH, Out, BranchGoal) :-
    TypeChain = [->|Xs],
    append(ArgTypes, [OutType], Xs),
    translate_args_by_type(T, ArgTypes, Live0, GsT2, AVsTmp),
    append(GsH, GsT2, InnerTmp),
    ( (OutType == '%Undefined%' ; OutType == '_' ; OutType == 'Atom')
       -> Extra = []
        ; ground_type_check(Out, OutType, OutCheck), Extra = [OutCheck] ),
    build_call_or_partial(Fun, AVsTmp, Out, InnerTmp, Extra, GoalsList),
    goals_list_to_conj(GoalsList, BranchGoal).


%Selectively apply translate_args for non-Atom args while Atom args stay as data input:
translate_args_by_type(As, Ts, GsOut, AVs) :- translate_args_by_type(As, Ts, false, GsOut, AVs).
translate_args_by_type([], _, _, [], []) :- !.
translate_args_by_type([A|As], [T|Ts], Live, GsOut, [AV|AVs]) :-
    ( T == 'Atom' -> AV = A, GsA = [], AEdited = false
                   ; counting(translate_expr(A, GsA0, AV0), AEdited),
                     maybe_stretch(Live, A, GsA0, AV0, _, GsA1, AV, _),
                     ( (T == '%Undefined%' ; T == '_')
                       -> GsA = GsA1
                        ; ground(T)
                       -> ground_type_check(AV, T, ArgCheck),
                          append(GsA1, [ArgCheck], GsA)
                        ; append(GsA1, [('get-type'(AV, T) *-> true ; 'get-metatype'(AV, T))], GsA) ) ),
    either_true(Live, AEdited, Live1),
    translate_args_by_type(As, Ts, Live1, GsRest, AVs),
    append(GsA, GsRest, GsOut).

%Convert let* to recusrive let:
letstar_to_rec_let([[Pat,Val]],Body,[let,Pat,Val,Body]).
letstar_to_rec_let([[Pat,Val]|Rest],Body,[let,Pat,Val,Out]) :- letstar_to_rec_let(Rest,Body,Out).

%Patterns: variables, atoms, numbers, lists:
translate_pattern(X, X) :- var(X), !.
translate_pattern(X, X) :- atomic(X), !.
translate_pattern([H|T], [P|Ps]) :- !, translate_pattern(H, P),
                                       translate_pattern(T, Ps).

% Connect a branch's result only when it runs. Val may also occur in sibling
% branches or the caller, so aliasing it with Out here can constrain them.
build_branch(true, Val, Out, (Out = Val)) :- !.
build_branch(Con, Val, Out, (Val = Out, Con)).

%Translate case expression recursively into nested if:
translate_case([[K,VExpr]|Rs], KE, Kv, Out, Goal, KGo) :- counting(translate_expr(VExpr, GV, VOut0), VE),
                                                          either_true(KE, VE, Live),
                                                          maybe_stretch_conj(Live, VExpr, GV, VOut0, ConV, VOut),
                                                          constrain_args(K, Kc, Gc),
                                                          build_branch(ConV, VOut, Out, Then),
                                                          ( Rs == [] -> Goal = ((Kv = Kc) -> Then), KGi=[]
                                                                      ; translate_case(Rs, KE, Kv, Out, Next, KGi),
                                                                        Goal = ((Kv = Kc) -> Then ; Next) ),
                                                          append([Gc,KGi], KGo).

%Translate arguments recursively:
translate_args([], [], []).
translate_args([X|Xs], Goals, [V|Vs]) :- translate_expr(X, G1, V),
                                         translate_args(Xs, G2, Vs),
                                         append(G1, G2, Goals).

translate_progn([X], Goals, Out, Evidence) :- !, translate_expr(X, Goals, Out, Evidence).
translate_progn([X|Xs], Goals, Out, Evidence) :- counting(translate_expr(X, G1, _), XEdits),
                                                 counting(translate_progn(Xs, G20, Out0, Ev0), RestEdits),
                                                 either_true(XEdits, RestEdits, Live),
                                                 maybe_stretch(Live, [progn|Xs], G20, Out0, Ev0, G2, Out, Evidence),
                                                 append(G1, G2, Goals).

%Build A ; B ; C ... from a proper list into a fresh output goal:
disj_list([], fail).
disj_list([G], G) :- !.
disj_list([G|Gs], (G ; R)) :- disj_list(Gs, R).

%Build one disjunct per branch: (Conj, Out = Val).
%A branch after one that may edit is decided when reached:
build_superpose_branches(Es, Out, Bs) :- build_superpose_branches(Es, false, Out, Bs).
build_superpose_branches([], _, _, []).
build_superpose_branches([E|Es], PriorEdited, Out, [B|Bs]) :-
    counting(translate_expr(E, Gs, Val), EEdits),
    maybe_stretch_conj(PriorEdited, E, Gs, Val, Conj, V),
    build_branch(Conj, V, Out, B),
    either_true(PriorEdited, EEdits, NextEdited),
    build_superpose_branches(Es, NextEdited, Out, Bs).

%Build hyperpose branch as a goal list for concurrent_maplist to consume:
build_hyperpose_branches([], []).
build_hyperpose_branches([E|Es], [(Goal, Res)|Bs]) :- translate_expr_to_conj(E, Goal, Res),
                                                      build_hyperpose_branches(Es, Bs).

%Runtime hyperpose path for variable/computed list arguments.
hyperpose_runtime(Exprs, Out) :- is_list(Exprs),
                                 concurrent_and(member(Expr, Exprs), eval(Expr, Out)).

%Like membercheck but with direct equality rather than unification
memberchk_eq(V, [H|_]) :- V == H, !.
memberchk_eq(V, [_|T]) :- memberchk_eq(V, T).

%Generate a readable name, with a shared counter for lambdas compiled in workers:
next_lambda_name(Name) :- flag(lambda_counter, Prev, Prev + 1),
                          N is Prev + 1,
                          format(atom(Candidate), 'lambda_~d', [N]),
                          ( ( fun(Candidate) ; current_predicate(Candidate/_) )
                            -> next_lambda_name(Name)
                            ; Name = Candidate ).

% Select a declaration by name and source arity without binding wildcard rows.
declared_output_type(F, Arity, OutType) :-
    atom(F), nonvar(OutType), current_predicate('&self'/3),
    clause('&self'(':', F, _), true, Ref),
    % The indexed lookup may bind a wildcard; inspect the original row by ref.
    clause('&self'(Colon, Target, Type), true, Ref),
    Colon == (:), Target == F, is_list(Type), Type = [Arrow|Types], Arrow == (->),
    TypeCount is Arity + 1, length(Types, TypeCount),
    last(Types, DeclaredOut), DeclaredOut == OutType.

%The key of a case with an Empty case runs once, and Empty only if the key yields no value. Soft-cut does exactly
%this, but would make a cut inside the key local to it; so a key containing a cut instead records in a fresh
%non-backtrackable flag whether it yielded a value, and its cut still commits the clause:
case_with_empty(GkConj, CaseGoal, DefaultThen, ( GkConj *-> CaseGoal ; DefaultThen )) :- \+ ( sub_term(G, GkConj), G == ! ), !.
case_with_empty(GkConj, CaseGoal, DefaultThen, ( functor(Seen, seen, 1),
                                                 ( GkConj, nb_setarg(1, Seen, true), CaseGoal
                                                 ; arg(1, Seen, S), var(S), DefaultThen ) )).
