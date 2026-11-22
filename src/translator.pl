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
                                        note_symbol_head(F),
                                        fun(F), !,
                                        translate_expr([F|Args], GoalsExpr, Var),
                                        flatten(GoalsExpr, Goals).
constrain_args(In, Out, Goals) :- ( In = [F|_], atom(F) -> note_symbol_head(F) ; true ),
                                  maplist(constrain_args, In, Out, NestedGoalsList),
                                  flatten(NestedGoalsList, Goals), !.

%Flatten (= Head Body) MeTTa function into Prolog Clause:
translate_clause(Input, Clause) :- translate_clause(Input, Clause, true).
translate_clause(Input, Clause, ConstrainArgs) :- translate_clause(Input, Clause, ConstrainArgs, auto).
translate_clause(Input, Clause, ConstrainArgs, Pos) :-
    Input = [=, [F|_], _],
    ( Pos == first -> Later = false ; Pos == later -> Later = true ; translated_from(_, [=, [F|_], _]) -> Later = true ; Later = false ),
    ( Later == true, may_edit(F) -> Kind = transient, StretchBody = true ; Kind = entry(EntryRev, Used), StretchBody = false ),
    in_unit(Kind, translate_equation(Input, Clause0, ConstrainArgs, StretchBody), Edits),
    ( Edits > 0, \+ may_edit(F) -> assertz(may_edit(F)) ; true ),
    ( Used == true -> prepend_entry_rev(Clause0, EntryRev, Clause) ; Clause = Clause0 ).

prepend_entry_rev((Head :- true), Rev, (Head :- interface_is(Rev))) :- !.
prepend_entry_rev((Head :- Body), Rev, (Head :- interface_is(Rev), Body)).

translate_equation(Input, (Head :- BodyConj), ConstrainArgs, StretchBody) :-
                                               Input = [=, [F|Args0], BodyExpr],
                                               ( ConstrainArgs -> maplist(constrain_args, Args0, Args1, GoalsA),
                                                                  flatten(GoalsA,GoalsPrefix)
                                                                ; Args1 = Args0, GoalsPrefix = [] ),
                                               ( declared_output_type(F, 'Atom')
                                                 -> GoalsBody = [],
                                                    ExpOut = BodyExpr
                                                  ; translate_expr(BodyExpr, Gs0, Out0),
                                                    ( StretchBody == true -> stretch(BodyExpr, Gs0, Out0, GoalsBody, ExpOut)
                                                                           ; GoalsBody = Gs0, ExpOut = Out0 ) ),
                                               (  nonvar(ExpOut) , ExpOut = partial(Base,Bound)
                                               -> arity(Base, Arity), length(Bound, N), M is (Arity - N) - 1,
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

%Track symbols each compiled clause depends on, so adding/removing definitions refreshes earlier users:
:- dynamic translated_from/2, used_symbol/2, may_edit/1.

note_symbol_head(HV) :- ( atom(HV), nb_current(petta_used_syms, Box), Box = syms(Old)
                          -> nb_setarg(1, Box, [HV|Old]) ; true ).

compile_clause_with_syms(Term, Pos, Clause, Syms) :-
    ( nb_current(petta_used_syms, Prev) -> true ; Prev = none ),
    Box = syms([]), b_setval(petta_used_syms, Box),
    copy_term(Term, Input), once(translate_clause(Input, Clause, true, Pos)),
    arg(1, Box, Raw), sort(Raw, Syms),
    b_setval(petta_used_syms, Prev).

assert_compiled_clause(Term, Clause, Syms, Ref) :-
    assertz(Clause, Ref), assertz(translated_from(Ref, Term)),
    forall(member(S, Syms), assertz(used_symbol(S, Ref))).

install_clause(Term, Clause, Ref) :-
    Term = [=, [F|_], _], ( may_edit(F) -> WasEditor = true ; WasEditor = false ),
    compile_clause_with_syms(Term, auto, Clause, Syms),
    assert_compiled_clause(Term, Clause, Syms, Ref),
    ( WasEditor == false, may_edit(F) -> bump_interface, refresh_symbol_users(F) ; true ).

refresh_symbol_users(F) :- refresh_symbol_users(F, []).
refresh_symbol_users(F, Path) :-
    findall(G, ( used_symbol(F, Ref), translated_from(Ref, [=, [G|_], _]) ), Raw),
    sort(Raw, Users),
    forall(member(G, Users), ( memberchk(G, Path) -> true ; recompile_symbol_user(G, [G|Path]) )).

recompile_symbol_user(G, Path) :-
    findall(Ref-Term, ( Term = [=, [G|_], _], translated_from(Ref, Term) ), Pairs),
    Pairs \= [], !,
    ( may_edit(G) -> WasEditor = true ; WasEditor = false ),
    recompile_clauses(Pairs, first, Compiled),
    forall(member(Ref-_, Pairs), ( erase(Ref), retractall(translated_from(Ref, _)), retractall(used_symbol(_, Ref)) )),
    forall(member(compiled(Term, Clause, Syms), Compiled), assert_compiled_clause(Term, Clause, Syms, _)),
    metta_on_function_changed(G),
    ( WasEditor == false, may_edit(G) -> refresh_symbol_users(G, Path) ; true ).
recompile_symbol_user(_, _).

recompile_clauses([], _, []).
recompile_clauses([_-Term|Rest], Pos, [compiled(Term, Clause, Syms)|Cs]) :-
    compile_clause_with_syms(Term, Pos, Clause, Syms),
    recompile_clauses(Rest, later, Cs).

%%% Deciding code when it is reached %%%
%Code reached after a program-changing edit is translated ahead as usual and guarded
%once by the interface revision; if it moved, the whole stretch is translated fresh.
bump_interface :- flag(petta_iface_rev, R, R + 1).
interface_is(Rev) :- flag(petta_iface_rev, Rev, Rev).
may_change_interface(Atom) :- ( var(Atom) -> true ; Atom = [E|_], ( var(E) ; E == (=) ; E == (:) ) ).
edits_world(F) :- ( may_edit(F) ; memberchk(F, ['import!', import_prolog_function, 'add-translator-rule!', 'remove-translator-rule!']) ), !.

in_unit(Kind, Goal, Edits) :-
    ( nb_current(petta_unit, Prev) -> true ; Prev = none ),
    Unit = u(Kind, 0), b_setval(petta_unit, Unit),
    call(Goal), arg(2, Unit, Edits),
    b_setval(petta_unit, Prev).

note_edit :- ( nb_current(petta_unit, U), U = u(_, N) -> N1 is N + 1, nb_setarg(2, U, N1) ; true ).
counting(Goal, Edited) :-
    ( nb_current(petta_unit, U), U = u(_, N0)
      -> call(Goal), arg(2, U, N1), ( N1 > N0 -> Edited = true ; Edited = false )
       ; call(Goal), Edited = false ).

note_eval(Expr) :- ( var(Expr) -> note_edit ; compound(Expr), text_edits(Expr) -> note_edit ; true ).
text_edits([H|T]) :-
    ( var(H) -> true ; H == quote -> fail
    ; atom(H) -> ( note_symbol_head(H), fail ; text_edit_head(H, T) -> true ; member(A, T), compound(A), text_edits(A), ! )
    ; member(A, [H|T]), compound(A), text_edits(A), ! ).
text_edit_head('add-atom', [_, Atom]) :- !, may_change_interface(Atom).
text_edit_head('remove-atom', [_, Atom]) :- !, may_change_interface(Atom).
text_edit_head(eval, [E]) :- !, ( var(E) -> true ; compound(E), text_edits(E) ).
text_edit_head(H, _) :- edits_world(H).

translate_transient(Expr, Goals, Out) :- in_unit(transient, translate_expr(Expr, Goals, Out), _).

stretch_check(interface_is(Rev)) :-
    ( nb_current(petta_unit, u(entry(Rev, Used), _)) -> Used = true
    ; interface_is(Rev) ).

stretch(Source, Gs, Fast, Gs, Fast) :- ( var(Source) ; atomic(Source) ; Source = [Q, _], Q == quote ), !.
stretch(Source, Gs, Fast, [( Check -> Ahead ; late_call(Template, Vs, Out) )], Out) :-
    term_variables(Source, Vs), copy_term_nat(Vs-Source, Template), numbervars(Template, 0, _),
    goals_list_to_conj(Gs, Conj), stretch_check(Check),
    ( var(Fast), \+ memberchk_eq(Fast, Vs) -> Out = Fast, Ahead = Conj ; Ahead = (Out = Fast, Conj) ).
stretch_conj(Source, Gs, Fast, Conj, Out) :- stretch(Source, Gs, Fast, Goals, Out), goals_list_to_conj(Goals, Conj).

maybe_stretch(true, Expr, Gs0, Out0, Gs, Out) :- !, stretch(Expr, Gs0, Out0, Gs, Out).
maybe_stretch(false, _, Gs, Out, Gs, Out).
maybe_stretch_conj(true, Expr, Gs, Fast, Conj, Out) :- !, stretch_conj(Expr, Gs, Fast, Conj, Out).
maybe_stretch_conj(false, _, Gs, Out, Conj, Out) :- goals_list_to_conj(Gs, Conj).
either_true(false, false, false) :- !.
either_true(_, _, true).

live_conj(Prior, Body, Conj, Out) :-
    counting(translate_expr(Body, Gs, Fast), BodyEdits),
    either_true(Prior, BodyEdits, Live),
    maybe_stretch_conj(Live, Body, Gs, Fast, Conj, Out).

late_call(Template, Vars, Out) :-
    varnumbers(Template, TemplateVars-Source),
    translate_transient(Source, Goals, Value),
    TemplateVars = Vars, Out = Value,
    call_goals(Goals).

split_args_at_edit([], [], [], [], false).
split_args_at_edit([A|As], Gs, [V|Vs], Rest, Edited) :-
    counting(translate_expr(A, GsA, V), AEdited),
    ( AEdited == true -> Gs = GsA, Vs = [], Rest = As, Edited = true
                       ; split_args_at_edit(As, GsRest, Vs, Rest, Edited), append(GsA, GsRest, Gs) ).

stretch_applied(Head, PreVals, Rest, StretchGs, Out) :-
    length(PreVals, K), length(PrefixVars, K),
    append(PrefixVars, Rest, ResidualArgs),
    ( ( atom(Head) ; nonvar(Head), Head = partial(_, _) )
      -> Residual = [Head|ResidualArgs], BindHead = true
       ; Residual = [HeadVar|ResidualArgs], BindHead = (HeadVar = Head) ),
    translate_expr(Residual, FastGs, FastOut),
    stretch(Residual, FastGs, FastOut, StretchGs, Out),
    call(BindHead), PrefixVars = PreVals.

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
                            ( current_predicate(F/Arity) , \+ (current_op(_, _, F), Arity =< 2)
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
translate_expr_to_conj(Input, Conj, Out) :- translate_expr(Input, Goals, Out),
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
translate_expr(X, [], X)          :- ((var(X) ; atomic(X)) ; X = partial(_,_)), !.
translate_expr([H0|T0], Goals, Out) :-
        safe_rewrite_streamops([H0|T0],[H|T]),
        ( atom(H) -> GsH = [], HV = H, HeadEdited = false
                   ; counting(translate_expr(H, GsH, HV), HeadEdited) ),
        %--- Translator rules ---:
        ( nonvar(HV), translator_rule(HV) -> note_symbol_head(HV),
                                             ( catch(match('&self', [':', HV, TypeChain], TypeChain, TypeChain), _, fail)
                                               -> TypeChain = [->|Xs],
                                                  append(ArgTypes, [_], Xs),
                                                  translate_args_by_type(T, ArgTypes, GsT, T1)
                                                ; translate_args(T, GsT, T1) ),
                                             append(T1,[Gs],Args),
                                             HookCall =.. [HV|Args],
                                             call(HookCall),
                                             translate_expr(Gs, GsE, Out),
                                             append([GsH,GsT,GsE],Goals)
        %--- Non-determinism ---:
        ; HV == superpose, T = [Args], is_list(Args) -> build_superpose_branches(Args, Out, Branches),
                                                        disj_list(Branches, Disj),
                                                        append(GsH, [Disj], Goals)
        ; HV == collapse, T = [E] -> translate_expr_to_conj(E, Conj, EV),
                                     append(GsH, [findall(EV, Conj, Out)], Goals)
        ; HV == cut, T = [] -> append(GsH, [(!)], Goals),
                               Out = true
        ; HV == test, T = [Expr, Expected] -> counting(translate_expr_to_conj(Expr, Conj, Val), EE),
                                              counting(translate_expr(Expected, GsE0, ExpVal0), XE),
                                              either_true(EE, XE, ELive),
                                              maybe_stretch(ELive, Expected, GsE0, ExpVal0, GsE, ExpVal),
                                              Goal1 = ( findall(Val, Conj, Results),
                                                        (Results = [Actual] -> true
                                                                             ; Actual = Results ) ),
                                              append(GsH, [Goal1], G1),
                                              append(G1, GsE, G2),
                                              append(G2, [test(Actual, ExpVal, Out)], Goals)
        ; HV == once, T = [X] -> translate_expr_to_conj(X, Conj, Out),
                                 append(GsH, [once(Conj)], Goals)
        ; HV == hyperpose, T = [L]
          -> ( nonvar(L), is_list(L)
               -> build_hyperpose_branches(L, Branches),
                  append(GsH, [concurrent_and(member((Goal,Res), Branches), (call(Goal), Out = Res))], Goals)
               ; translate_expr(L, GsL, LV),
                 append(GsH, GsL, Inner),
                 append(Inner, [hyperpose_runtime(LV, Out)], Goals),
                 note_edit )
        ; HV == with_mutex, T = [M,X] -> translate_expr_to_conj(X, Conj, Out),
                                         append(GsH, [with_mutex(M,Conj)], Goals)
        ; HV == transaction, T = [X] -> translate_expr_to_conj(X, Conj, Out),
                                        append(GsH, [transaction(Conj)], Goals)
        %--- Sequential execution ---:
        ; HV == progn, T = Exprs -> translate_progn(Exprs, GsList, Out),
                                    append(GsH, GsList, Goals)
        ; HV == prog1, T = [First|Rest] -> counting(translate_expr(First, GsF, Out), FEdits),
                                           ( Rest == [] -> GsRest = []
                                           ; counting(translate_progn(Rest, GsR0, ROut0), REdits),
                                             either_true(FEdits, REdits, RLive),
                                             maybe_stretch(RLive, [progn|Rest], GsR0, ROut0, GsRest, _) ),
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
                                                           counting(translate_expr(In, Gi0, Out0), InEdits),
                                                           either_true(PatEdits, ValEdits, L0), either_true(L0, InEdits, Live),
                                                           maybe_stretch(Live, In, Gi0, Out0, Gi, Out),
                                                           append([GsH,[(Pv=V)],Gp,Gv,Gi], Goals)
        ; HV == 'let*', T = [Binds, Body] -> letstar_to_rec_let(Binds,Body,RecLet),
                                             translate_expr(RecLet,  Goals, Out)
        ; HV == sealed, T = [Vars, Expr] -> translate_expr_to_conj(Expr, Con, Val),
                                            Goals = [copy_term(Vars,[Con,Val],_,[Ncon,Out]),Ncon]
        %--- Iterating over non-deterministic generators without reification ---:
        ; HV == 'forall', T = [GF, TF]
          -> ( is_list(GF) -> GF = [GFH|GFA],
                              translate_expr(GFH, GsGFH, GFHV),
                              translate_args(GFA, GsGFA, GFAv),
                              append(GsGFH, GsGFA, GsGF),
                              GenList = [GFHV|GFAv]
                            ; translate_expr(GF, GsGF, GFHV),
                              GenList = [GFHV] ),
             translate_expr(TF, GsTF, TFHV),
             TestList = [TFHV, V],
             goals_list_to_conj(GsGF, GPre),
             GenGoal = (GPre, reduce(GenList, V)),
             append(GsH, GsTF, Tmp0),
             append(Tmp0, [( forall(GenGoal, ( reduce(TestList, Truth), Truth == true )) -> Out = true ; Out = false )], Goals),
             note_edit
        ; HV == 'foldall', T = [AF, GF, InitS]
          -> translate_expr_to_conj(InitS, ConjInit, Init),
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
                              GenList = [GFHV] ),
             append(GsH, GsAF, Tmp1),
             append(Tmp1, GsGF, Tmp2),
             append(Tmp2, [ConjInit, foldall(agg_reduce(AFV, V), reduce(GenList, V), Init, Out)], Goals),
             note_edit
        %--- Higher-order functions with pseudo-lambdas and lambdas ---:
        ; HV == 'foldl-atom', T = [List, Init, AccVar, XVar, Body]
          -> counting(translate_expr_to_conj(List, ConjList, L), LE),
             counting(translate_expr_to_conj(Init, ConjInit, InitV), IE),
             either_true(LE, IE, PreE),
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
                                           install_clause([=, [F|FullArgs], Body], Clause, _),
                                           %translate_clause records arities; keep the function marker idempotent.
                                           ( fun(F) -> true ; assertz(fun(F)) ),
                                           format(atom(Label), "metta lambda (~w)", [F]),
                                           maybe_print_compiled_clause(Label, ['|->', Args, Body], Clause),
                                           length(FullArgs, N),
                                           Arity is N + 1,
                                           (arity(F, Arity) -> true ; assertz(arity(F, Arity))),
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
                                                     counting(translate_expr(Body, GsB0, Out0), BodyEdits),
                                                     either_true(SE, BodyEdits, Live),
                                                     maybe_stretch(Live, Body, GsB0, Out0, GsB, Out),
                                                     append(G1, [match(S, Pattern, Out, Out)], G2),
                                                     append(G2, GsB, Goals)
        %--- Predicate to compiled goal ---:
        ; HV == translatePredicate, T = [Expr] -> Expr = [S|Args],
                                                  translate_args(Args, GsArgs, ArgsOut),
                                                  Goal =.. [S|ArgsOut],
                                                  append(GsH, GsArgs, Inner),
                                                  append(Inner, [Goal], Goals)
        %--- Manual dispatch options: ---
        %Generate a predicate call on compilation, translating Args for nesting:
        ; HV == call,  T = [Expr] -> Expr = [F|Args],
                                     ( atom(F) -> note_symbol_head(F), ( edits_world(F) -> note_edit ; true ) ; note_edit ),
                                     translate_args(Args, GsArgs, ArgsOut),
                                     append(GsH, GsArgs, Inner),
                                     append(ArgsOut, [Out], CallArgs),
                                     Goal =.. [F|CallArgs],
                                     append(Inner, [Goal], Goals)
        %Produce a dynamic dispatch, translating Args for nesting:
        ; HV == reduce, T = [Expr] -> ( var(Expr) -> translate_expr(Expr, GsH, ExprOut),
                                                     Goals = [reduce(ExprOut, Out)|GsH], note_edit
                                                   ; Expr = [F|Args],
                                                     ( atom(F) -> note_symbol_head(F), ( edits_world(F) -> note_edit ; true ) ; note_edit ),
                                                     translate_args(Args, GsArgs, ArgsOut),
                                                     append(GsH, GsArgs, Inner),
                                                     ExprOut = [F|ArgsOut],
                                                     append(Inner, [reduce(ExprOut, Out)], Goals) )
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
          translate_expr(Expr, GsExpr, ExprOut),
          append(GsH, [], Inner),
          goals_list_to_conj(GsExpr, Conj),
          Goal = catch((Conj, Out = ExprOut),
                       Exception,
                       (Exception = error(Type, Ctx) -> Out = ['Error', Type, Ctx]
                                                      ; Out = ['Error', Exception])),
          append(Inner, [Goal], Goals)
        %--- Automatic 'smart' dispatch, translator deciding when to create a predicate call, data list, or dynamic dispatch: ---
        ; HeadEdited == true, is_list(T) ->
            stretch_applied(HV, [], T, StretchGs, Out),
            append(GsH, StretchGs, Goals)
        ; is_list(T),
          ( atom(HV), fun(HV), Fun = HV, Bound = [], IsPartial = false
          ; compound(HV), HV = partial(Fun, Bound), IsPartial = true )
          -> note_symbol_head(Fun),
             ( edits_world(Fun) -> note_edit ; true ),
             findall(TypeChain, catch(match('&self', [':', Fun, TypeChain], TypeChain, TypeChain), _, fail), TypeChains),
             list_to_set(TypeChains, UniqueTypeChains),
             ( UniqueTypeChains \= []
               -> length(Bound, NB), length(T, NT), InputArity is NB + NT, Arity is InputArity + 1,
                  ( incomplete_application_kind(Fun, Arity, ApplicationKind), ApplicationKind == overapplied
                    -> split_args_at_edit(T, PreGs, PreVals, RestArgs, ArgEdited),
                       ( ArgEdited == true
                         -> stretch_applied(HV, PreVals, RestArgs, StretchGs, Out),
                            append([GsH, PreGs, StretchGs], Goals)
                          ; append(GsH, [throw_function_overapplication(Fun, InputArity)], Goals) )
                     ; maplist({Fun,T,GsH,IsPartial,Bound,Out}/[TypeChain,BranchGoal]>>(
                               typed_functioncall_branch(Fun, TypeChain, T, GsH, IsPartial, Bound, Out, BranchGoal)), UniqueTypeChains, Branches),
                       disj_list(Branches, Disj),
                       Goals = [Disj] )
                ; split_args_at_edit(T, PreGs, PreVals, RestArgs, ArgEdited),
                  ( ArgEdited == true
                    -> stretch_applied(HV, PreVals, RestArgs, StretchGs, Out),
                       append([GsH, PreGs, StretchGs], Goals)
                     ; ( IsPartial == true -> append(Bound, PreVals, AllAVs) ; AllAVs = PreVals ),
                       append(GsH, PreGs, Inner),
                       build_call_or_partial(Fun, AllAVs, Out, Inner, [], Goals) ) )
        ; split_args_at_edit(T, PreGs, PreVals, RestArgs, ArgEdited),
          ( ArgEdited == true
            -> stretch_applied(HV, PreVals, RestArgs, StretchGs, Out),
               append([GsH, PreGs, StretchGs], Goals)
             ; append(GsH, PreGs, Inner),
               %Literals (numbers, strings, etc.), known non-function atom => data:
               ( ( atomic(HV), \+ atom(HV) ; atom(HV), \+ fun(HV) ) -> note_symbol_head(HV),
                                                                       Out = [HV|PreVals],
                                                                       Goals = Inner
               %Plain data list: evaluate inner fun-sublists
               ; is_list(HV) -> eval_data_term(HV, Gd, HV1),
                                append(Inner, Gd, Goals),
                                Out = [HV1|PreVals]
               %Unknown head (var/compound) => runtime dispatch:
               ; append(Inner, [reduce([HV|PreVals], Out)], Goals), note_edit ) ) ).

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

%Type function call generation, returns function call plus typechecks for input and output:
typed_functioncall_branch(Fun, TypeChain, T, GsH, IsPartial, Bound, Out, BranchGoal) :-
    TypeChain = [->|Xs],
    append(ArgTypes, [OutType], Xs),
    translate_args_by_type(T, ArgTypes, GsT2, AVsTmp0),
    ( IsPartial -> append(Bound, AVsTmp0, AVsTmp) ; AVsTmp = AVsTmp0 ),
    append(GsH, GsT2, InnerTmp),
    ( (OutType == '%Undefined%' ; OutType == '_' ; OutType == 'Atom')
       -> Extra = [] ; Extra = [('get-type'(Out, OutType) *-> true ; 'get-metatype'(Out, OutType))] ),
    build_call_or_partial(Fun, AVsTmp, Out, InnerTmp, Extra, GoalsList),
    goals_list_to_conj(GoalsList, BranchGoal).


%Selectively apply translate_args for non-Expression args while Expression args stay as data input:
translate_args_by_type(As, Ts, GsOut, AVs) :- translate_args_by_type(As, Ts, false, GsOut, AVs).
translate_args_by_type([], _, _, [], []) :- !.
translate_args_by_type([A|As], [T|Ts], Live, GsOut, [AV|AVs]) :-
    ( T == 'Atom' -> AV = A, GsA = [], AEdited = false
                   ; counting(translate_expr(A, GsA0, AV0), AEdited),
                     maybe_stretch(Live, A, GsA0, AV0, GsA1, AV),
                     ( (T == '%Undefined%' ; T == '_')
                       -> GsA = GsA1
                        ; append(GsA1, [('get-type'(AV, T) *-> true ; 'get-metatype'(AV, T))], GsA) ) ),
    either_true(Live, AEdited, Live1),
    translate_args_by_type(As, Ts, Live1, GsRest, AVs),
    append(GsA, GsRest, GsOut).

%Handle data list:
eval_data_term(X, [], X) :- (var(X); atomic(X)), !.
eval_data_term([F|As], Goals, Val) :- ( atom(F), fun(F) -> translate_expr([F|As], Goals, Val)
                                                         ; eval_data_list([F|As], Goals, Val) ).

%Handle data list entry:
eval_data_list([], [], []).
eval_data_list([E|Es], Goals, [V|Vs]) :- ( is_list(E) -> eval_data_term(E, G1, V) ; V = E, G1 = [] ),
                                         eval_data_list(Es, G2, Vs),
                                         append(G1, G2, Goals).


%Convert let* to recusrive let:
letstar_to_rec_let([[Pat,Val]],Body,[let,Pat,Val,Body]).
letstar_to_rec_let([[Pat,Val]|Rest],Body,[let,Pat,Val,Out]) :- letstar_to_rec_let(Rest,Body,Out).

%Patterns: variables, atoms, numbers, lists:
translate_pattern(X, X) :- var(X), !.
translate_pattern(X, X) :- atomic(X), !.
translate_pattern([H|T], [P|Ps]) :- !, translate_pattern(H, P),
                                       translate_pattern(T, Ps).

% Constructs the goal for a single branch of an if-then-else/case.
build_branch(true, Val, Out, (Out = Val)) :- !.
build_branch(Con, Val, Out, Goal) :- var(Val) -> Val = Out, Goal = Con
                                               ; Goal = (Val = Out, Con).

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

translate_progn([X], Goals, Out) :- !, translate_expr(X, Goals, Out).
translate_progn([X|Xs], Goals, Out) :- counting(translate_expr(X, G1, _), XEdits),
                                       counting(translate_progn(Xs, G20, Out0), RestEdits),
                                       either_true(XEdits, RestEdits, Live),
                                       maybe_stretch(Live, [progn|Xs], G20, Out0, G2, Out),
                                       append(G1, G2, Goals).

%Build A ; B ; C ... from a proper list into a fresh output goal:
disj_list([], fail).
disj_list([G], G) :- !.
disj_list([G|Gs], (G ; R)) :- disj_list(Gs, R).

%Build one disjunct per branch: (Conj, Out = Val):
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

declared_output_type(F, OutType) :- atom(F),
                                    nonvar(OutType),
                                    catch(match('&self', [':', F, TypeChain], TypeChain, TypeChain), _, fail),
                                    TypeChain = [->|Types],
                                    append(_, [DeclaredOutType], Types),
                                    DeclaredOutType == OutType.

%The key of a case with an Empty case runs once, and Empty only if the key yields no value. Soft-cut does exactly
%this, but would make a cut inside the key local to it; so a key containing a cut instead records in a fresh
%non-backtrackable flag whether it yielded a value, and its cut still commits the clause:
case_with_empty(GkConj, CaseGoal, DefaultThen, ( GkConj *-> CaseGoal ; DefaultThen )) :- \+ ( sub_term(G, GkConj), G == ! ), !.
case_with_empty(GkConj, CaseGoal, DefaultThen, ( functor(Seen, seen, 1),
                                                 ( GkConj, nb_setarg(1, Seen, true), CaseGoal
                                                 ; arg(1, Seen, S), var(S), DefaultThen ) )).
