% Clause generation and call routing for runtime contracts.
% Loaded by types.pl in the existing user module. This unit owns private
% worker/entry names and depends on the membership and frame operations there.
% Source clause ownership and transactions remain the translator's responsibility.
%
% Review order: source workers -> checked tail/suffix entries -> publication
% and retirement -> boundary emission -> argument modes -> native/memo routing.
:- dynamic type_worker/3, type_wrapper/3, type_redirect/2, type_tail_entry/2, type_suffix_entry/3, type_raw_calls/0, type_dispatch_clause/2, type_raw_function/1, type_call_entry/3.

% Source clauses retain their existing ownership and logical arity records.
type_store_clause(Term, (Head :- Body), (Stored :- Worker)) :-
    Term = [=,[F|_],_], type_update_dispatch(F), Head =.. [F|Args], length(Args, A), N is A-1,
    ( type_guarded_clause(F,N,Term,_) -> type_worker_name(F, A, W), Stored =.. [W|Args],
        (retract(type_redirect(W,Ref)) -> erase(Ref); true),
        type_tail_calls(Body,F,A,W,Args,Worker)
    ; Stored = Head, Worker = Body ).

% A self-call in tail position that returns this clause's own result needs no
% result check of its own: the entry checks that same value right after it,
% under the same definitions. Its inputs are still checked, and the worker
% call becomes the last call, so typed tail recursion runs in constant space.
type_tail_calls(Body,F,A,W,Args,Worker) :- N is A-1,last(Args,Out),
    ( type_schemas(F,N,[Schema]),append(Inputs,[Result],Schema),
      length(Probe,N),maplist(type_inline_slot(Schema),Inputs,Probe,_),type_inline_slot(Schema,Result,_,_)
      -> atom_concat('$tail$',W,Tail),type_tail_rewrite(Body,F,A,Tail,Out,Tailed),
         (Tailed==Body->true;type_tail_target(A,W,Schema,Tail)),
         append(Values,[_],Args),type_suffix_known(Values,Inputs,Known),
         type_suffix_rewrite(Tailed,self(F,Tail,A,W,Schema),Known,Worker,_)
    ; Worker = Body ).
% A self-call whose argument is the tail of an input checked against a closed
% (ListOf T) needs no check at that slot: the tail of such a list is again a
% (ListOf T), and an open tail keeps the input's delayed checks. Each set of
% skipped slots has its own checked entry, retired like the tail entry.
type_suffix_known([],[],[]).
type_suffix_known([V|Vs],[T|Ts],Known) :-
    (var(V),ground(T),T=['ListOf',_],type_structural(T) -> Known=[V-T|Rest];Known=Rest),
    type_suffix_known(Vs,Ts,Rest).
type_suffix_rewrite((G,R),S,K,(G1,R1),Out) :- !,type_suffix_rewrite(G,S,K,G1,K1),type_suffix_rewrite(R,S,K1,R1,Out).
type_suffix_rewrite((C->T;E),S,K,(C1->T1;E1),K) :- !,
    type_suffix_rewrite(C,S,K,C1,KC),type_suffix_rewrite(T,S,KC,T1,_),type_suffix_rewrite(E,S,K,E1,_).
type_suffix_rewrite((C*->T;E),S,K,(C1*->T1;E1),K) :- !,
    type_suffix_rewrite(C,S,K,C1,KC),type_suffix_rewrite(T,S,KC,T1,_),type_suffix_rewrite(E,S,K,E1,_).
type_suffix_rewrite((L;R),S,K,(L1;R1),K) :- !,type_suffix_rewrite(L,S,K,L1,_),type_suffix_rewrite(R,S,K,R1,_).
type_suffix_rewrite('cdr-atom'(X,E),_,K,'cdr-atom'(X,E),[E-T|K]) :- var(X),var(E),member(V-T,K),V==X,!.
type_suffix_rewrite(G,self(F,Tail,A,W,Schema),K,Call,K) :- compound(G),compound_name_arity(G,Name,A),
    (Name==F->Kind=call;Name==Tail->Kind=tail),G=..[_|All],append(Values,[_],All),
    append(Inputs,[_],Schema),findall(I,(nth0(I,Values,V),var(V),nth0(I,Inputs,T),member(U-T0,K),U==V,T0==T),Found),
    sort(Found,Mask),Mask\==[],!,type_suffix_target(A,W,Schema,Kind-Mask,Entry),Call=..[Entry|All].
type_suffix_rewrite(G,_,K,G,K).
type_suffix_target(_,W,_,Key,Entry) :- type_suffix_entry(W,Key,Entry),!.
type_suffix_target(A,W,Schema,Kind-Mask,Entry) :-
    flag(type_suffix,I,I+1),format(atom(Candidate),'$self$~d',[I]),
    (current_predicate(Candidate/_) -> type_suffix_target(A,W,Schema,Kind-Mask,Entry)
    ;Entry=Candidate,N is A-1,length(Values,N),append(Values,[Out],All),Head=..[Entry|All],Call=..[W|All],
     append(Inputs,[Result],Schema),type_suffix_checks(Inputs,Values,0,Mask,Schema,Checks),
     (Kind==tail->After=true;type_inline_slot(Schema,Result,Out,After)),
     append(Checks,[Call,After],Goals),exclude(==(true),Goals,Needed),goals_list_to_conj(Needed,Body),
     assertz((Head:-Body)),assertz(type_suffix_entry(W,Kind-Mask,Entry))).
type_suffix_checks([],[],_,_,_,[]).
type_suffix_checks([T|Ts],[V|Vs],J,Mask,Schema,[G|Gs]) :-
    (memberchk(J,Mask)->G=true;type_inline_slot(Schema,T,V,G)),
    K is J+1,type_suffix_checks(Ts,Vs,K,Mask,Schema,Gs).
type_tail_rewrite((G,R),F,A,W,Out,(G,R1)) :- !,type_tail_rewrite(R,F,A,W,Out,R1).
type_tail_rewrite((C->T;E),F,A,W,Out,(C->T1;E1)) :- !,
    type_tail_rewrite(T,F,A,W,Out,T1),type_tail_rewrite(E,F,A,W,Out,E1).
type_tail_rewrite((C*->T;E),F,A,W,Out,(C*->T1;E1)) :- !,
    type_tail_rewrite(T,F,A,W,Out,T1),type_tail_rewrite(E,F,A,W,Out,E1).
type_tail_rewrite((L;R),F,A,W,Out,(L1;R1)) :- !,
    type_tail_rewrite(L,F,A,W,Out,L1),type_tail_rewrite(R,F,A,W,Out,R1).
type_tail_rewrite(G,F,A,W,Out,Tail) :- compound(G),compound_name_arity(G,F,A),arg(A,G,O),O==Out,!,
    G=..[F|All],Tail=..[W|All].
type_tail_rewrite(G,_,_,_,_,G).
% A separate checked entry can be redirected as a whole after a contract edit;
% no obsolete input test remains in an already-running caller.
type_tail_target(_,W,_,Tail) :- type_tail_entry(W,Tail),!.
type_tail_target(A,W,Schema,Tail) :- atom_concat('$tail$',W,Tail),
    N is A-1,length(Values,N),append(Values,[_Out],All),Head=..[Tail|All],Call=..[W|All],
    append(Inputs,[_],Schema),maplist(type_inline_slot(Schema),Inputs,Values,Checks),
    append(Checks,[Call],Goals),
    exclude(==(true),Goals,Needed),goals_list_to_conj(Needed,Body),
    (retract(type_redirect(Tail,Ref)) -> erase(Ref); true),
    assertz((Head:-Body)),assertz(type_tail_entry(W,Tail)).
type_worker_name(F, A, W) :- type_worker(F,A,W), !.
type_worker_name(F,A,W) :- flag(type_worker,I,I+1),format(atom(Candidate),'$body$~d',[I]),
    (current_predicate(Candidate/_) -> type_worker_name(F,A,W)
    ;W=Candidate,assertz(type_worker(F,A,W))).

type_publish(F) :-
    type_forget_constructors(F),
    type_membership_function_changed(F),
    type_update_dispatch(F),type_update_modes(F),
    forall(retract(type_wrapper(F,_,Ref)), erase(Ref)),
    forall(type_worker(F,A,W), type_publish_arity(F,A,W)).
type_publish_arity(F, A, W) :-
    ( equation_arity(F,A,Ref), clause(H,_,Ref), functor(H,W,A)
      -> N is A-1, type_schemas(F,N,Schemas), length(Args,N), append(Args,[Out], All),
         Head =.. [F|All], type_entry_body(W,Args,Out,Schemas,Body),
         (retract(no_equations_clause(F,A,Empty)) -> erase(Empty); true),
         assertz((Head :- Body), Entry), assertz(type_wrapper(F,A,Entry))
    ; type_retire_worker(F,A,W) ).
% A retired tail or self-call entry keeps only its redirect, so a running
% caller is checked once, under the current contract.
type_retire_worker(F,A,W) :- type_redirect_worker(F,A,W),
    forall((retract(type_tail_entry(W,Entry));retract(type_suffix_entry(W,_,Entry))),
       (length(Args,A),Head=..[Entry|Args],retractall(Head),type_redirect_worker(F,A,Entry))).
type_redirect_worker(F,A,W) :-
    (type_redirect(W,_) -> true
    ;length(Args,A),Head=..[W|Args],Call=..[F|Args],
     assertz((Head:-Call),Ref),assertz(type_redirect(W,Ref))).

% Primitive monomorphic boundaries compile to native inline tests.
type_entry_body(W,Args,Out,Schemas,Body) :-
    append(Args,[Raw],All),Call=..[W|All],type_contract_body(Args,Out,Raw,Schemas,Call,Body).
type_contract_body(Args, Out, Raw, [Schema], Call, Body) :-
    Raw = Out,
    append(Inputs, [Result], Schema),
    maplist(type_inline, Inputs, Args, Before),
    type_inline(Result, Raw, After), !,
    append(Before, [Call,After], Goals),
    exclude(==(true), Goals, Needed),
    goals_list_to_conj(Needed, Body).
% A single signature's independent slots need no joint solver. Only shared
% parameters and non-ground structured types remain in the residual frame.
type_contract_body(Args, Out, Raw, [Schema], Call, Body) :- !,
    Raw = Out,
    append(Inputs, [Result], Schema),
    type_split_slots(Schema, Inputs, Args, Before, Types, Values),
    ( type_inline_slot(Schema, Result, Out, After) -> Last = '_'
    ; Last = Result, After = true
    ),
    ( Types == [], Last == '_' -> Enter = [], Exit = []
    ; append(Types, [Last], Reduced),
      type_prime_schema(Reduced),
      Enter = [types_enter([Reduced], Values, Frame)],
      Exit = [types_exit(Frame, Out)]
    ),
    append([Before,Enter,[Call],Exit,[After]], Goals),
    exclude(==(true), Goals, Needed),
    goals_list_to_conj(Needed, Body).
type_contract_body(Args,Out,Raw,Schemas,Call,(types_enter(Schemas,Args,Frame),Call,types_exit(Frame,Out))) :-
    Raw=Out,maplist(type_prime_schema,Schemas).
type_split_slots(_,[],[],[],[],[]).
type_split_slots(Schema,[T|Ts],[V|Vs],Before,Types,Values) :-
    (type_inline_slot(Schema,T,V,Here)->Before=[Here|More],Types=Rest,Values=Tail
    ;Before=More,Types=[T|Rest],Values=[V|Tail]),
    type_split_slots(Schema,Ts,Vs,More,Rest,Tail).
type_inline_slot(Schema,T,_,true) :- var(T),!,occurrences_of_var(T,Schema,1).
type_inline_slot(_,T,V,Goal) :- (type_inline(T,V,Goal)->true;type_mode(T),Goal=type_observe(T,V)).
type_inline(T,V,Goal) :-
    ( T == 'Number' -> Test=number(V); T == 'String' -> Test=string(V)
    ; T == 'Bool' -> Test=(V==true->true;V==false) ), !,
    Goal=(var(V) -> type_freeze(V,Test); Test).
type_inline(T,_,true) :- (T == 'Atom'; T == '%Undefined%'; T == '_'),!.
type_inline(Declared,V,Goal) :- ground(Declared),\+ type_mode(Declared),type_normalize(Declared,T),
    type_code_goal(T,V,[],Fast),
    (type_structural(T) -> Open=(acyclic_term(V),type_parts(T,V)) ; Open=types_enter([[T,'_']],[V],_)),
    Goal=(ground(V) -> acyclic_term(V),once(Fast);Open).

% Argument plans are inspected before evaluation, only when holding can matter.
type_call_schemas(F,N,Schemas) :- A is N+1,
    (arity(F,A) -> type_schemas(F,N,Schemas)
    ; findall(Ts,(arity(F,M),M>A,K is M-1,type_schema(F,K,Ts)),Schemas)).
type_holds(F, N, I) :- type_call_schemas(F,N,Schemas), Schemas \== [],
    forall(member(Ts,Schemas), (nth0(I,Ts,T), T == 'Atom')).
type_translate_args(F,N,I,Raw,Goals,Values) :- type_call_schemas(F,N,Schemas),
    type_translate_schema_args(Schemas,I,Raw,Goals,Values).
type_translate_schema_args(_,_,[],[],[]).
type_translate_schema_args(Schemas,I,[X|Xs],Goals,[V|Vs]) :-
    (Schemas\==[],forall(member(Ts,Schemas),(nth0(I,Ts,T),T=='Atom')) -> V=X,Here=[]; translate_expr(X,Here,V)),
    J is I+1,type_translate_schema_args(Schemas,J,Xs,Rest,Vs),append(Here,Rest,Goals).
type_plans([],[],[],[]).
type_plans([X|Xs],[plan(X,G,V)|Plans],Goals,[V|Vs]) :-
    translate_expr(X,Here,V),goals_list_to_conj(Here,G),type_plans(Xs,Plans,Rest,Vs),append(Here,Rest,Goals).
type_plans_needed([plan(X,G,V)|_]) :- (G\==true;X\==V),!.
type_plans_needed([_|Rest]) :- type_plans_needed(Rest).
type_indirect(F, Plans, Out) :-
    (nonvar(F),F=partial(Base,Bound)->length(Bound,Offset);Base=F,Bound=[],Offset=0),
    length(Plans,L),N is Offset+L,
    (atom(Base),fun(Base)->type_call_schemas(Base,N,Schemas);Schemas=[]),
    type_run_plans(Plans,Schemas,Offset,Args),append(Bound,Args,All),reduce([Base|All],Out).
type_run_plans([],_,_,[]).
type_run_plans([plan(X,G,V)|Plans],Schemas,I,[A|As]) :-
    (Schemas\==[],forall(member(Ts,Schemas),(nth0(I,Ts,T),T=='Atom'))->A=X;call(G),A=V),
    J is I+1,type_run_plans(Plans,Schemas,J,As).

type_update_modes(F) :-
    (type_raw_calls->Old=raw;Old=plain),
    ( fun(F),arity(F,A),N is A-1,N>0,Last is N-1,between(0,Last,I),type_holds(F,N,I)
      -> (type_raw_function(F)->true;assertz(type_raw_function(F)))
    ; retractall(type_raw_function(F)) ),
    (type_raw_function(_) -> (type_raw_calls->true;assertz(type_raw_calls)),New=raw
    ;retractall(type_raw_calls),New=plain),
    (Old==New->true;refresh_users('$argument_modes',[])).

type_declaration_changed(F) :- atom(F), !,
    findall(A-W,retract(type_worker(F,A,W)),Retired),recompile_function(F),
    forall(member(A-W,Retired),type_retire_worker(F,A,W)),
    refresh_users(F,[]).
type_declaration_changed(_).

% The ordinary resolver stays unchanged for names without a contract. Its
% variable-head fallback is indexed alongside these function-specific clauses.
type_update_dispatch(F) :-
    findall(A,(arity(F,A),A>=1,N is A-1,type_guarded(F,N,_),
         (native_arity(F,A);current_predicate(memoization_enabled_for_predicate_arity/2),
                            memoization_enabled_for_predicate_arity(F,A))),Raw),sort(Raw,Needed),
    forall(member(A,Needed),type_call_entry_name(F,A,_)),
    forall(type_call_entry(F,A,Name),type_build_call_entry(F,A,Name)),
    (Needed\==[] -> (type_dispatch_clause(F,_) -> true
       ;asserta((resolve_memoization(F,Args,Out,Goal) :- !,type_resolve(F,Args,Out,Goal)),Ref),
        assertz(type_dispatch_clause(F,Ref)))
    ;forall(retract(type_dispatch_clause(F,Ref)),erase(Ref))).
type_call_entry_name(F,A,Name) :- type_call_entry(F,A,Name),!.
type_call_entry_name(F,A,Name) :- flag(type_call,I,I+1),format(atom(Candidate),'$call$~d',[I]),
    (current_predicate(Candidate/_)->type_call_entry_name(F,A,Name)
    ;Name=Candidate,dynamic(Name/A),assertz(type_call_entry(F,A,Name))).
type_build_call_entry(F,A,Name) :- N is A-1,length(Args,N),append(Args,[Out],All),Head=..[Name|All],
    (metta_memoized_dispatch_call(F,Args,Raw,Call)->true;append(Args,[Raw],RawArgs),Call=..[F|RawArgs]),
    (type_guarded(F,N,Schemas)->type_contract_body(Args,Out,Raw,Schemas,Call,Body);Raw=Out,Body=Call),
    Empty=..[Name|All],retractall(Empty),assertz((Head :- Body)).
type_resolve(F,Args,Out,Goal) :- length(Args,N),A is N+1,
    (type_call_entry(F,A,Name) -> append(Args,[Out],All),Goal=..[Name|All]
    ;metta_memoized_dispatch_call(F,Args,Out,Goal)->true
    ;append(Args,[Out],All),Goal=..[F|All]).

type_prime_schema(Schema) :- forall((member(D,Schema),ground(D),\+ type_mode(D),D\=='_',D\=='%Undefined%'),
    (type_normalize(D,T),type_code_goal(T,_,[],_))).


type_public_name(F) :-
    ( (sub_atom(F,0,6,_,'$body$');sub_atom(F,0,8,_,'$member$');sub_atom(F,0,6,_,'$call$');sub_atom(F,0,6,_,'$tail$');sub_atom(F,0,6,_,'$self$'))
      -> domain_error(public_function_name,F);true ).
type_plain_source(Term) :- term_attvars(Term,Vars),
    (Vars==[] -> true;type_error(plain_source,Term)).
