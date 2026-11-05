:- use_module(type_obligations).
% Runtime contracts. Reflection (get-type) is deliberately independent.
:- dynamic type_worker/3, type_wrapper/3, type_redirect/2, type_tail_entry/2, type_raw_calls/0, type_dispatch_clause/2, type_raw_function/1, type_call_entry/3.

% The declaration index is a compiled view of &self, updated in the same
% transaction as its source rows. Wildcard rows remain ordinary space data.
:- dynamic type_declaration/2, type_pattern_declaration/3, type_constructor_cache/2.
type_index_add(F,T) :-
    (nonvar(F),acyclic_term(F-T),term_attvars(F-T,[]),\+ (sub_term(P,T),P=='$any'(true)) -> assertz(type_declaration(F,T)),
       (atom(F)->true;type_pattern_key(F,Key),assertz(type_pattern_declaration(Key,F,T))),type_forget_constructors(F)
    ;true).
type_index_remove(Term) :- copy_term_nat(Term,[:,F,T]),
    retractall(type_declaration(F,T)),retractall(type_pattern_declaration(_,F,T)),retractall(type_constructor_cache(_,_)).
type_pattern_key([],nil) :- !.
type_pattern_key([H|_],Key) :- !,(atom(H)->Key=head(H);Key=wild).
type_pattern_key(_,opaque).

type_source_schema(F,N,Chain) :- type_declaration(F,D),acyclic_term(D),is_list(D),
    D=[Tag|Chain],Tag==(->),L is N+1,length(Chain,L).
type_schema(F,N,Types) :- type_schema_for(F,N,none,Types).
type_schema_for(F,N,Current,Types) :- type_declaration(F,D),acyclic_term(D),is_list(D),D=[Tag|Chain],Tag==(->),
    append(Inputs,[Result],Chain),length(Inputs,M),
    (M==N -> Types=Chain
    ;M<N,((Current==M;type_eta_source(F,N,M))->Eta=true;Eta=false),
     type_schema_arity(Inputs,Result,N,Eta,Types)).
type_eta_source(F,N,M) :- A is N+1,
    once((equation_arity(F,A,Ref),translated_from(Ref,[=,[F|Args],_]),length(Args,M))).
type_schema_arity(Inputs,Result,N,Eta,Types) :- length(Inputs,M),
    (M==N -> append(Inputs,[Result],Types)
    ;M<N,Eta==true,var(Result) -> K is N-M,length(More,K),append(More,[Out],Tail),Result=[->|Tail],
                        append(Inputs,More,All),append(All,[Out],Types)
    ;M<N,Eta==true,(Result=='Atom';Result=='%Undefined%';Result=='_') ->
        K is N-M,length(More,K),maplist(=('%Undefined%'),More),append(Inputs,More,All),append(All,[Result],Types)
    ;M<N,Result=[Tag|Tail],Tag==(->),is_list(Tail),append(More,[Out],Tail),
        append(Inputs,More,All),type_schema_arity(All,Out,N,Eta,Types)).
type_schemas(F,N,Schemas) :- findall(Ts,type_schema(F,N,Ts),Raw),
    (Raw=[_,_|_]->sort(Raw,Schemas);Schemas=Raw).
type_eta_allowed(F,N) :-
    findall(R,(type_source_schema(F,N,Ts),last(Ts,R)),Returns),
    (Returns==[];member(R,Returns),(var(R);R=='%Undefined%';R=='_';R=[Tag|_],Tag==(->))).

type_mode(T) :- nonvar(T), memberchk(T, ['Atom','Variable','Symbol','Expression','Grounded']).
type_observe(T, V) :- ( T == 'Atom' -> true ; T == 'Variable' -> var(V)
    ; var(V) -> true ; 'get-metatype'(V, M), M == T ).
type_normalize(T, R) :- ( var(T) -> R = T
    ; (T == '%Undefined%'; T == '_') -> R = '$any'(true)
    ; is_list(T),T=[Tag|_],Tag==(->) -> R=T
    ; is_list(T) -> maplist(type_normalize, T, R) ; R = T ).
type_slot(T, V, R) :- (type_mode(T) -> type_observe(T, V), R = '$any'(true); type_normalize(T, R)).
type_free_schema(Ts) :- forall(member(T, Ts),
    (T == 'Atom'; T == '%Undefined%'; T == '_')).
type_guarded(F, N, Schemas) :- \+ translator_rule(F), type_schemas(F, N, Schemas), Schemas \== [],
    \+ (member(Ts, Schemas), type_free_schema(Ts)).

type_guarded_clause(F,N,[=,[_|Args],_],Schemas) :- \+translator_rule(F),length(Args,SourceN),
    findall(Ts,type_schema_for(F,N,SourceN,Ts),Raw),sort(Raw,Schemas),Schemas\==[],
    \+ (member(Ts,Schemas),type_free_schema(Ts)).

% A frame keeps factored type equations and pending value requests. Solving a
% check binds no program values and commits no overload or declaration world.
types_enter(Schemas, Args, Frame) :- acyclic_term(Args),
    type_stamp(Stamp),type_input_options(Schemas,Args,Options), Options\==[], Frame=choices(Options,input,_Identity,Stamp,Args),
    type_validate(Frame),maplist(type_arm_option(Frame),Options).
type_arm_option(Frame,option(_,_,Form)) :- type_arm(Frame,Form).
type_input_options([],_,[]).
type_input_options([Schema|Schemas],Args,Options) :-
    ( append(Input,[Result],Schema), maplist(type_slot,Input,Args,Types)
      -> (type_mode(Result) -> Mode=mode(Result),Out='$any'(true);Mode=value,type_normalize(Result,Out)),
         type_input_formulas(Args,Types,Out,Types,Form),Options=[option(Mode,Out,Form)|Rest]
    ; Options=Rest ),type_input_options(Schemas,Args,Rest).

types_exit(Frame, Value) :- acyclic_term(Value), arg(1,Frame,Options),
    arg(5,Frame,Inputs),setarg(5,Frame,[Value|Inputs]),
    arg(4,Frame,Before),type_stamp(Now),(Before==Now->Stable=true;Stable=false),
    type_output_options(Options,Value,Stable,Next,Fresh),Next\==[],setarg(1,Frame,Next),setarg(2,Frame,output),
    type_validate(Frame),maplist(type_arm(Frame),Fresh),type_discharge(Frame).
type_output_options([],_,_,[],[]).
type_output_options([option(Mode,Type,Before)|Options],Value,Stable,Next,Fresh) :-
    ( Mode=mode(M) -> (type_observe(M,Value)->After=yes,Keep=true;Keep=false)
    ; Stable==true,type_same_input(Before,Type,Value)
      -> type_alias_input(Before,Type,Value,Aliased),After=yes,Keep=true
    ; type_formula(Value,Type,After),Keep=true ),
    (var(Aliased)->Aliased=Before;true),
    (Keep==true -> Next=[option(done,Type,both(Aliased,After))|Rest],Fresh=[After|More];Next=Rest,Fresh=More),
    type_output_options(Options,Value,Stable,Rest,More).

% Reusing an identical input check requires unchanged declarations and
% callable names. Native generations only test this premise; they pin no world.
type_stamp(stamp(D,F,A,E)) :-
    predicate_property(type_declaration(_,_),last_modified_generation(D)),
    predicate_property(fun(_),last_modified_generation(F)),
    predicate_property(arity(_,_),last_modified_generation(A)),
    predicate_property(equation_arity(_,_,_),last_modified_generation(E)).
type_same_input(has(E,U),T,V) :- U==T,arg(1,E,Value),Value==V.
type_same_input(passive(F),T,V) :- type_same_input(F,T,V).
type_same_input(both(A,B),T,V) :- (type_same_input(A,T,V);type_same_input(B,T,V)).
type_alias_input(passive(F),T,V,yes) :- type_same_input(F,T,V),!.
type_alias_input(both(A,B),T,V,both(C,D)) :- !,type_alias_input(A,T,V,C),type_alias_input(B,T,V,D).
type_alias_input(F,_,_,F).

% Each unknown leaf owns one suspension. Binding it compiles that leaf once;
% other input evidence remains intact. Completed vacuous frames are released.
type_validate(Frame) :- arg(1,Frame,Options),
    (Options==[] -> true;arg(2,Frame,Stage), \+ \+ (member(option(_,T,F),Options),(T=='$any'(true)->true;type_kind(T)),type_satisfies(F,Stage))).
type_arm(Frame,passive(has(E,_))) :- !,type_arm_evidence(Frame,E,passive).
type_arm(Frame,has(E,_)) :- !,type_arm_evidence(Frame,E,active).
type_arm(Frame,both(A,B)) :- !,type_arm(Frame,A),type_arm(Frame,B).
type_arm(_,_).
% Native traversal visits each open value variable once, including repeated
% occurrences and opaque fields; declaration parameters are not value variables.
type_arm_evidence(Frame,E,Kind) :- arg(1,E,Value),term_variables(Value,Vars),
    maplist(type_watch_value(Frame,Kind),Vars).
type_watch_value(Frame,Kind,V) :- type_obligations:watch(V,_,Frame,Kind).
type_satisfies(yes,_).
type_satisfies(passive(_),input) :- !.
type_satisfies(passive(F),Stage) :- type_satisfies(F,Stage).
type_satisfies(both(A,B),Stage) :- type_satisfies(A,Stage),type_satisfies(B,Stage).
type_satisfies(has(E,T),_) :- type_evidence_has(E,T,_,[]).

type_input_formulas([],[],_,_,yes).
type_input_formulas([V|Vs],[T|Ts],Out,All,both(Here,Rest)) :-
    (var(T),occurrences_of_var(T,All,1) ->
       (occurrences_of_var(T,Out,0)->Here=yes;type_formula(V,T,F),Here=passive(F))
    ;type_formula(V,T,Here)),type_input_formulas(Vs,Ts,Out,All,Rest).
type_formula(_,T,yes) :- T=='$any'(true),!.
type_formula(V,T,F) :- ground(V),ground(T),!,
    (type_ground_formula(T,V)->F=yes;F=no).
type_formula(V,T,has(E,T)) :- type_capture(V,E).

% Evidence records the clauses entered for known structure. An unknown leaf
% records its own later lookup; no full declaration environment is retained.
type_capture(V,open(V,Cell)) :- var(V),!,type_obligations:cell(V,Cell).
type_capture(V,primitive(V,Rows,'Number')) :- number(V),!,type_annotations(V,Rows).
type_capture(V,primitive(V,Rows,'String')) :- string(V),!,type_annotations(V,Rows).
type_capture(V,primitive(V,Rows,'Bool')) :- (V==true;V==false),!,type_annotations(V,Rows).
type_capture(V,E) :- type_annotations(V,Rows),
    (V==[] -> E=nil([],Rows)
    ;atom(V) -> E=atom(V,Rows)
    ;V=[H|Tail] -> type_capture(H,HE),type_capture(Tail,TE),
        ((var(H);atom(H),arg(2,HE,[_|_]))->type_constructors(H,Ctors);Ctors=[]),
        E=cons(V,Rows,Ctors,HE,TE)
    ;V=partial(F,Bound),atom(F),is_list(Bound) -> type_capture(Bound,BE),length(Bound,N),
        findall(Used-[->|Later],(type_partial_schema(F,N,Ts),
            length(Used,N),append(Used,Rest,Ts),Rest\==[],type_curried(Rest,Later)),Schemes),
        E=partial(V,Rows,BE,Schemes)
    ;functor(V,F,N),E=opaque(V,Rows,F,N) ).
type_partial_schema(F,Bound,Ts) :-
    (arity(F,_) -> arity(F,A),N is A-1,N>=Bound,type_schema(F,N,Ts)
    ;type_declaration(F,D),is_list(D),D=[Tag|Ts],Tag==(->)).
type_annotations(V,Rows) :-
    (atom(V) -> (type_declaration(V,_)->findall(V-T,type_atom_annotation(V,T),Named);Named=[])
    ;\+ type_pattern_declaration(_,_,_) -> Named=[]
    ;type_pattern_key(V,Key),
     ((type_pattern_declaration(Key,_,_);Key\==wild,type_pattern_declaration(wild,_,_)) ->
       findall(P-T,(type_pattern_declaration(Key,P,T);Key\==wild,type_pattern_declaration(wild,P,T)),Named)
     ;Named=[])),
    (Named==[]->Rows=[];include(type_matching_row(V),Named,Rows)).
type_atom_annotation(F,T) :- type_declaration(F,T),
    \+ (fun(F),nonvar(T),T=[Tag|_],Tag==(->)).
type_atom_annotation(F,[->|Ts]) :- fun(F),arity(F,A),A>=1,N is A-1,type_schema(F,N,Schema),
    type_curried(Schema,Ts).
% A function value also takes its inputs in curried groups: an incomplete
% application is completed when its remaining arguments arrive.
type_curried(Ts,Ts).
type_curried(Ts,Curried) :- append(Now,[Next|Rest],Ts),Now\==[],Rest\==[],
    type_curried([Next|Rest],Later),append(Now,[[->|Later]],Curried).
type_matching_row(V,P-T) :- nonvar(T),acyclic_term(T),
    \+ memberchk(T,['Number','String','Bool','%Undefined%','_']),
    (T=[Tag|_],Tag==(->) -> atom(V),is_list(T),T=[_,_|_];type_nominal_result(T)),
    \+ \+ type_kind(T),
    copy_term_nat(P-V,Pattern-Value),unify_with_occurs_check(Pattern,Value).
type_constructors(H,Ctors) :-
    (atom(H)->(type_declaration(H,_)->type_constructor_templates(known(H),Ctors);Ctors=[])
    ;var(H)->type_constructor_templates(open,Ctors);Ctors=[]).
type_constructor_templates(Key,Ctors) :- type_constructor_cache(Key,Ctors),!.
type_constructor_templates(Key,Ctors) :- with_mutex(petta_definitions,transaction((
    (type_constructor_cache(Key,Ctors)->true
    ;(Key==open->true;Key=known(F)),type_collect_constructors(F,Ctors),assertz(type_constructor_cache(Key,Ctors)))))).
type_forget_constructors(F) :- retractall(type_constructor_cache(known(F),_)),retractall(type_constructor_cache(open,_)).
type_collect_constructors(Lookup,Ctors) :- findall(ctor(F,Fields,Out),
       (type_declaration(Lookup,D),F=Lookup,atom(F),\+ fun(F),is_list(D),D=[Tag|Ts],Tag==(->),
        append(Ps,[R],Ts),maplist(type_field_type,Ps,Fields),type_normalize(R,Out),type_nominal_result(Out)),Ctors).

% The same relation serves general contracts and grounded membership fallback.
% Private type parameters unify; program values are only inspected.
type_member(V,T,Pending) :- type_capture(V,E),type_evidence_has(E,T,Pending,[]).
type_solve([],[],[]).
type_solve([V|Vs],[T|Ts],Pending) :- type_member(V,T,Here),type_solve(Vs,Ts,Rest),append(Here,Rest,Pending).
type_kind(T) :- var(T),!,freeze(T,type_kind(T)).
type_kind(T) :- atomic(T),!,\+memberchk(T,['ListOf','TupleOf','PairOf','Opaque',->,'%Undefined%','_']).
type_kind([]) :- !.
type_kind([H|Args]) :-
    (H=='ListOf' -> Args=[T],type_kind(T)
    ;H=='TupleOf' -> type_kinds(Args)
    ;H=='PairOf' -> Args=[A,B],type_kind(A),type_kind(B)
    ;H=='Opaque' -> Args=[F,N],freeze(F,atom(F)),freeze(N,(integer(N),N>=0))
    ;H==(->) -> Args=[_|_],type_slot_kinds(Args)
    ;type_kinds([H|Args])).
type_kinds(Ts) :- var(Ts),!,freeze(Ts,type_kinds(Ts)).
type_kinds([]).
type_kinds([T|Ts]) :- type_kind(T),type_kinds(Ts).
type_slot_kinds(Ts) :- var(Ts),!,freeze(Ts,type_slot_kinds(Ts)).
type_slot_kinds([]).
type_slot_kinds([T|Ts]) :- type_slot_kind(T),type_slot_kinds(Ts).
type_slot_kind(T) :- (T=='%Undefined%';T=='_'),!.
type_slot_kind(T) :- type_kind(T).

% Data constructors have a named result family. Predefined representation
% types use their native formation rules; declarations are not casts to them.
type_nominal_result(T) :- nonvar(T),T\==[],
    (atomic(T)->Head=T;is_list(T),T=[Head|_],atom(Head)),
    \+memberchk(Head,['Number','String','Bool','ListOf','TupleOf','PairOf','Opaque',->,'%Undefined%','_']).
type_evidence_has(_,T,P,P) :- T=='$any'(true),!.
type_evidence_has(open(V,Cell),T,P,R) :- !,type_kind(T),
    (var(Cell)->P=[need(V,T)|R];type_evidence_has(Cell,T,P,R)).
type_evidence_has(primitive(V,Rows,K),T,P,R) :- !,
    (unify_with_occurs_check(T,K),P=R
    ;type_kind(T),freeze(T,type_nonprimitive(T)),type_evidence_branch(primitive(V,Rows,K),T,P,R)).
type_evidence_has(E,T,P,R) :-
    type_kind(T),freeze(T,type_nonprimitive(T)),type_evidence_branch(E,T,P,R).
type_nonprimitive(T) :- \+ memberchk(T,['Number','String','Bool']).
type_evidence_branch(E,T,P,R) :- arg(1,E,Value),arg(2,E,Rows),member(Pattern-Type,Rows),
    copy_term_nat(Pattern-Type,A-U),type_kind(U),unify_with_occurs_check(T,U),
    type_pattern_match(A,Value,P,R).
type_evidence_branch(atom(_,[]),'Symbol',P,P).
type_evidence_branch(cons(Value,_,Ctors,_,Tail),T,P,R) :-
    member(Scheme,Ctors),copy_term_nat(Scheme,ctor(F,Fields,Out)),type_kind(Out),Value=[Head|_],
    (var(Head)->P=[pattern(F,Head)|Q];Head==F,P=Q),
    unify_with_occurs_check(T,Out),type_evidence_vector(Tail,Fields,Q,R).
type_evidence_branch(E,T,P,R) :- type_evidence_vector(E,T,P,R).
type_evidence_branch(E,['TupleOf'|Ts],P,R) :- type_evidence_vector(E,Ts,P,R).
type_evidence_branch(E,['ListOf',Item],P,R) :- type_evidence_list(E,Item,P,R).
type_evidence_branch(cons(_,_,_,H,T),['PairOf',A,B],P,R) :-
    type_evidence_has(H,A,P,Q),type_evidence_has(T,B,Q,R).
type_evidence_branch(partial(_,_,Bound,Schemes),T,P,R) :-
    member(S, Schemes),copy_term_nat(S,Used-Out),maplist(type_bound_domain,Used,Fields),
    type_kind(Out),unify_with_occurs_check(T,Out),type_evidence_vector(Bound,Fields,P,R).
type_evidence_branch(partial(_,_,_,_),T,P,P) :- unify_with_occurs_check(T,['Opaque',partial,2]).
type_evidence_branch(opaque(_,_,F,N),T,P,P) :- unify_with_occurs_check(T,['Opaque',F,N]).
% Matching a nominal pattern instantiates the variables it shares with its type.
% Unknown parts of the value are matched as private copies and stay pending.
type_pattern_match(A,Value,P,R) :-
    (ground(Value) -> unify_with_occurs_check(A,Value),P=R
    ;copy_term_nat(Value,Copy),unify_with_occurs_check(A,Copy),P=[pattern(A,Value)|R]).

type_bound_domain(T,R) :- (type_mode(T)->R='$any'(true);type_normalize(T,R)).
type_evidence_vector(open(V,Cell),Ts,P,R) :- !,
    (var(Cell)->freeze(Ts,is_list(Ts)),P=[arguments(V,Ts)|R];type_evidence_vector(Cell,Ts,P,R)).
type_evidence_vector(nil([],_),[],P,P).
type_evidence_vector(cons(_,_,_,H,T),[A|As],P,R) :-
    type_evidence_has(H,A,P,Q),type_evidence_vector(T,As,Q,R).
type_evidence_list(open(V,Cell),T,P,R) :- !,
    (var(Cell)->P=[list(V,T)|R];type_evidence_list(Cell,T,P,R)).
type_evidence_list(nil([],_),_,P,P).
type_evidence_list(cons(_,_,_,H,T),E,P,R) :-
    type_evidence_has(H,E,P,Q),type_evidence_list(T,E,Q,R).

% Once all residual type parameters are independent, they constrain no future
% values. Release the completed frame.
type_discharge(Frame) :- arg(1,Frame,Options),
    ( \+ \+ (member(option(_,_,Form),Options),type_residual(Form,Pending,[]),
                 is_list(Pending),type_independent(Pending))
      -> arg(5,Frame,Values),term_variables(Values,Vars),setarg(1,Frame,[]),setarg(5,Frame,[]),
         maplist(type_obligations:release(Frame),Vars)
    ;true ).
type_residual(yes,P,P).
type_residual(passive(F),P,R) :- type_residual(F,P,R).
type_residual(both(A,B),P,R) :- type_residual(A,P,Q),type_residual(B,Q,R).
type_residual(has(E,T),P,R) :- type_evidence_has(E,T,P,R).
% Patterns are vacuous only jointly: their values already match them, and the
% matched type variables are free of kinds and of every open-value request.
type_independent(Pending) :- type_requests(Pending,Needs,Patterns,Values),
    forall(member(need(V,T),Needs),(var(V),type_free_parameter(T),
        forall(member(need(W,U),Needs),(U==T -> W==V;true)))),
    subsumes_term(Patterns,Values),term_variables(Patterns,Vars),
    forall(member(X,Vars),(\+ attvar(X),\+ (member(need(_,U),Needs),U==X))).
% Well-formedness alone does not restrict a free parameter's values.
% Other type attributes and pattern variables must remain constrained.
type_free_parameter(T) :- var(T),
    (get_attrs(T,Attrs)->Attrs=att(freeze,Goals,[]),type_kind_goals(Goals,T);true).
type_kind_goals('$and'(A,B),T) :- !,type_kind_goals(A,T),type_kind_goals(B,T).
type_kind_goals(user:type_kind(U),T) :- U==T.
type_requests([],[],[],[]).
type_requests([need(V,T)|Rest],[need(V,T)|Needs],Ps,Vs) :- type_requests(Rest,Needs,Ps,Vs).
type_requests([pattern(P,V)|Rest],Needs,[P|Ps],[V|Vs]) :- type_requests(Rest,Needs,Ps,Vs).
% An open value passed through many boundaries keeps one copy of each test;
% freeze/2 joins the goals in its attribute with '$and'/2.
type_freeze(V,Test) :- get_attr(V,freeze,Frozen),type_frozen(Frozen,user:Test),!.
type_freeze(V,Test) :- freeze(V,Test).
type_frozen('$and'(A,B),Test) :- !,(type_frozen(A,Test);type_frozen(B,Test)).
type_frozen(Goal,Test) :- Goal==Test.

% Source clauses retain their existing ownership and logical arity records.
type_store_clause(Term, (Head :- Body), (Stored :- Worker)) :-
    Term = [=,[F|_],_], type_update_dispatch(F), Head =.. [F|Args], length(Args, A), N is A-1,
    ( type_guarded_clause(F,N,Term,_) -> type_worker_name(F, A, W), Stored =.. [W|Args],
        (retract(type_redirect(W,Ref)) -> erase(Ref); true),
        last(Args,Out),type_tail_calls(Body,F,A,W,Out,Worker)
    ; Stored = Head, Worker = Body ).

% A self-call in tail position that returns this clause's own result needs no
% result check of its own: the entry checks that same value right after it,
% under the same definitions. Its inputs are still checked, and the worker
% call becomes the last call, so typed tail recursion runs in constant space.
type_tail_calls(Body,F,A,W,Out,Worker) :- N is A-1,
    ( type_schemas(F,N,[Schema]),append(Inputs,[Result],Schema),
      length(Probe,N),maplist(type_inline_slot(Schema),Inputs,Probe,_),type_inline_slot(Schema,Result,_,_)
      -> atom_concat('$tail$',W,Tail),type_tail_rewrite(Body,F,A,Tail,Out,Worker),
         (Worker==Body->true;type_tail_target(A,W,Schema,Tail))
    ; Worker = Body ).
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
type_retire_worker(F,A,W) :- type_redirect_worker(F,A,W),
    (type_tail_entry(W,Tail)->type_redirect_worker(F,A,Tail);true).
type_redirect_worker(F,A,W) :-
    (type_redirect(W,_) -> true
    ;length(Args,A),Head=..[W|Args],Call=..[F|Args],
     assertz((Head:-Call),Ref),assertz(type_redirect(W,Ref))).

% Primitive monomorphic boundaries compile to native inline tests.
type_entry_body(W,Args,Out,Schemas,Body) :-
    append(Args,[Raw],All),Call=..[W|All],type_contract_body(Args,Out,Raw,Schemas,Call,Body).
type_contract_body(Args,Out,Raw,[Schema],Call,Body) :- Raw=Out,append(Inputs,[Result],Schema),
    maplist(type_inline,Inputs,Args,Before),type_inline(Result,Raw,After),!,
    append(Before,[Call,After],Goals),exclude(==(true),Goals,Needed),goals_list_to_conj(Needed,Body).
% A single signature's independent slots need no joint solver. Only shared
% parameters and non-ground structured types remain in the residual frame.
type_contract_body(Args,Out,Raw,[Schema],Call,Body) :- !,Raw=Out,append(Inputs,[Result],Schema),
    type_split_slots(Schema,Inputs,Args,Before,Types,Values),
    (type_inline_slot(Schema,Result,Out,After)->Last='_';Last=Result,After=true),
    (Types==[],Last=='_' -> Enter=[],Exit=[]
    ;append(Types,[Last],Reduced),type_prime_schema(Reduced),
     Enter=[types_enter([Reduced],Values,Frame)],Exit=[types_exit(Frame,Out)]),
    append([Before,Enter,[Call],Exit,[After]],Goals),
    exclude(==(true),Goals,Needed),goals_list_to_conj(Needed,Body).
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
type_inline(T,V,Goal) :- ground(T),\+ type_mode(T),
    type_code_goal(T,V,[],Fast),
    Goal=(ground(V) -> acyclic_term(V),once(Fast);types_enter([[T,'_']],[V],_)).

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

type_prime_schema(Schema) :- forall((member(T,Schema),ground(T),\+ type_mode(T),T\=='_',T\=='%Undefined%'),
    type_code_goal(T,_,[],_)).
type_ground_formula(T,V) :- type_member_key(T,Key),
    (type_member_code(Key,T,Name) -> Call=..[Name,V],once(Call);type_ground_check(T,V)).

type_public_name(F) :-
    ( (sub_atom(F,0,6,_,'$body$');sub_atom(F,0,8,_,'$member$');sub_atom(F,0,6,_,'$call$');sub_atom(F,0,6,_,'$tail$'))
      -> domain_error(public_function_name,F);true ).
type_plain_source(Term) :- term_attvars(Term,Vars),
    (Vars==[] -> true;type_error(plain_source,Term)).
