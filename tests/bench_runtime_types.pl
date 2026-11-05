:- use_module(library(http/json)).

runtime_measure(Goal,Info) :-
    statistics(inferences,I0),statistics(cputime,T0),once(Goal),
    statistics(cputime,T1),statistics(inferences,I1),
    Inf is I1-I0,CPU is T1-T0,Info=_{inferences:Inf,cpu:CPU}.

% Measure a compiled MeTTa call. This includes legacy call-site checks as well
% as the candidate's callee checks; direct Prolog entries omit the former.
runtime_bench_main :- current_prolog_flag(argv,[Source,Kind,Size|_]),atom_number(Size,N),
    runtime_measure(load_metta_file(Source,_),Load),
    (memberchk(Kind,[count,relation])->Call=[bf,A,B],Head=runtime_bench_call(A,B,R)
    ;Call=[bf,A],Head=runtime_bench_call(A,R)),
    translate_expr(Call,Goals,R),goals_list_to_conj(Goals,Body),assertz((Head:-Body)),
    runtime_bench_goal(Kind,0,Warm),once(Warm),
    runtime_bench_goal(Kind,N,Goal),runtime_measure(Goal,Info),
    put_dict(load,Info,Load,All),json_write_dict(current_output,All),nl.
runtime_bench_goal(count,N,(runtime_bench_call(N,0,R),R=:=N)).
runtime_bench_goal(relation,N,(runtime_bench_call(N,X,R),X=7,R=7)).
runtime_bench_goal(list,N,(runtime_bench_call(L,R),R=:=N)) :- runtime_bench_list(N,L).
runtime_bench_goal(small,0,runtime_bench_call(1,_)) :- !.
runtime_bench_goal(small,N,forall(between(1,N,_),(runtime_bench_call(1,R),R=2))).
runtime_bench_list(0,'Nil') :- !.
runtime_bench_list(N,['Cons',1,T]) :- M is N-1,runtime_bench_list(M,T).

runtime_heavy_main :- current_prolog_flag(argv,[Source|_]),
    runtime_measure(load_metta_file(Source,_),Info),
    write('MEASURE='),json_write_dict(current_output,Info),nl.

% No declarations: execution should use the ordinary compiler and native APIs.
runtime_untyped_main :-
    process_metta_string("(= (bench_inc $x) (+ $x 1))
      (= (bench_ho $f $x) ($f $x))
      (= (bench_collect $x) (collapse (superpose ($x $x))))
      !(add-atom &bench_space (row 1)) !(change-state! bench_cell 1)",_),
    maplist(runtime_gate,[higher_order,collection,space,state,write_ground,write_open],Rows),
    json_write_dict(current_output,_{rows:Rows}),nl.
runtime_gate(Kind,Info) :- runtime_measure(runtime_gate_run(Kind),M),put_dict(kind,M,Kind,Info).
runtime_gate_run(higher_order) :- forall(between(1,10000,_),(bench_ho(bench_inc,1,R),R=2)).
runtime_gate_run(collection) :- forall(between(1,10000,_),(bench_collect(1,R),R=[1,1])).
runtime_gate_run(space) :- forall(between(1,10000,_),findall(X,'get-atoms'('&bench_space',X),[_])).
runtime_gate_run(state) :- forall(between(1,10000,_),'get-state'(bench_cell,1)).
runtime_gate_run(write_ground) :- forall(between(1,10000,_),
    ('add-atom'('&bench_write',[row,1],true),'remove-atom'('&bench_write',[row,1],true))).
runtime_gate_run(write_open) :- forall(between(1,10000,_),
    ('add-atom'('&bench_write',[row,_],true),'remove-atom'('&bench_write',[row,_],true))).
