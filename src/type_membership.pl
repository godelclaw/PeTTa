% Ground membership compiles to indexed clauses. Open values use the same
% contract formulas as other calls. Generated predicate names remain stable
% across declaration edits, using Prolog's ordinary logical update view.
:- dynamic type_member_code/3, type_member_dep/3.

type_ground_check(T,V) :- once(type_member(V,T,[])).
type_member_key(T,Key) :- (atom(T)->Key=T;T=[Head|_],atom(Head)->Key=Head;Key='$other').
% A family recurring inside itself compiles while it shrinks to a part of the
% enclosing type; a growing (non-regular) family uses the general check.
% Like the general relation, compiled membership admits no value of an
% ill-kinded type, including a declared field type. Kinds are checked
% only while code is generated.
type_code_goal(T,V,Seen,Goal) :-
    (type_inline_primitive(T,V,Goal) -> true
    ; \+ \+ type_kind(T) -> type_code_goal_kinded(T,V,Seen,Goal)
    ; Goal = fail ).
type_code_goal_kinded(T,V,Seen,Goal) :-
    ( ground(T),type_member_key(T,Key),
      (member(Ancestor,Seen),type_member_key(Ancestor,Key),Ancestor\==T,\+ (sub_term(S,Ancestor),S==T)
        -> Goal=type_ground_check(T,V)
      ; type_code(T,Seen,Name),Goal=..[Name,V]) ).
type_inline_primitive('Number',V,number(V)).
type_inline_primitive('String',V,string(V)).
type_inline_primitive('Bool',V,(V==true->true;V==false)).
type_inline_primitive('$any'(true),_,true).

type_code(T,_,Name) :- type_member_key(T,Key),type_member_code(Key,T,Name),!.
type_code(T,Seen,Name) :- type_member_key(T,Key),
    flag(type_member,I,I+1),format(atom(Candidate),'$member$~d',[I]),
    (current_predicate(Candidate/_) -> type_code(T,Seen,Name)
    ; Name=Candidate,dynamic(Name/1),assertz(type_member_code(Key,T,Name)),type_build_code(T,Name,[T|Seen]) ).
type_build_code(T,Name,Seen) :-
    retractall(type_member_dep(_,Name,_)),
    findall(Clause,type_member_clause(T,Name,Seen,Clause),Clauses),
    Head=..[Name,_],retractall(Head),forall(member(C,Clauses),assertz(C)).

type_member_clause(T,Name,_,(Head :- type_ground_check(T,V))) :-
    (T=='Symbol';T=[Tag|_],Tag==(->);T=['Opaque',_,_]),!,Head=..[Name,V].
type_member_clause(['ListOf',T],Name,Seen,(Head :- Body)) :- !,
    (Head=..[Name,[]],Body=true
    ;Head=..[Name,[H|Tail]],type_code_goal(T,H,Seen,Here),Again=..[Name,Tail],Body=(Here,Again)).
type_member_clause(['TupleOf'|Ts],Name,Seen,(Head :- Body)) :- !,
    same_length(Vs,Ts),maplist(type_field_goal(Seen),Ts,Vs,Goals),
    Head=..[Name,Vs],goals_list_to_conj(Goals,Body).
type_member_clause(['PairOf',A,B],Name,Seen,(Head :- (GA,GB))) :- !,
    Head=..[Name,[H|Tail]],type_code_goal(A,H,Seen,GA),type_code_goal(B,Tail,Seen,GB).
type_member_clause(T,Name,Seen,(Head :- Body)) :-
    ( type_declaration(P,Declared),\+ (Declared=[Tag|_],Tag==(->)),
      nonvar(Declared),type_normalize(Declared,U),type_nominal_result(U),type_kind(U),unify_with_occurs_check(U,T),
      Head=..[Name,P],Body=true
    ; type_declaration(F,D),atom(F),is_list(D),D=[Tag|Ts],Tag==(->),
      append(Ps,[R],Ts),type_normalize(R,U),type_nominal_result(U),type_kind(U),unify_with_occurs_check(U,T),
      (fun(F)->Was=function;Was=data),
      (type_member_dep(F,Name,Was)->true;assertz(type_member_dep(F,Name,Was))),
      Was==data,maplist(type_field_type,Ps,Fields),same_length(Args,Fields),
      Head=..[Name,[F|Args]],
      (ground(Fields)->maplist(type_field_goal(Seen),Fields,Args,Goals),goals_list_to_conj(Goals,Body)
      ;Body=type_solve(Args,Fields,[]))
    ; is_list(T),same_length(Vs,T),maplist(type_field_goal(Seen),T,Vs,Goals),
      Head=..[Name,Vs],goals_list_to_conj(Goals,Body) ).
type_field_type(T,R) :- type_normalize(T,R).
type_field_goal(Seen,T,V,Goal) :- type_code_goal(T,V,Seen,Goal).

% Update just the result-type family touched by a declaration. A genuinely
% polymorphic result can affect every family; it is the exceptional full case.
type_rebuild_declaration(D) :-
    (nonvar(D),D=[Tag|Ts],Tag==(->),is_list(Ts),append(_,[R],Ts) -> Result=R;Result=D),
    (var(Result)->findall(T-Name,type_member_code(_,T,Name),Affected)
    ;type_member_key(Result,Key),findall(T-Name,type_member_code(Key,T,Name),Affected)),
    (nonvar(D),D=[Tag2|_],Tag2==(->) ->
        findall(T-Name,type_member_code(->,T,Name),Arrows),append(Affected,Arrows,All)
     ;All=Affected),
    sort(All,Unique),forall(member(T-Name,Unique),type_build_code(T,Name,[T])).
type_membership_function_changed(F) :-
    (fun(F)->Now=function;Now=data),
    findall(Name,(type_member_dep(F,Name,Was),Was\==Now),Raw),sort(Raw,Names),
    forall((member(Name,Names),type_member_code(_,T,Name)),type_build_code(T,Name,[T])).
