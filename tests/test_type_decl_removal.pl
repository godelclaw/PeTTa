:- ensure_loaded('../src/metta').
:- use_module(library(plunit)).

:- begin_tests(type_decl_removal).

role_type('Number').
role_type('String').
role_type('Bool').
role_type(['Number','String']).
role_type(['->','Number','Number']).
role_type(['->',T,T]).
role_type(['Foreign']).
role_type(['Foreign',1]).
role_type(['Newtype','Number']).
role_type(['Alias','Number']).
role_type(['SpaceOf',['Number','String']]).
role_type(T) :- var(T).

% The public update API must remove the value's store entry. A separate
% function declaration survives unless the removal pattern takes its row too.
test(alias_values_keep_store_identity,
     [forall((role_type(Type), member(Mode, [ground,operator,type])))]) :-
    user:retractall(silent(_)), user:assertz(silent(true)),
    role_case(Type, Mode).

role_case(T,Mode) :-
    flag(type_decl_removal_case,I,I+1),
    format(atom(A),'type_decl_alias_~d',[I]),format(atom(V),'type_decl_value_~d',[I]),
    copy_term_nat(T,Type),
    user:'add-atom'('&self',[':',A,['Alias',Type]],true),
    user:'add-atom'('&self',[':',V,['->','Number','Number']],true),
    user:'add-atom'('&self',[':',V,A],true),
    once(user:declared_value_type(V,_)),
    (Mode==ground -> Pattern=[':',V,A]
    ;Mode==operator -> Pattern=[Op,V,A]
    ;Pattern=[':',V,Unknown]),
    user:'remove-atom'('&self',Pattern,true),
    assertion(var(Op)),assertion(var(Unknown)),
    assertion(\+ user:declared_value_type(V,_)),
    ( Mode==type -> assertion(\+ user:fn_decl(V,_,_,_,_,_))
    ; assertion(user:fn_decl(V,1,_,_,_,_)),
      user:'remove-atom'('&self',[':',V,['->','Number','Number']],true) ),
    user:'remove-atom'('&self',[':',A,['Alias',Type]],true).

:- end_tests(type_decl_removal).
