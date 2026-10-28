%%%%%%%%%% Dependencies %%%%%%%%%%
:- dynamic library_path/1.

library(X, Path) :- resolve_library_path(library_path_candidate(X), Path).
library(X, Y, Path) :- resolve_library_path(library_path_candidate(X, Y), Path).

library_path_candidate(X, Path) :- standard_library_path(Base),
                                   atomic_list_concat([Base, '/', X], Path).
library_path_candidate(X, Y, Path) :- library_path(Base),
                                      atom_concat(_, X, Base),
                                      atomic_list_concat([Base, '/', Y], Path).

resolve_library_path(Candidate, Path) :- ( once((call(Candidate, ExistingPath),
                                                  library_source_exists(ExistingPath)))
                                           -> Path = ExistingPath
                                            ; once(call(Candidate, Path)) ).

library_source_exists(Path) :- exists_file(Path), !.
library_source_exists(Path) :- file_name_extension(Path, metta, MettaPath),
                               exists_file(MettaPath).
:- prolog_load_context(directory, Source),
   directory_file_path(Source, '..', Parent),
   directory_file_path(Parent, 'lib', LibPath),
   asserta(standard_library_path(LibPath)).
:- autoload(library(uuid)).
:- use_module(library(random)).
:- use_module(library(janus)).
:- use_module(library(error)).
:- use_module(library(listing)).
:- use_module(library(aggregate)).
:- use_module(library(thread)).
:- use_module(library(lists)).
:- use_module(library(yall), except([(/)/3])).
:- use_module(library(apply)).
:- use_module(library(apply_macros)).
:- use_module(library(process)).
:- use_module(library(filesex)).
:- current_prolog_flag(argv, Argv),
  ( member(mork, Argv) -> ensure_loaded([ext_points, parser, translator, filereader, '../mork_ffi/morkspaces', spaces])
                        ; ensure_loaded([ext_points, parser, translator, filereader, spaces])).

%%%%%%%%%% Standard Library for MeTTa %%%%%%%%%%

%%% Representation and parsing conversions: %%%
id(X, X).
repr(Term, R) :- swrite(Term, R).
repra(Term, R) :- term_to_atom(Term, R).
parse(Str, R) :- sread(Str, R).

%%% Arithmetic & Comparison: %%%
%Compile this section's arithmetic inline. The loader's optimise setting is kept
%for clpfd and restored after the section:
:- current_prolog_flag(optimise, Optimise), nb_setval(petta_loader_optimise, Optimise),
   set_prolog_flag(optimise, true).
%SWI arithmetic also accepts strings and singleton lists. Reject those MeTTa
%values; ordinary numeric calls avoid the helper, and named constants still work:
arith_arg(A) :- ( ( string(A) ; is_list(A) ) -> type_error(evaluable, A) ; true ).
'+'(A,B,R)  :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), R is A + B.
'-'(A,B,R)  :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), R is A - B.
'*'(A,B,R)  :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), R is A * B.
'/'(A,B,R)  :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), R is A / B.
'%'(A,B,R)  :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), R is A mod B.
'<'(A,B,R)  :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), (A<B -> R=true ; R=false).
'>'(A,B,R)  :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), (A>B -> R=true ; R=false).
'@<'(A,B,R) :- (A@<B -> R=true ; R=false).
'@>'(A,B,R) :- (A@>B -> R=true ; R=false).
'=='(A,B,R) :- (A==B -> R=true
               ; float(A) -> ((float(B) -> A =:= B ; number(B), exact_equal(A,B)) -> R=true ; R=false)
               ; float(B) -> (number(A), exact_equal(B,A) -> R=true ; R=false)
               ; compound(A) -> (compound(B), tree_equal(A,B,1024,S),
                                  (S == 0 -> graph_equal(A,B) ; true) -> R=true ; R=false)
               ; R=false).
'!='(A,B,R) :- ('=='(A,B,true) -> R=false ; R=true).
'='(A,B,R) :-  (A=B -> R=true ; R=false).
'=?'(A,B,R) :- (\+ \+ A=B -> R=true ; R=false).
'=alpha'(A,B,R) :- (A =@= B -> R=true ; R=false).
'=@='(A,B,R) :- (A =@= B -> R=true ; R=false).
'<='(A,B,R) :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), (A =< B -> R=true ; R=false).
'>='(A,B,R) :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), (A >= B -> R=true ; R=false).
'@<='(A,B,R) :- (A @=< B -> R=true ; R=false).
'@>='(A,B,R) :- (A @>= B -> R=true ; R=false).
%Numbers compare by exact value at every depth; other leaves keep SWI's identity.
%NaN keeps SWI's reflexive identity too, so the native == fast path is sound.
%After it fails, only mixed float comparisons or two compounds can still match.
%A float against an integer or a rational: cmpr is exact, where =:= would round the other to a float.
exact_equal(F,N) :- F =:= F, 0 =:= cmpr(F,N).
%The walk returns what is left of its budget.  When the budget runs out it stops descending and returns 0,
%a leaf that differs still fails it, and the graph comparison below decides.  Neither side is ever a
%variable, so list cells are taken apart in the clause head, where a unification never scans the rest of
%the list again; a unification in a body does, when occurs_check is on.  An element or argument that both
%sides share is skipped.  A tail is not tested for sharing, which would cost a call per cell: a shared
%tail is only reached when everything before it is equal in value.
%Leaf tests stay inline in both walks: different nonnumeric atoms need no helper call.
tree_equal([X|Xs],[Y|Ys],S0,S) :- !,
    ( S0 == 0 -> S = 0
    ; S1 is S0-1,
      ( atomic(X) -> S2 = S1,
        ( X == Y -> true
        ; float(X) -> (float(Y) -> X =:= Y ; number(Y), exact_equal(X,Y))
        ; float(Y), number(X), exact_equal(Y,X) )
      ; var(X) -> X == Y, S2 = S1
      ; same_term(X,Y) -> S2 = S1
      ; compound(Y), tree_equal(X,Y,S1,S2) ),
      ( compound(Xs) -> compound(Ys), tree_equal(Xs,Ys,S2,S)
      ; var(Xs) -> Xs == Ys, S = S2
      ; S = S2, '=='(Xs,Ys,true) ) ).
tree_equal(A,B,S0,S) :-
    ( S0 == 0 -> S = 0
    ; S1 is S0-1, compound_name_arity(A,F,N), compound_name_arity(B,F,N), args_equal(1,N,A,B,S1,S) ).
%K counts the arguments left: K == 0 needs no call, where I > N would.
args_equal(I,K,A,B,S0,S) :-
    ( K == 0 -> S = S0
    ; arg(I,A,X), arg(I,B,Y),
      ( atomic(X) -> S1 = S0,
        ( X == Y -> true
        ; float(X) -> (float(Y) -> X =:= Y ; number(Y), exact_equal(X,Y))
        ; float(Y), number(X), exact_equal(Y,X) )
      ; var(X) -> X == Y, S1 = S0
      ; same_term(X,Y) -> S1 = S0
      ; compound(Y), tree_equal(X,Y,S0,S1) ),
      I1 is I+1, K1 is K-1, args_equal(I1,K1,A,B,S1,S) ).
%Past the budget, terms that share no subterm are trees after all, walked again with a negative budget,
%which never runs out.  Others go to ==/2, which already compares cyclic and shared terms as graphs, once
%every finite float in them is replaced by its exact value: '$factorize_term' cuts both terms into trees at their
%shared subterms (in place, undone by \+ \+), the trees are mapped, and the factors are tied back.
graph_equal(A,B) :- \+ \+ ( '$factorize_term'(A-B, S, Fs),
                            ( Fs == [] -> tree_equal(A,B,-1,_)
                            ; exact_term(S-Fs, Mapped), tied_equal(Mapped) ) ).
tied_equal(P-Es) :- tie_factors(Es, P), pair_equal(P).
pair_equal(X-Y) :- X == Y.
exact_term(X, E) :- var(X), !, E = X.
exact_term(X, E) :- float(X), !, ( X =:= X, \+ float_class(X, infinite) -> E is rational(X) ; E = X ).
exact_term(X, E) :- atomic(X), !, E = X.
exact_term([X|Xs], [E|Es]) :- !, exact_term(X, E), exact_term(Xs, Es).
exact_term(X, E) :- compound_name_arity(X, F, N), compound_name_arity(E, F, N), exact_args(N, X, E).
%Every compound output is fresh. Set a slot to a constant before attaching its subtree:
%setarg on an unbound slot would unify and rescan that subtree under occurs_check.
exact_args(0, _, _) :- !.
exact_args(N, X, E) :- arg(N, X, A), setarg(N, E, []), exact_term(A, B), setarg(N, E, B), N1 is N-1, exact_args(N1, X, E).
%Unification would tie the factors back only where the occurs_check flag allows, so setarg does it: each
%factor variable is bound to a marker, and every argument that holds a marker is set to that factor.
tie_factors(Es, P) :- length(Es, N), functor(Fs, factors, N), foldl(mark_factor(M, Fs), Es, 1, _),
                      tie_args(P, M, Fs), tie_args(Fs, M, Fs).
mark_factor(M, Fs, V=E, I, I1) :- V = '$factor'(M, I), arg(I, Fs, E), I1 is I+1.
tie_args(T, M, Fs) :- compound(T), compound_name_arity(T, F, N), N > 0, !,
                      ( F == '[|]', N == 2 -> tie_cell(T, T, M, Fs) ; tie_args(1, N, T, M, Fs) ).
tie_args(_, _, _).
tie_cell([H|R], L, M, Fs) :- tie_arg(H, 1, L, M, Fs), tie_arg(R, 2, L, M, Fs).
tie_args(K, N, T, M, Fs) :- arg(K, T, A), tie_arg(A, K, T, M, Fs), ( K < N -> K1 is K+1, tie_args(K1, N, T, M, Fs) ; true ).
tie_arg(A, K, T, M, Fs) :- ( nonvar(A), A = '$factor'(M0, I), M0 == M -> arg(I, Fs, E), setarg(K, T, E) ; tie_args(A, M, Fs) ).
min(A,B,R)  :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), R is min(A,B).
max(A,B,R)  :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), R is max(A,B).
exp(A,R) :- ( number(A) -> true ; arith_arg(A) ), R is exp(A).
:- nb_getval(petta_loader_optimise, Optimise), set_prolog_flag(optimise, Optimise).
:- use_module(library(clpfd)).
'#+'(A, B, R) :- R #= A + B.
'#-'(A, B, R) :- R #= A - B.
'#*'(A, B, R) :- R #= A * B.
'#div'(A, B, R) :- R #= A div B.
'#//'(A, B, R) :- R #= A // B.
'#mod'(A, B, R) :- R #= A mod B.
'#min'(A, B, R) :- R #= min(A,B).
'#max'(A, B, R) :- R #= max(A,B).
'#<'(A, B, true)  :- A #< B, !.
'#<'(_, _, false).
'#>'(A, B, true)  :- A #> B, !.
'#>'(_, _, false).
'#='(A, B, true)  :- A #= B, !.
'#='(_, _, false).
'#\\='(A, B, true)  :- A #\= B, !.
'#\\='(_, _, false).
:- set_prolog_flag(optimise, true).
'pow-math'(A, B, Out) :- ( number(A), number(B) -> true ; arith_arg(A), arith_arg(B) ), Out is A ** B.
'sqrt-math'(A, Out)   :- ( number(A) -> true ; arith_arg(A) ), Out is sqrt(A).
'abs-math'(A, Out)    :- ( number(A) -> true ; arith_arg(A) ), Out is abs(A).
'log-math'(Base, X, Out) :- ( number(Base), number(X) -> true ; arith_arg(Base), arith_arg(X) ), Out is log(X) / log(Base).
'trunc-math'(A, Out)  :- ( number(A) -> true ; arith_arg(A) ), Out is truncate(A).
'ceil-math'(A, Out)   :- ( number(A) -> true ; arith_arg(A) ), Out is ceil(A).
'floor-math'(A, Out)  :- ( number(A) -> true ; arith_arg(A) ), Out is floor(A).
'round-math'(A, Out)  :- ( number(A) -> true ; arith_arg(A) ), Out is round(A).
'sin-math'(A, Out)  :- ( number(A) -> true ; arith_arg(A) ), Out is sin(A).
'cos-math'(A, Out)  :- ( number(A) -> true ; arith_arg(A) ), Out is cos(A).
'tan-math'(A, Out)  :- ( number(A) -> true ; arith_arg(A) ), Out is tan(A).
'asin-math'(A, Out) :- ( number(A) -> true ; arith_arg(A) ), Out is asin(A).
'acos-math'(A, Out) :- ( number(A) -> true ; arith_arg(A) ), Out is acos(A).
'atan-math'(A, Out) :- ( number(A) -> true ; arith_arg(A) ), Out is atan(A).
'isnan-math'(A, Out) :- ( number(A) -> true ; arith_arg(A) ), ( A =:= A -> Out = false ; Out = true ).
'isinf-math'(A, Out) :- ( number(A) -> true ; arith_arg(A) ), ( ( A =:= 1.0Inf ; A =:= -1.0Inf ) -> Out = true ; Out = false ).
'min-atom'(List, Out) :- non_list(List), !, Out = [].
%Partial lists keep the library error instead of being completed by the check:
'min-atom'(List, Out) :- ( is_list(List) -> List = [H|T], arith_num(H), num_min(T, H, Out) ; min_list(List, Out) ).
'max-atom'(List, Out) :- non_list(List), !, Out = [].
'max-atom'(List, Out) :- ( is_list(List) -> List = [H|T], arith_num(H), num_max(T, H, Out) ; max_list(List, Out) ).
%After SWI's native list check, check each element while folding, in library(lists)' argument order:
arith_num(A) :- ( number(A) -> true ; arith_arg(A) ).
num_min([], Min, Min).
num_min([H|T], Min0, Min) :- ( number(H) -> true ; arith_arg(H) ), Min1 is min(H, Min0), num_min(T, Min1, Min).
num_max([], Max, Max).
num_max([H|T], Max0, Max) :- ( number(H) -> true ; arith_arg(H) ), Max1 is max(H, Max0), num_max(T, Max1, Max).

%%% Random Generators: %%%
'random-int'(Min, Max, Result) :- random_between(Min, Max, Result).
'random-int'('&rng', Min, Max, Result) :- random_between(Min, Max, Result).
'random-float'(Min, Max, Result) :- ( number(Min), number(Max) -> true ; arith_arg(Min), arith_arg(Max) ), random(R), Result is Min + R * (Max - Min).
'random-float'('&rng', Min, Max, Result) :- ( number(Min), number(Max) -> true ; arith_arg(Min), arith_arg(Max) ), random(R), Result is Min + R * (Max - Min).
:- nb_getval(petta_loader_optimise, Optimise), set_prolog_flag(optimise, Optimise),
   nb_delete(petta_loader_optimise).

%%% Boolean Logic: %%%
bool(true).
bool(false).
and(A,B,C) :- bool(A), bool(B), ( A == true -> C = B ; A == false -> C = false ).
or(A,B,C) :- bool(A), bool(B), ( A == true -> C = true ; A == false -> C = B ).
not(A,B) :- bool(A), ( A == true -> B = false ; A == false -> B = true ).
xor(A,B,C) :- bool(A), bool(B), ( A == B -> C = false ; C = true ).
implies(A,B,C) :- bool(A), bool(B), ( A == true -> ( B == true  -> C = true ; B == false -> C = false )
                                                 ; A == false -> C = true ).

%%% Nondeterminism: %%%
superpose(L,X) :- member(X,L).
empty(_) :- fail.

%%% Lists / Tuples: %%%
'cons-atom'(H, T, [H|T]).
'decons-atom'([H|T], [H|[T]]).
'first-from-pair'([A, _], A).
first([A, _], A).
'second-from-pair'([_, A], A).
'unique-atom'(A, B) :- non_list(A), !, B = [].
'unique-atom'(A, B) :- list_to_set(A, B).

%%% Alpha-equivalence unique atom %%%
'alpha-unique-atom'(A, B) :- non_list(A), !, B = [].
'alpha-unique-atom'(A, B) :- alpha_list_to_set(A, B).

alpha_list_to_set(List, Set) :-
    empty_assoc(Seen0),
    alpha_list_to_set_assoc(List, Seen0, Set).

alpha_list_to_set_assoc([], _, []).
alpha_list_to_set_assoc([H|T], SeenIn, R) :-
    copy_term(H, HCopy),
    numbervars(HCopy, 0, _),
    term_hash(HCopy, Key),
    ( get_assoc(Key, SeenIn, _) ->
        alpha_list_to_set_assoc(T, SeenIn, R)
    ;
        put_assoc(Key, SeenIn, true, SeenOut),
        R = [H|RT],
        alpha_list_to_set_assoc(T, SeenOut, RT)
    ).

%A term that can never become a list, no matter how it gets instantiated:
non_list(X) :- atomic(X), X \== [].
non_list(X) :- compound(X), X \= [_|_].

'sort-atom'(List, Sorted) :- non_list(List), !, Sorted = [].
'sort-atom'(List, Sorted) :- msort(List, Sorted).
'size-atom'(List, Size) :- non_list(List), !, Size = [].
'size-atom'(List, Size) :- length(List, Size).
'car-atom'([H|_], H) :- !.
'car-atom'(_, []).
'cdr-atom'([_|T], T) :- !.
'cdr-atom'(_, []).
decons([H|T], [H|[T]]).
cons(H, T, [H|T]).
'index-atom'(_, Index, _) :- nonvar(Index), \+ integer(Index), !, fail.
'index-atom'(List, Index, Elem) :- nth0(Index, List, Elem).
member(X, L, true) :- member(X, L).
'is-member'(X, List, true) :- member(X, List).
'is-member'(X, List, false) :- \+ member(X, List).

member_alpha(X, [H|_]) :- (var(X) -> var(H) ; true), X = H, !.
member_alpha(X, [_|T]) :- member_alpha(X, T).

'is-alpha-member'(X, List, true) :- member_alpha(X, List), !.
'is-alpha-member'(_, _, false).

'exclude-item'(A, L, R) :- exclude(==(A), L, R).

%Multisets:
'subtraction-atom'([], _, []).
'subtraction-atom'([H|T], B, Out) :- ( select(H, B, BRest) -> 'subtraction-atom'(T, BRest, Out)
                                                            ; Out = [H|Rest],
                                                              'subtraction-atom'(T, B, Rest) ).
'union-atom'(A, B, Out) :- append(A, B, Out).
'intersection-atom'(A, B, Out) :- ( non_list(A) ; non_list(B) ), !, Out = [].
'intersection-atom'([], _, []).
'intersection-atom'([H|T], B, Out) :- ( select(H, B, BRest) -> Out = [H|Rest],
                                                              'intersection-atom'(T, BRest, Rest)
                                                            ; 'intersection-atom'(T, B, Out) ).

%%% Type system: %%%
get_function_type([F|Args], T) :- nonvar(F), match('&self', [':',F,[->|Ts]], _, _),
                                  append(As,[T0],Ts),
                                  checked_args(As, Args, As1, Args1),
                                  T = T0,
                                  maplist('get-type',Args1,As1).
%As in typed calls, an argument declared %Undefined% is not checked. These parameters are found
%before the requested type or another argument can bind a type variable to %Undefined%:
checked_args([], [], [], []).
checked_args([A|As], [X|Xs], Bs, Ys) :- ( A == '%Undefined%' -> Bs = Bs1, Ys = Ys1 ; Bs = [A|Bs1], Ys = [X|Ys1] ),
                                        checked_args(As, Xs, Bs1, Ys1).

:- dynamic 'get-type'/2.
%An unbound request takes each type of the value, or %Undefined% if it has none. %Undefined% is
%confirmed only for a value without types or with %Undefined% among them:
'get-type'(X, T) :- ( var(T) -> ( get_type_candidate(X, T0) *-> T = T0 ; T = '%Undefined%' )
                    ; T == '%Undefined%' -> ( \+ get_type_candidate(X, _) -> true ; get_type_candidate(X, T) )
                    ; get_type_candidate(X, T) ).
%An intrinsic kind is chosen before the requested type is compared:
get_type_candidate(X, T) :- number(X), !, T = 'Number'.
get_type_candidate(X, _) :- var(X), !.
get_type_candidate(X, T) :- string(X), !, T = 'String'.
get_type_candidate(true, T) :- !, T = 'Bool'.
get_type_candidate(false, T) :- !, T = 'Bool'.
get_type_candidate(X, T) :- get_function_type(X,T).
get_type_candidate(X, T) :- \+ get_function_type(X, _),
                            is_list(X),
                            maplist('get-type', X, T).
get_type_candidate(X, T) :- match('&self', [':',X,T], T, _).

'space-get-type'(Space, X, T) :-
    ( space_get_type_candidate(Space, X, T) *-> true ; T = '%Undefined%' ).
space_get_type_candidate(_, X, 'Number') :- number(X), !.
space_get_type_candidate(_, X, _) :- var(X), !.
space_get_type_candidate(_, X, 'String') :- string(X), !.
space_get_type_candidate(_, true, 'Bool') :- !.
space_get_type_candidate(_, false, 'Bool') :- !.
space_get_type_candidate(Space, X, T) :- space_get_function_type(Space, X, T).
space_get_type_candidate(Space, X, T) :-
    \+ space_get_function_type(Space, X, _),
    is_list(X),
    maplist('space-get-type'(Space), X, T).
space_get_type_candidate(Space, X, T) :- match(Space, [':',X,T], T, _).

space_get_function_type(Space, [F|Args], T) :- nonvar(F),
                                               match(Space, [':',F,[->|Types]], _, _),
                                               append(ArgTypes, [T], Types),
                                               maplist('space-get-type'(Space), Args, ArgTypes).
'get-metatype'(X, 'Variable') :- var(X), !.
'get-metatype'(X, 'Grounded') :- number(X), !.
'get-metatype'(X, 'Grounded') :- string(X), !.
'get-metatype'(true,  'Grounded') :- !.
'get-metatype'(false, 'Grounded') :- !.
'get-metatype'(X, 'Grounded') :- atom(X), created_space(X), !.
'get-metatype'(X, 'Grounded') :- atom(X), fun(X), !.  % e.g., '+' is a registered fun/1
'get-metatype'(X, 'Expression') :- is_list(X), !.     % e.g., (+ 1 2), (a b)
'get-metatype'(X, 'Symbol') :- atom(X), !.            % e.g., a

'is-var'(A,R) :- var(A) -> R=true ; R=false.
'is-ground'(A,R) :- ground(A) -> R=true ; R=false.
'is-expr'(A,R) :- is_list(A) -> R=true ; R=false.
'is-space'(A,R) :- atom(A), atom_concat('&', _, A) -> R=true ; R=false.

%%% Diagnostics / Testing: %%%
'println!'(Arg, true) :- swrite(Arg, RArg),
                         format('~w~n', [RArg]).

'readln!'(Out) :- read_line_to_string(user_input, Str),
                  sread(Str, Out).

test(A,B,true) :- (A =@= B -> E = '✅' ; E = '❌'),
                  swrite(A, RA),
                  swrite(B, RB),
                  format("is ~w, should ~w. ~w ~n", [RA, RB, E]),
                  (A =@= B -> true ; halt(1)).

assert(Goal, true) :- ( call(Goal) -> true
                                    ; swrite(Goal, RG),
                                      format("Assertion failed: ~w~n", [RG]),
                                      halt(1) ).

%%% Time Retrieval: %%%
'current-time'(Time) :- get_time(Time).
'format-time'(Format, TimeString) :- get_time(Time), format_time(atom(TimeString), Format, Time).

%%% Python bindings: %%%
% janus converts Python booleans to @(true)/@(false); normalize them to the
% language booleans so py-call results compose with if, and, or, ==.
py_bool_norm('@'(true), true) :- !.
py_bool_norm('@'(false), false) :- !.
py_bool_norm(R, R).
'py-call'(SpecList, Result) :- 'py-call'(SpecList, Result, [py_string_as(string)]).
'py-call'([Spec|Args], Result, Opts) :- ( string(Spec) -> atom_string(A, Spec) ; A = Spec ),
                                        must_be(atom, A),
                                        ( sub_atom(A, 0, 1, _, '.')         % ".method"
                                          -> sub_atom(A, 1, _, 0, Fun),
                                             Args = [Obj|Rest],
                                             ( py_is_object(Obj)            % on a Python object reference
                                               -> ( Rest == []
                                                    -> compound_name_arguments(Meth, Fun, [])
                                                     ; Meth =.. [Fun|Rest] ),
                                                  py_call(Obj:Meth, R0, Opts), py_bool_norm(R0, Result)
                                                ; py_call(builtins:type(Obj), Ty), % on a converted value (str, int, ...)
                                                  Call =.. [Fun, Obj|Rest],
                                                  py_call(Ty:Call, R0, Opts), py_bool_norm(R0, Result) )
                                           ; atomic_list_concat([M,F], '.', A) % "mod.fun"
                                             -> ( Args == []
                                                  -> compound_name_arguments(Call0, F, [])
                                                   ; Call0 =.. [F|Args] ),
                                                py_call(M:Call0, R0, Opts), py_bool_norm(R0, Result)
                                              ; ( Args == []                      % bare "fun"
                                                  -> compound_name_arguments(Call0, A, [])
                                                   ; Call0 =.. [A|Args] ),
                                                py_call(builtins:Call0, R0, Opts), py_bool_norm(R0, Result) ).

%%% States: %%%
'bind!'(A, ['new-state', B], C) :- 'change-state!'(A, B, C).
'change-state!'(Var, Value, true) :- nb_setval(Var, Value).
'get-state'(Var, Value) :- nb_getval(Var, Value).

%%% Eval: %%%
eval(C, Out) :- translate_expr(C, Goals, Out),
                call_goals(Goals).

eval(C, Space, Out) :- translate_expr_in_space(Space, C, Goals, Out),
                       call_goals(Goals).

call_goals([]).
call_goals([G|Gs]) :- call(G), 
                      call_goals(Gs).

%%% Higher-Order Functions: %%%
'foldl-atom'([], Acc, _Func, Acc).
'foldl-atom'([H|T], Acc0, Func, Out) :- reduce([Func,Acc0,H], Acc1),
                                        'foldl-atom'(T, Acc1, Func, Out).

'map-atom'([], _Func, []).
'map-atom'([H|T], Func, [R|RT]) :- reduce([Func,H], R),
                                   'map-atom'(T, Func, RT).

'filter-atom'([], _Func, []).
'filter-atom'([H|T], Func, Out) :- ( reduce([Func,H], true) -> Out = [H|RT]
                                                             ; Out = RT ),
                                   'filter-atom'(T, Func, RT).

%%% Prolog interop: %%%
argv(K, Arg) :- current_prolog_flag(argv, Argv), nth0(K, Argv, A), ( atom_number(A, N) -> Arg = N ; Arg = A ).
import_prolog_function(N, true) :- register_fun(N).
'Predicate'([F|Args], Term) :- Term =.. [F|Args].
callPredicate(G, true) :- call(G).
assertzPredicate(G, true) :- assertz(G).
assertaPredicate(G, true) :- asserta(G).
retractPredicate(G, true) :- retract(G), !.
retractPredicate(_, false).

%%% Library / Import: %%%
ensure_metta_ext(Path, Path) :- file_name_extension(_, metta, Path), !.
ensure_metta_ext(Path, PathWithExt) :- file_name_extension(Path, metta, PathWithExt).

current_working_dir(Base) :- working_dir(Base), !.
current_working_dir(Base) :- absolute_file_name('.', Base, [file_type(directory)]).

import_file_string(File, SFile) :- string(File), !, SFile = File.
import_file_string(File, SFile) :- atom_string(File, SFile).

python_import_file(File) :- import_file_string(File, SFile),
                            file_name_extension(_, py, SFile).

resolve_existing_import_path(Base, RequestedPath, CanonPath) :-
    absolute_file_name(RequestedPath, CanonPath,
                       [relative_to(Base), access(read), file_errors(fail)]), !.

throw_missing_import(File) :-
    throw(error(existence_error(source_sink, File), context('import!', File))).

resolve_metta_import_path(File, CanonPath) :-
    import_file_string(File, SFile),
    \+ python_import_file(SFile),
    current_working_dir(Base),
    ensure_metta_ext(SFile, RequestedPath),
    ( resolve_existing_import_path(Base, RequestedPath, CanonPath)
      -> true
       ; throw_missing_import(File) ).

resolve_python_import_path(File, CanonPath) :-
    import_file_string(File, SFile),
    python_import_file(SFile),
    current_working_dir(Base),
    ( resolve_existing_import_path(Base, SFile, CanonPath)
      -> true
       ; throw_missing_import(File) ).

:- dynamic metta_import_state/3.

% A loading or active entry breaks cycles; a loaded entry makes later imports no-ops.
% Failed loads remove their loading entry, but may leave partial state; retrying a
% failed import in the same runtime is unsupported.
claim_import(Space, CanonPath, skip) :- metta_import_state(Space, CanonPath, loaded), !.
claim_import(Space, CanonPath, skip) :- metta_import_state(Space, CanonPath, loading), !.
claim_import(Space, CanonPath, skip) :- active_metta_load(Space, CanonPath), !.
claim_import(Space, CanonPath, load) :- assertz(metta_import_state(Space, CanonPath, loading)).

clear_import_state(Space, CanonPath) :- retractall(metta_import_state(Space, CanonPath, _)).

mark_import_loaded(Space, CanonPath) :- clear_import_state(Space, CanonPath),
                                        assertz(metta_import_state(Space, CanonPath, loaded)).

run_new_import(Space, CanonPath, Goal) :-
    catch(( once(Goal)
            -> mark_import_loaded(Space, CanonPath)
             ; clear_import_state(Space, CanonPath), fail ),
          Error,
          ( clear_import_state(Space, CanonPath), throw(Error) )).

import_once(Space, CanonPath, Goal) :- claim_import(Space, CanonPath, Action),
                                       ( Action = skip -> true
                                                       ; run_new_import(Space, CanonPath, Goal) ).

'import!'(Space, File, true) :- importer_helper(Space, File).
importer_helper(Space, File) :-
    ( python_import_file(File)
      -> resolve_python_import_path(File, CanonPath),
         file_directory_name(CanonPath, Dir),
         file_base_name(CanonPath, BaseName),
         file_name_extension(ModuleName, _, BaseName),
         import_once(Space, CanonPath,
                     ( py_call(sys:path:append(Dir), _),
                       py_call(builtins:'__import__'(ModuleName), _) ))
       ; resolve_metta_import_path(File, CanonPath),
         import_once(Space, CanonPath, load_metta_file(CanonPath, _, Space)) ).

:- dynamic translator_rule/1.
'add-translator-rule!'(HV, true) :- ( translator_rule(HV)
                                      -> true ; assertz(translator_rule(HV)) ).

'remove-translator-rule!'(HV, true) :- retractall(translator_rule(HV)).

%%% Registration: %%%
:- dynamic fun/1, arity/2.
register_fun(N) :- fun(N), !.
%Arities are registered in ascending order: the order current_predicate/1
%enumerates them in depends on how many atoms the process created before.
register_fun(N) :- assertz(fun(N)),
                   findall(Arity, (current_predicate(N/Arity), \+ (current_op(_, _, N), Arity =< 2)), Arities0),
                   sort(Arities0, Arities),
                   forall(member(Arity, Arities),
                          (arity(N, Arity) -> true ; assertz(arity(N, Arity)))).
:- maplist(register_fun, [superpose, empty, '+','-','*','/', '%', min, max, 'change-state!', 'get-state', 'bind!',
                          '<','>','@<', '@>', '==', '!=', '=', '=?', '<=', '>=', '@<=', '@>=', and, or, xor, implies, not, sqrt, exp, log, cos, sin,
                          'first-from-pair', 'second-from-pair', 'car-atom', 'cdr-atom', 'unique-atom', 'alpha-unique-atom',
                          repr, repra, parse, 'println!', 'readln!', test, assert, 'mm2-exec', atom_concat, atom_chars, copy_term, term_hash,
                          foldl, first, last, append, length, 'size-atom', sort, msort, member, 'is-member', 'is-alpha-member', 'exclude-item', list_to_set, maplist, eval, reduce, 'import!',
                          'add-atom', 'remove-atom', 'get-atoms', 'new-space', match, 'is-var', 'is-ground', 'is-expr', 'is-space', 'get-mettatype',
                          decons, 'decons-atom', 'py-call', 'get-type', 'get-metatype', '=alpha', concat, sread, cons, reverse,
                          '#+','#-','#*','#div','#//','#mod','#min','#max','#<','#>','#=','#\\=','set_hook',
                          'union-atom', 'cons-atom', 'intersection-atom', 'subtraction-atom', 'index-atom', id,
                          'pow-math', 'sqrt-math', 'sort-atom','abs-math', 'log-math', 'trunc-math', 'ceil-math',
                          'floor-math', 'round-math', 'sin-math', 'cos-math', 'tan-math', 'asin-math','random-int','random-float',
                          'acos-math', 'atan-math', 'isnan-math', 'isinf-math', 'min-atom', 'max-atom',
                          'foldl-atom', 'map-atom', 'filter-atom','current-time','format-time', library, exists_file,
                          import_prolog_function, 'Predicate', callPredicate, assertaPredicate, assertzPredicate, retractPredicate,
                          'add-translator-rule!', 'remove-translator-rule!', argv]).
