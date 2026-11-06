:- module(type_obligations, [cell/2, watch/4, recorded/1, restore/3, release/2]).

% One evidence cell per program variable. Contracts share the cell, so binding
% a heavily used variable does not repeatedly inspect the same value.
% Attribute state(Cell, Watches) belongs to a program variable. Cell is a
% private attributed variable until binding captures evidence into it;
% Watches contains watch(Frame, active/passive), deduplicated by frame identity.
% The separate cell_marker preserves this sharing under native term copying.
% Updates are backtrackable: failed branches must restore both cells and watches.
cell(V,Cell) :-
    (get_attr(V,type_obligations,state(Stored,_)) -> Cell=Stored
    ;mark(Cell),put_attr(V,type_obligations,state(Cell,[]))).
watch(V,Cell,Frame,Kind) :-
    ( get_attr(V, type_obligations, state(Cell,Before)) -> true
    ; mark(Cell), Before = []
    ),
    arg(3, Frame, Identity),
    ( has_watch(Before, Identity, Kind) -> true
    ; put_attr(V, type_obligations, state(Cell,[watch(Frame,Kind)|Before]))
    ).
has_watch([watch(Frame,Kind0)|_],Identity,Kind) :-
    Kind0==Kind,arg(3,Frame,Other),Identity==Other,!.
has_watch([_|Rest],Identity,Kind) :- has_watch(Rest,Identity,Kind).
% A running call keeps its watchers until it returns. A passive nested input
% may borrow that recorder, but must arm its own unresolved checks at exit.
recorded(V) :- get_attr(V,type_obligations,state(_,Watching)),
    member(watch(Frame,_),Watching),arg(2,Frame,input),arg(1,Frame,Options),Options\==[],!.

% Marking private cells preserves their sharing through native attribute copies.
mark(Cell) :- (var(Cell)->put_attr(Cell,type_obligations,cell_marker);true).
attr_unify_hook(cell_marker,V) :- !,
    (var(V),\+get_attr(V,type_obligations,_)->put_attr(V,type_obligations,cell_marker);true).
attr_unify_hook(state(Cell,Watching),Value) :-
    (var(Value) ->
       (get_attr(Value,type_obligations,state(Other,Before)) -> Cell=Other,merge(Watching,Before,Next)
       ;Next=Watching),put_attr(Value,type_obligations,state(Cell,Next))
    ;(member(watch(Frame,_),Watching),arg(1,Frame,Options),Options\==[] ->
        acyclic_term(Value),user:type_capture(Value,Evidence),Cell=Evidence,
        term_variables(Value,Vars),maplist(notify(Vars),Watching)
     ;true) ).
notify(_,watch(Frame,_)) :- arg(1,Frame,[]),!.
notify(Vars,watch(Frame,Kind)) :-
    (Kind==passive,arg(2,Frame,input)->true;user:type_validate(Frame)),
    maplist(user:type_watch_value(Frame,Kind),Vars).

merge([],Rest,Rest).
merge([Watch|Watches],Before,Next) :-
    (member(Same,Before),same_watch(Same,Watch) -> More=Before;More=[Watch|Before]),
    merge(Watches,More,Next).

same_watch(watch(F,K),watch(G,L)) :- K==L,arg(3,F,I),arg(3,G,J),I==J.

% A discharged frame imposes nothing further. Remove both kinds of watcher;
% other frames and foreign attributes on the variable remain untouched.
release(Frame,V) :-
    (get_attr(V,type_obligations,state(Cell,Before)) ->
       exclude(frame_watch(Frame),Before,Rest),
       (Rest==[]->del_attr(V,type_obligations);put_attr(V,type_obligations,state(Cell,Rest)))
    ;true).
frame_watch(Frame,watch(Other,_)) :- arg(3,Frame,I),arg(3,Other,J),I==J.

restore(V,Cell,Watching) :- mark(Cell),
    (var(V) -> (get_attr(V,type_obligations,state(Other,Before)) -> Cell=Other,merge(Watching,Before,Next)
               ;Next=Watching),put_attr(V,type_obligations,state(Cell,Next))
    ;attr_unify_hook(state(Cell,Watching),V)).
attribute_goals(V) --> {get_attr(V,type_obligations,cell_marker)},!,[].
attribute_goals(V) -->
    {get_attr(V,type_obligations,state(Cell,Watching))},
    [type_obligations:restore(V,Cell,Watching)].
