:- module(type_obligations, [cell/2, watch/4, restore/3, release/2]).

% One evidence cell per program variable. Contracts share the cell, so binding
% a heavily used variable does not repeatedly inspect the same value.
cell(V,Cell) :-
    (get_attr(V,type_obligations,state(Stored,_)) -> Cell=Stored
    ;mark(Cell),put_attr(V,type_obligations,state(Cell,[]))).
watch(V,Cell,Frame,Kind) :- cell(V,Cell),get_attr(V,type_obligations,state(Cell,Before)),
    merge([watch(Frame,Kind)],Before,Next),put_attr(V,type_obligations,state(Cell,Next)).

% Marking private cells preserves their sharing through native attribute copies.
mark(Cell) :- (var(Cell)->put_attr(Cell,type_obligations,cell_marker);true).
attr_unify_hook(cell_marker,V) :- !,
    (var(V),\+get_attr(V,type_obligations,_)->put_attr(V,type_obligations,cell_marker);true).
attr_unify_hook(state(Cell,Watching),Value) :-
    (var(Value) ->
       (get_attr(Value,type_obligations,state(Other,Before)) -> Cell=Other,merge(Watching,Before,Next)
       ;Next=Watching),put_attr(Value,type_obligations,state(Cell,Next))
    ;acyclic_term(Value),
     (member(watch(Frame,_),Watching),arg(1,Frame,Options),Options\==[] ->
        user:type_capture(Value,Evidence),Cell=Evidence,maplist(notify(Value,Evidence),Watching)
     ;user:type_finite(Value)) ).
notify(_,_,watch(Frame,_)) :- arg(1,Frame,[]),!.
notify(_,Evidence,watch(Frame,Kind)) :-
    (Kind==passive,arg(2,Frame,input)->true;user:type_validate(Frame)),
    user:type_arm_evidence(Frame,Evidence,Kind).

merge([],Rest,Rest).
merge([Watch|Watches],Before,Next) :-
    (member(Same,Before),same_watch(Same,Watch) -> More=Before;More=[Watch|Before]),
    merge(Watches,More,Next).

same_watch(watch(F,K),watch(G,L)) :- K==L,arg(3,F,I),arg(3,G,J),I==J.

% A discharged frame imposes only finiteness. Remove both kinds of watcher;
% other frames and foreign attributes on the variable remain untouched.
release(Frame,V) :-
    (get_attr(V,type_obligations,state(Cell,Before)) ->
       exclude(frame_watch(Frame),Before,Rest),
       (Rest==[]->del_attr(V,type_obligations);put_attr(V,type_obligations,state(Cell,Rest)))
    ;true),user:type_watch_finite(V).
frame_watch(Frame,watch(Other,_)) :- arg(3,Frame,I),arg(3,Other,J),I==J.

restore(V,Cell,Watching) :- mark(Cell),
    (var(V) -> (get_attr(V,type_obligations,state(Other,Before)) -> Cell=Other,merge(Watching,Before,Next)
               ;Next=Watching),put_attr(V,type_obligations,state(Cell,Next))
    ;attr_unify_hook(state(Cell,Watching),V)).
attribute_goals(V) --> {get_attr(V,type_obligations,cell_marker)},!,[].
attribute_goals(V) -->
    {get_attr(V,type_obligations,state(Cell,Watching))},
    [type_obligations:restore(V,Cell,Watching)].
