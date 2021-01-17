
:- discontiguous(ally/5).
:- discontiguous(ethan/4).
:- dynamic ethan/4.
:- dynamic goalsTarget/1.
:- dynamic ally/5.
:- dynamic capacity/1.
:- include('KB').
%convert members_loc([[X,Y],[X,Y]]) to our format of ally(X,Y,CARRY,DROP,Situation).
initAlly([X,Y]):-
assert(ally(X,Y,0,0,s0)).
%convert ethan_loc(X,Y) to our format of ethan(X,Y,Capacity,Situation).
init():- 
ethan_loc(X,Y),
capacity(C),
retractall(ethan),
%Ethan starting position and capacity.
assert(ethan(Y,X,C,s0)),
members_loc(AllyList),
length(AllyList,Size),
retractall(goalsTarget),
%number of allies to save
assert(goalsTarget(Size)),
%allies starting positions
maplist(initAlly,AllyList).
goal(S):-
%If there are no allies to save then the goal query is the intial situation s0. If we have 1 ally so save then the goal is saving 1 ally in the form of 2 allies where X can be equal to X1 and Y can be equal to X2, we if we have to save 2 allies the goal query would be 2 allies and X not equal X1 OR Y not equal Y1.
	solve(((goalsTarget(0),submarine(SubX,SubY),ethan(SubY,SubX,_,S));
	ally(X,Y,0,1,S),ally(X1,Y1,0,1,S),
	submarine(SubX,SubY),ethan(SubY,SubX,_,S),
	(
	(
	((goalsTarget(2))
	,((X1\=X);(Y1\=Y)));((goalsTarget(1)
	)))))).
	
%%checks if the cell is valid
isValid(X, Y):-
    \+ (X < 0),
    \+ (Y < 0).
% ETHAN SUCCESSOR STATE AXIOMS (SUCESSOR AXIOM 1)
%-----------------------------
ethan(Col,Row, CurrentCapacity, result(Action, Situation)):-
%-----------------------------
%If action was carry and there was an ally in the same cell as ethan who is not carried or dropped then decrease capacity by 1.
	((Action=carry),
    ethan(Col, Row, OldCapacity, Situation),
    CurrentCapacity is OldCapacity - 1,
    \+ (CurrentCapacity = -1),
    (ally(Row, Col, 0,0, Situation))
	);
	
%-----------------------------
% If the action was drop and ethan was standing on the submarine and there exists an ally who was carried then that ally would be dropped so increase ethan capacity back to maximum.
	((Action=drop),
	ethan(Col, Row, _, Situation),
	ally(_,_,1,0,Situation),
    capacity(CurrentCapacity),
    submarine(Row, Col)
	);
	
%-----------------------------
%Move Actions, check out of bounds of the grid then move.
    isValid(Col,Row),
    ColDec is Col - 1,
    ColInc is Col + 1,
    RowInc is Row + 1,
    RowDec is Row - 1,
	
    ((Action = right, ethan(ColDec, Row, CurrentCapacity, Situation));
     (Action = left, ethan(ColInc, Row, CurrentCapacity, Situation));
     (Action = up, ethan(Col, RowInc, CurrentCapacity, Situation));
     (Action = down, ethan(Col, RowDec, CurrentCapacity, Situation))).
	 
%-----------------------------
%-----------------------------
% ALLY SUCCESSOR STATE AXIOMS (SUCESSOR AXIOM 2)
%-----------------------------
%3rd Input is carried boolean, 4th input is dropped boolean.
ally(Row, Col, Carry,Drop, result(Action, Situation)):-
%-----------------------------
% An ally is not carried in the result situation if the ally was not carried in the previous situation and the action is not a carry. In other words, only carry can affect a non carried ally.
	((Carry=0,Drop=0),
    ally(Row, Col, 0,0, Situation),
    ((Action = right); (Action = left); (Action = up); (Action = down); (Action = drop)));
	
%-----------------------------
%An ally is not carried in the result of the situation if the ally was alive in the previous situation and the actionwas carry but ethan was not standing with the ally on the same cell or ethan had no capacity.
	((Carry=0,Drop=0,Action=carry),
ally(Row, Col, 0,0, Situation),
    \+ (ethan(Col, Row, _, Situation);ethan(Col, Row, 0, Situation))
	);
	
%-----------------------------
%If the ally was not carried in the previous situation and Ethan was standing on the same cell and the action is a carry and ethan has enough space >0.
	((Carry=1,Drop=0,Action=carry),
	 ally(Row, Col, 0,0, Situation),
    (ethan(Col, Row, OldCapacity1, Situation), \+ (OldCapacity1 = 0))
	);
	
%-----------------------------
%If the ally was not dropped in the previous situation and the current action is drop and ethan is standing on the submarine
	((Carry=0,Drop=1,Action=drop),
	submarine(X,Y),
	ethan(Y,X,_,Situation),
    ally(Row, Col, 1,0, Situation)
	);
	
%-----------------------------
%If an ally was carried in the previous situation then the ally remains carried regardless of the action, unless the action is a drop.
	((Carry=1,Drop=0,\+Action=drop),
	    ally(Row, Col, 1,0, Situation)
	);
	
%-----------------------------
%If an ally was dropped in the previous situation then the ally remains dropped regardless of the action.
	((Carry=0,Drop=1),
	    ally(Row, Col, 0,1, Situation)
	).
	
%-----------------------------
%-----------------------------
	
%%Solve Predicates.
solve(Query):-
%call init function which initializes custom facts
init(),
%call init dls with depth limit 1 and query to satisfy.
  dls(Query,1).
dls(Query, Limit):-
%This only returns after either finding a solution at depth limit or failing to find a solution at depth limit. If it failed then when calling goalTest the currentDepth would be == depth limit if it did not fail then current depth would be less than depth limit.
  call_with_depth_limit(Query,Limit,R),
  goalTest(Query,Limit,R).
%%If current depth is not equal to depth limit then we found a solution
goalTest(_, _, CurrentDepth):-
  CurrentDepth \= depth_limit_exceeded.
%%If current depth == depth limit then solution not found so increment depth limit
goalTest(Query, Limit, CurrentDepth):-
%if current depth == depth limit
  CurrentDepth == depth_limit_exceeded,
  NewDepth is Limit + 1,
  %call dls again with new depth and same query.
  dls(Query,NewDepth).
