%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Traveling Tournament Problem with Predefined Venues
%
% Compact single round robin schedule minimizing total travel distance
% The venue of each game has already been decided
% Specialized for CIRC instances (circular distances)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

include "globals.mzn";

int: nbTeams;
int: nbRounds = nbTeams-1;

set of int: Teams = 1..nbTeams;
set of int: Rounds = 1..nbRounds;
set of int: Travels = 1..nbRounds+1;

% predefined venue: pv[i][j] = 1 iff i is playing at home against j
array[Teams,Teams] of 1..2: pv; 

% circular distances: for i>=j, distance[i][j]=min{i-j,j-i+nbTeams}
array[Teams,Teams] of int: distance = 
  array2d(Teams,Teams,[ if i>=j then (if i-j < j-i+nbTeams then i-j else j-i+nbTeams endif) 
                                else (if j-i < i-j+nbTeams then j-i else i-j+nbTeams endif) 
                                endif | i,j in Teams]);

% output related
int: digs = ceil(log(10.0,int2float(nbTeams)));

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% decision variables: in round k, team i plays against team opponent[i,k]
array[Teams,Rounds] of var Teams: opponent;

% auxiliary variables: venue[i,k] = 1 iff team i plays at home in round k
array[Teams,Rounds] of var 1..2: venue;
constraint forall (i in Teams, k in Rounds) (venue[i,k] = pv[i,opponent[i,k]]);

% auxiliary variables: travel[i,k] is the distance travelled by team i to go play in round k (includes travelling back home after last round)
array[Teams,Travels] of var 0..(nbTeams div 2): travel;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% a team cannot play against itself
constraint forall (i in Teams, k in Rounds) (opponent[i,k] != i);

% in round k, i plays j means j plays i
constraint forall (i in Teams, k in Rounds) (opponent[opponent[i,k],k] = i);

% for each team i, all opponents are different
constraint forall (i in Teams) (alldifferent([opponent[i,k] | k in Rounds]));

% for each round k, all opponents are different (implied constraint)
constraint forall (k in Rounds) (alldifferent([opponent[i,k] | i in Teams]));

% for each team i, there can be at most 3 consecutive home games and at most 3 consecutive away games
int: nbStates = 7;
set of int: States = 1..nbStates;
array[States,1..2] of int: delta = 
  [| 2, 5
   | 3, 5
   | 4, 5
   | 0, 5
   | 2, 6
   | 2, 7
   | 2, 0 |];
constraint forall (i in Teams) (regular( [venue[i,k] | k in Rounds], nbStates, 2, delta, 1, States));

% symmetry breaking: distances are symmetric so reversing the rounds yields a schedule of same cost
constraint (opponent[1,1] < opponent[1,nbRounds]);

% define travel variables wrt venues of current- and next-round games
constraint forall (i in Teams) (
	(venue[i,1]=1 -> travel[i,1] = 0) /\
	(venue[i,1]=2 -> travel[i,1] = distance[i,opponent[i,1]]) );
constraint forall (i in Teams, k in 1..nbRounds-1) (
	((venue[i,k]=1 /\ venue[i,k+1]=1) -> travel[i,k+1] = 0) /\
	((venue[i,k]=2 /\ venue[i,k+1]=1) -> travel[i,k+1] = distance[opponent[i,k],i]) /\
	((venue[i,k]=1 /\ venue[i,k+1]=2) -> travel[i,k+1] = distance[i,opponent[i,k+1]]) /\
	((venue[i,k]=2 /\ venue[i,k+1]=2) -> travel[i,k+1] = distance[opponent[i,k],opponent[i,k+1]]) );
constraint forall (i in Teams) (
	(venue[i,nbRounds]=1 -> travel[i,nbRounds+1] = 0) /\
	(venue[i,nbRounds]=2 -> travel[i,nbRounds+1] = distance[opponent[i,nbRounds],i]) );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
int: maxObj = sum(i in Teams, k in Travels)(ub(travel[i, k]));
var 0..maxObj: objective; 
constraint objective = sum (i in Teams, k in Travels) (travel[i,k]);

solve 
    :: seq_search([
        int_search([opponent[i, j] | i in Teams, j in Rounds], input_order, indomain_min, complete),
        int_search([venue[i, j] | i in Teams, j in Rounds], input_order, indomain_min, complete),
        int_search([travel[i, j] | i in Teams, j in Travels], first_fail, indomain_min, complete),
    ])
    minimize objective;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
output [
    "%% SCHEDULE\n%% "
] ++ [ 
    if fix(venue[i,k]) == 1 then " " else "@" endif ++
	show_int(digs,opponent[i,k]) ++ " " ++ 
    if k == nbRounds /\ i != nbTeams then "\n%% " else "" endif
| i in Teams, k in Rounds ] ++ ["\n"] ++ [
    "opponent = array2d(", show(Teams), ", ", show(Rounds), ", ", show(opponent), ");\n",
    "venue = array2d(", show(Teams), ", ", show(Rounds), ", ", show(venue), ");\n",
    "travel = array2d(", show(Teams), ", ", show(Travels), ", ", show(travel), ");\n",
    "objective = ", show(objective), ";\n"
];
