%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Traveling Tournament Problem with Predefined Venues
%
% Compact single round robin schedule minimizing total travel distance
% The venue of each game has already been decided
% Specialized for CIRC instances (circular distances)
%
% MiniZinc Challenge model (traveling-tppv, 2014-2022) rewritten with one cost_regular per team:
% the automaton state is the home/away run of the original regular constraint together with the
% team's current location, and a transition costs the distance travelled to the next game.
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

% a team cannot play against itself
constraint forall (i in Teams, k in Rounds) (opponent[i,k] != i);

% in round k, i plays j means j plays i
constraint forall (i in Teams, k in Rounds) (opponent[opponent[i,k],k] = i);

% for each team i, all opponents are different
constraint forall (i in Teams) (alldifferent([opponent[i,k] | k in Rounds]));

% for each round k, all opponents are different (implied constraint)
constraint forall (k in Rounds) (alldifferent([opponent[i,k] | i in Teams]));

% symmetry breaking: distances are symmetric so reversing the rounds yields a schedule of same cost
constraint (opponent[1,1] < opponent[1,nbRounds]);

% Run automaton of the original model (at most 3 consecutive home or away games).
int: nbRuns = 7;
array[1..nbRuns,1..2] of int: delta =
  [| 2, 5
   | 3, 5
   | 4, 5
   | 0, 5
   | 2, 6
   | 2, 7
   | 2, 0 |];

% cost_regular per team i on the word opponent[i,1..nbRounds] ++ [i].
% A state is (run r, current location l), numbered (r-1)*nbTeams + l; state done = nbRuns*nbTeams + 1.
% Playing j moves the team to i (home) or to j (away) and costs the distance from l.
% The final letter i (only allowed as the last letter, it leads to done) is the trip back home.
int: done = nbRuns*nbTeams + 1;
function int: st(int: r, int: l) = (r-1)*nbTeams + l;

array[Teams] of var 0..(nbTeams div 2)*(nbRounds+1): teamTravel;

constraint forall (i in Teams) (
  let {
    array[1..done, Teams] of int: d = array2d(1..done, Teams,
      [ if q == done then 0
        else let { int: r = (q-1) div nbTeams + 1; int: l = (q-1) mod nbTeams + 1 } in
          if j == i then done
          elseif delta[r, pv[i,j]] == 0 then 0
          elseif pv[i,j] == 1 then st(delta[r,1], i)
          else st(delta[r,2], j) endif
        endif | q in 1..done, j in Teams ]);
    array[1..done, Teams] of int: c = array2d(1..done, Teams,
      [ if q == done then 0
        else let { int: l = (q-1) mod nbTeams + 1 } in
          if j == i then distance[l,i]
          elseif pv[i,j] == 1 then distance[l,i]
          else distance[l,j] endif
        endif | q in 1..done, j in Teams ]);
  } in
  cost_regular([opponent[i,k] | k in Rounds] ++ [i], done, nbTeams, d, st(1,i), {done}, c, teamTravel[i])
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
int: maxObj = sum(i in Teams)(ub(teamTravel[i]));
var 0..maxObj: objective;
constraint objective = sum (i in Teams) (teamTravel[i]);

solve
    :: int_search([opponent[i, j] | i in Teams, j in Rounds], input_order, indomain_min, complete)
    minimize objective;

output [
    "opponent = array2d(", show(Teams), ", ", show(Rounds), ", ", show(opponent), ");\n",
    "objective = ", show(objective), ";\n"
];
