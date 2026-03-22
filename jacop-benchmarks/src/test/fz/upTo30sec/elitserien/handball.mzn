%   Elitserien handboll -- generic model, needs specific:
%   - sets of teams for N and S divisions
%   - which teams to form complementary divisions
%   - derby sets
%   - venue unavailabilities
% 
%   Jeff Larson <jeffreyl@kth.se>
%   Mats Carlsson <matsc@sics.se>

% * 14-team league

% * Form 2 divisions which hold a single round-robin tournament

% 1. Each 7-team division must hold a SRRT to start the season.

% 2. This must be followed by two SRRTs between the entire league, the
%    second SRRT being a mirror of the first.

% 3. There must be a minimum number of breaks in the schedule
%    (home-home pair or away-away pair).

% 4. Each team has one bye during the season (to occur during the
%    divisional RRT).

% 5. At no point during the season can the number of home and away
%    games played by a team differ by more than 1.

% 6. Any pair of teams must have consecutive meetings occur at different
%    venues. (AVR)

% 7. Each division must have 3 pairs of complementary schedules.

include "alldifferent.mzn";
include "global_cardinality_closed.mzn";
include "inverse.mzn";
include "member.mzn";
include "regular.mzn";

%% HAP patterns

int: A = 1; % away
int: B = 2; % bye
int: H = 3; % home

int: divsize = 7;

set of int: north_teams = 1..7;
set of int: south_teams = 8..14;
set of int: teams = 1..14;
set of int: first_tour = 1..7;
set of int: second_tour = 8..20;
set of int: period = 1..20;

array[teams,period] of var A..H: hap;
array[teams,period] of var teams: contestant;
array[teams] of var 0..19: break;


int: objmin = 0;
int: objmax = sum(t in teams, p in 1..33)(1);
var objmin..objmax: objective;

array[teams] of var teams: row;	% row[i]=j means TEAMi gets row j of template
array[teams] of var teams: team;% the inverse of row

%% venue unavailability

array[teams,1..33] of 0..1: nohome;

%% division assignment

set of int: group1;
set of int: group2;

%% derby constraints

array[int] of set of int: derby_set;
array[int] of period: derby_period;

%% complementary schedules

array[int] of set of int: cpairs;

%% DFA states

int: INIT = 1;
int: B_1 = 2;
int: A_1 = 3;
int: H_1 = 4;
int: A_2 = 5;
int: H_2 = 6;
int: AB_2 = 7;
int: HB_2 = 8;
int: A_3 = 9;
int: H_3 = 10;
int: AB_3 = 11;
int: HB_3 = 12;
int: A_4 = 13;
int: H_4 = 14;
int: AB_4 = 15;
int: HB_4 = 16;
int: A_5 = 17;
int: H_5 = 18;
int: AB_5 = 19;
int: HB_5 = 20;
int: A_6 = 21;
int: H_6 = 22;
int: AB_6 = 23;
int: HB_6 = 24;
int: AB_7 = 25;
int: HB_7 = 26;
int: AB_8 = 27;
int: HB_8 = 28;
int: AB_9 = 29;
int: HB_9 = 30;
int: AB_20 = 31;
int: HB_20 = 32;

array[int,int] of int: transition =
    		  [|  A_1,   B_1,   H_1  % INIT, start state
		   | AB_2,     0,  HB_2  % B_1
		   |    0,  AB_2,   H_2  % A_1
		   |  A_2,  HB_2,     0  % H_1
		   |    0,  AB_3,   H_3  % A_2
		   |  A_3,  HB_3,     0  % H_2
		   |    0,     0,  HB_3  % AB_2
		   | AB_3,     0,     0  % HB_2
		   |    0,  AB_4,   H_4  % A_3
		   |  A_4,  HB_4,     0  % H_3
		   |    0,     0,  HB_4  % AB_3
		   | AB_4,     0,     0  % HB_3
		   |    0,  AB_5,   H_5  % A_4
		   |  A_5,  HB_5,     0  % H_4
		   |    0,     0,  HB_5  % AB_4
		   | AB_5,     0,     0  % HB_4
		   |    0,  AB_6,   H_6  % A_5
		   |  A_6,  HB_6,     0  % H_5
		   |    0,     0,  HB_6  % AB_5
		   | AB_6,     0,     0  % HB_5
		   |    0,  AB_7,     0  % A_6
		   |    0,  HB_7,     0  % H_6
		   |    0,     0,  HB_7  % AB_6
		   | AB_7,     0,     0  % HB_6
		   |    0,     0,  HB_8  % AB_7
		   | AB_8,     0,     0  % HB_7
		   |    0,     0,  HB_9  % AB_8, accept state
		   | AB_9,     0,     0  % HB_8, accept state
		   |AB_20,     0,  HB_8  % AB_9
		   | AB_8,     0, HB_20  % HB_9
		   |    0,     0, HB_20  % AB_20, accept state
		   |AB_20,     0,     0  % HB_20, accept state
		   |];

%% SEASONAL CONSTRANTS

% cost function

constraint
    objective = sum(t in teams, p in period  where nohome[t,p]=1)(bool2int(hap[row[t],p]=H))
         + sum(t in teams, p in 21..33 where nohome[t,p]=1)(bool2int(hap[row[t],41-p]=A));

% division assignment

constraint
    forall(t in group1)(row[t] in 1..7) /\
    forall(t in group2)(row[t] in 8..14);

constraint
    inverse(row,team) :: domain;

% derby constraints

constraint
    forall(i in index_set(derby_set))(
        let {set of int: ds = derby_set[i],
	     int: dp0 = derby_period[i],
	     period: dp = if dp0>20 then 41-dp0 else dp0 endif} in (
	    if card(ds) = 3 then
	        exists(t in ds, u in ds where t<u)(
          	    contestant[row[t],dp] = row[u] /\
		    contestant[row[u],dp] = row[t]
		)
	    else if card(ds) = 4 then
	        forall(t in ds)(
		    member([row[u] | u in ds where u != t], contestant[row[t],dp]) /\
		    member([contestant[row[u],dp] | u in ds where u != t], row[t])
		)
	    else true endif endif
	)
    );

% complementary schedules

constraint
    forall(cp in cpairs)(
        let {int: t = min(cp), int: u = max(cp)} in (
            break[row[t]] = break[row[u]] /\
            forall(p in period)(hap[row[t],p]!=hap[row[u],p])
	)
    );	    

%% STRUCTURAL CONSTAINTS

predicate compl(int: t1, int: t2) = (
          break[t1] = break[t2] /\
          forall(p in period)(hap[t1,p]!=hap[t2,p])
    );

% first round robin tournament (domains)
constraint
    forall(p in first_tour, t in north_teams)(
        contestant[t,p] in north_teams
    ) /\
    forall(p in first_tour, t in south_teams)(
        contestant[t,p] in south_teams
    );

% channel break <---> hap (2)
constraint
    forall(t in teams)(
        break[t] = sum(p in {9,11,13,15,17,19})(p*bool2int(hap[t,p]=hap[t,p+1]))
    );

% regular expression for HAP set per team (4)
constraint
    forall(t in teams)(
	regular([hap[t,p] | p in period],
		HB_20, % last state
		H,     % last symbol
		transition,
		INIT,  % start state
		{AB_8,HB_8,AB_20,HB_20} % accept states
		)
    );

% away and home should match -- has absolutely zero effect
% constraint
%     forall(p in period)(
% 	sum(t in teams)(hap[t,p]) = divsize*(H+A)
%     );

% RRT (5)
constraint
    forall(p in period)(
        inverse([contestant[t,p] | t in teams],[contestant[t,p] | t in teams]) :: domain
    );

% RRT (6)
constraint
    forall(t in teams)(
        alldifferent([contestant[t,p] | p in first_tour]) :: domain /\
        alldifferent([contestant[t,p] | p in second_tour]) :: domain
    );

% either we at home and contestant away (7)
%     or we away and contestant at home
%     or bye (we = contestant)
constraint
    forall(p in period, t in teams)(
        let {var teams: ctw = contestant[t,p]} in (
	    hap[ctw,p] + hap[t,p] = A+H
	)
    );

% AVR rule (1) (8)
constraint
    forall(t in teams)(
        alldifferent([3*contestant[t,p]+hap[t,p] | p in period]) :: domain
    );

% each division must have 3 pairs of complementary schedules -- generic version (9)
% constraint
%     let {array[1..14] of var 0..1: nc} in (
%         forall(i in 1..7)(
% 	    nc[i]=1 <-> exists(j in 1..7 where j!=i)(compl(i,j))
% 	) /\
%         forall(i in 8..14)(
% 	    nc[i]=1 <-> exists(j in 8..14 where j!=i)(compl(i,j))
% 	) /\
% 	sum(i in 1.. 7)(nc[i]) = 6 /\
% 	sum(i in 8..14)(nc[i]) = 6
%     );

%% IMPLIED CONSTRAINTS
    
% channel contestant <---> hap (3)
constraint
    forall(t in teams, p in period)(
        contestant[t,p]=t <-> hap[t,p]=B
    );

% exactly six aligned breaks per division (10)
constraint
    sum(t in north_teams )(bool2int(break[t]>0)) = 6 /\
    sum(t in south_teams)(bool2int(break[t]>0)) = 6;

% The byes that each division has in Part~I occur in different weeks -- (11)
% constraint
%     let {array[1..14] of var 1..14: bye} in (
%         forall(t in 1.. 7)(hap[t,bye[t]] = B) /\
%         forall(t in 8..14)(hap[t,bye[t]-7] = B) /\
% 	alldifferent(bye) :: domain
%     );

% exactly two occurrences of every break period (12)
constraint
    global_cardinality_closed(break, [0,9,11,13,15,17,19], [2,2,2,2,2,2,2]);

%% SYMMETRY-BREAKING CONSTAINTS

% SYMMETRY: global home/away (13)
% constraint
%     hap[1,2] = H /\ hap[2,1] = A;

% SYMMETRY: North/South division (14)
% constraint
%     lex_greater([break[i] | i in 1..2], [break[i] | i in 8..9]);

% SYMMETRY: fix bye period (15)
constraint
    forall(t in north_teams)(
        hap[t,t] = B /\ 
        hap[t+divsize,t] = B
    );

% each division must have 3 pairs of complementary schedules (16)
% - only 1/2, 2/3, 3/4, 4/5, 5/6, 6/7 can be complementary
constraint
    let {array[1..13] of var bool: cij} in (
        forall(i in 1..13 where i != 7)(cij[i] <-> compl(i,i+1)) /\
	(cij[1] \/ cij[2]) /\
	(cij[3] \/ cij[4]) /\
	(cij[5] \/ cij[6]) /\
	(cij[8] \/ cij[9]) /\
	(cij[10] \/ cij[11]) /\
	(cij[12] \/ cij[13])
    );

% teams 2, 4, 6, 9, 11, 13 must be complementary with adjacent team (17)
constraint
    forall(t in {2,4,6,9,11,13})(break[t] > 0);

% 1st row and 1st column complementary for each division (18)
constraint
    forall(t in north_teams)(
        hap[t,1] + hap[1,t] = A+H /\
        hap[t+divsize,1] + hap[1+divsize,t] = A+H
    );

%% SOLVING AND OUTPUTTING

solve 
	:: seq_search([
    	int_search([hap[t,p] | p in period, t in teams], input_order, indomain_min, complete),
     	int_search(row, input_order, indomain_min, complete),
     	int_search([contestant[t,p] | t in teams, p in period], first_fail, indomain_min, complete)
   	])
	minimize objective;

output [
%	if fix(hap[t,p]) = B then "  B"
%    else if fix(hap[t,p]) = A then "  A"
%    else "  H"
%    endif endif ++
%    if p = max(period) then "\n" else " " endif
%| t in teams, p in period
%] ++ ["\n"] ++ [
%	if fix(contestant[t,p])<10 then "  " else " " endif ++
%    show(contestant[t,p]) ++
%    if p = max(period) then "\n" else " " endif
%| t in teams, p in period
%] ++ ["\n"] ++ [
%	if p = min(period) /\ t < 10 then "TEAM  " ++ show(t) ++ ":"
%    else if p = min(period) then "TEAM " ++ show(t) ++ ":" 
%    else "" endif endif ++
%    let {
%		var int: value =
%    		if fix(hap[row[t],p]) = A then -team[contestant[row[t],p]]
%    		else if fix(hap[row[t],p]) = H then team[contestant[row[t],p]]
%    		else 0
%    		endif endif
%	} in (
%   		     if fix(value) < -9 then " "   ++ show(value)
%    	else if fix(value) <  0 then "  "  ++ show(value)
%    	else if fix(value) < 10 then "   " ++ show(value)
%    	else "  "++show(value)
%    	endif endif endif
%   	) ++
%      	if p = max(period) then "\n" else "" endif
%| t in teams, p in period
%] ++ [
	"hap = array2d(", show(teams), ", ", show(period), ", ", show(hap), ");\n",
	"contestant = array2d(", show(teams), ", ", show(period), ", ", show(contestant), ");\n",
	"row = ", show(row), ";\n",
	"objective = ", show(objective), ";\n"
];

