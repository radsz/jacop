%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Model example for Multi-Skilled Project Scheduling Problems (MSPSP)
% 
% MSPSP is a variation of the basic resource-constrained project scheduling
% problem. Here, a set of activities must be executed so that the project
% duration is minimised while satisfying all constraints involved. These
% constraints are
% 1) precedence relations between some activities expressing that an activity
% can only be run after its preceding activity's execution is finished,
% 2) skills requirements of activities on workers who have the capability to
% perform the activity, and
% 3) workers availibility, i.e., a worker can perform only one activity in
% each time period.
% 
%-----------------------------------------------------------------------------%

include "globals.mzn";

%-----------------------------------------------------------------------------%
% Model parameters.

    % Skills parameters
    %
int: n_skills;
set of int: Skills  = 1 .. n_skills;
int: n_workers;
set of int: Workers = 1 .. n_workers;
array [Workers] of set of Skills: has_skills;

array [Skills] of int: rc = 
    [ card({j | j in Workers where i in has_skills[j]}) | i in Skills ];

    % Task parameters
    %
int: n_tasks;                               % Number of tasks
set of int: Tasks = 1 .. n_tasks;           % Set of tasks
array [Tasks]         of int       : d  ;   % Durations
array [Skills, Tasks] of int       : rr ;   % Resource requirements
array [Tasks]         of set of int: suc;   % Successors

    % Planning horizon
    %
int: tmax = sum(i in Tasks)( d[i] );       % Trivial upper bound
set of int: Times = 0 .. tmax;

%-----------------------------------------------------------------------------%
% Model variables.

array [Tasks] of var Times: s;         % Start times
array [Workers, Tasks] of var bool: w; % Assignment of workers to tasks
var Times: objective;                  % Project duration (makespan)

%-----------------------------------------------------------------------------%
% Constraints.

    % Precedence constraints
    %
constraint
   forall ( i in Tasks, j in suc[i] )
   (
         s[i] + d[i] <= s[j]
   );

    % Skills constraints
    %
constraint
    forall ( i in Tasks )
    (
        let {
            set of int: TWorkers = 
                { j | j in Workers where 
                            exists(k in has_skills[j])(rr[k, i] > 0)
                }
        } in (
            forall ( k in Skills where rr[k, i] > 0 )
            (
                sum(j in TWorkers where k in has_skills[j])
                (
                    bool2int(w[j, i])
                ) >= rr[k, i]
            )
        /\  forall ( j in Workers where not(j in TWorkers) )
            (
                w[j, i] = false
            )
        )
    );

    % Redundant non-overlapping constraints for the workers
    %
constraint
    forall ( j in Workers )
    (
        let {
            set of int: WTasks =
                { i | i in Tasks where 
                            exists(k in has_skills[j])(rr[k, i] > 0)
                }
        } in (
            if card(WTasks) > 1 then
                cumulative(
                    [ s[i]              | i in WTasks ],
                    [ d[i]              | i in WTasks ],
                    [ bool2int(w[j, i]) | i in WTasks ],
                    1
                )
            else
                true
            endif
        )
    );

    % Redundant non-overlapping constraints
    %
constraint
	forall ( 
		i, j in Tasks
	where 
		i < j /\ not(j in suc[i]) /\ not(i in suc[j])
	)(
        if exists( k in Skills )( rr[k,i] + rr[k,j] > rc[k] ) then
            let { var bool: before } in (
		        (     before  -> s[i] + d[i] <= s[j] )
            /\  ( not(before) -> s[j] + d[j] <= s[i] )
            )
        else
            true
        endif
	);

    % Redudant cumulative resource constraints
    %
constraint
    forall ( k in Skills )
    (
        let { 
            set of int: RTasks = { i | i in Tasks where rr[k, i] > 0 },
            int: sum_rr = sum(i in RTasks)( rr[k,i] )
        } in (
            if card(RTasks) > 1 /\ sum_rr > rc[k] then
                cumulative(
                    [ s[i]    | i in RTasks ],
                    [ d[i]    | i in RTasks ],
                    [ rr[k,i] | i in RTasks ],
                    rc[k]
                )
            else
                true
            endif
        )
    );

    % Makespan constraints
    %
constraint
   forall ( i in Tasks where suc[i] == {} )
   (
      s[i] + d[i] <= objective
   );

%-----------------------------------------------------------------------------%
% Objective.

solve
    :: seq_search([
        int_search(s, smallest, indomain_split, complete),
        bool_search([w[i,j] | i in Workers, j in Tasks], input_order, 
            indomain_max, complete),
        int_search([objective], input_order, indomain_min, complete)
    ])
    minimize objective;

%-----------------------------------------------------------------------------%
% Output.

output [
    "% mspsp\n",
    "s = "         ++ show( s         ) ++ ";\n",
    "w = "         ++ show( w         ) ++ ";\n",
    "objective = " ++ show( objective ) ++ ";\n"
];

%-----------------------------------------------------------------------------%
%%% EOF %%%

