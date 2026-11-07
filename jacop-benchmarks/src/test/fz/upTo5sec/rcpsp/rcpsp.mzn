%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2009-2012 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
% Model example for Resource-Constrained Project Scheduling Problems (RCPSP)
% 
% A RCPSP consists of resources, tasks, and precedences between some tasks 
% where resources have of a specific capacity and tasks need some capacity of 
% some resource to be executed.
% Here, we consider resources with a constant discrete capacity over time and
% tasks with a constant discrete duration and resource requirements.
% The objective is to find a optimal schedule with respect to the earliest end
% time of the schedule where the tasks' resource requirements do not exceed
% the resource capacities to any time and each precedence is met.
% 
%-----------------------------------------------------------------------------%

include "globals.mzn";

%-----------------------------------------------------------------------------%
% Model parameters.


    % Resources
    %
int: n_res;                     % The number of resources
set of int: Res = 1..n_res;     % The set of all resources
array [Res] of int: rc;         % The resource capabilities

    % Tasks
    %
int: n_tasks;                           % The number of tasks
set of int: Tasks = 1..n_tasks;         % The set of all tasks
array [Tasks]      of int       : d  ;  % The task durations
array [Res, Tasks] of int       : rr ;  % The resource requirements
array [Tasks]      of set of int: suc;  % The task successors

    % Planning horizon
    % 
int: t_max = sum(i in Tasks)(d[i]);     % End time of the planning horizon
set of int: Times = 0..(t_max - 1);     % Possible start times

%-----------------------------------------------------------------------------%
% Model variables.

array [Tasks] of var Times: s;  % The start times
var 0..t_max: objective      ;  % The project duration (makespan)

%-----------------------------------------------------------------------------%
% Constraints.

    % Precedence constraints
    %
constraint
   forall ( i in Tasks, j in suc[i] )
   (
         s[i] + d[i] <= s[j]
   );

    % Redundant non-overlapping constraints
    %
constraint
    forall ( i, j in Tasks where i < j )
    (
        if exists(r in Res)(rr[r, i] + rr[r, j] > rc[r]) then
            s[i] + d[i] <= s[j]   \/ s[j] + d[j] <= s[i]
        else
            true
        endif
    );

    % Cumulative resource constraints
    %
constraint
    forall ( r in Res )
    (
        let { 
            set of int: RTasks = 
                            { i | i in Tasks 
                            where rr[r, i] > 0 /\ d[i] > 0 },
            int: sum_rr = sum(i in RTasks)(rr[r, i])
        } in (
            if RTasks != {} /\ sum_rr > rc[r] then
                cumulative(
                    [ s[i] | i in RTasks ],
                    [ d[i] | i in RTasks ],
                    [ rr[r, i] | i in RTasks ],
                    rc[r]
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
   :: int_search( s ++ [objective], smallest, indomain_min, complete )
   minimize objective;

%-----------------------------------------------------------------------------%

output [
    "Start times = ", show(s), "\n",
    "makespan = ", show(objective), "\n"
];

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

