%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2013 National ICT Australia.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author(s): 
%   Andreas Schutt <andreas.schutt@nicta.com.au>
%
%-----------------------------------------------------------------------------%
% Flexible Job Shop Scheduling
%
% Flexible Job Shop Scheduling (FJSS) is more general version of Job Shop
% Scheduling in which some tasks can be run an alternative machines. The goal
% is to find a feasible schedule minimising the makespan.
%
%-----------------------------------------------------------------------------%
% Including files

include "globals.mzn";

%-----------------------------------------------------------------------------%
% Parameters

int: no_mach;   % Number of machines
int: no_jobs;   % Number of jobs
int: no_task;   % Number of total tasks
int: no_optt;   % Number of total optional tasks

set of int: Mach  = 1..no_mach;
set of int: Jobs  = 1..no_jobs;
set of int: Tasks = 1..no_task;
set of int: OptTs = 1..no_optt;

array [Jobs] of set of int: tasks;
array [Tasks] of set of int: optts;

array [OptTs] of int: optt_mach;
array [OptTs] of int: optt_dur;

array [Jobs] of int: last_task = [ max(tasks[j]) | j in Jobs ];

    % Additional derived parameters for tasks
    %
array [Tasks] of int: task_job = 
    [ min(j in Jobs where t in tasks[j])(j) | t in Tasks ];
array [Tasks] of int: task_mins =
    [ sum(k in tasks[task_job[t]])(if k < t then task_mind[k] else 0 endif)
    |   t in Tasks ];
array [Tasks] of int: task_maxs =
    [ t_max -
        sum(k in tasks[task_job[t]])(if k < t then 0 else task_mind[k] endif)
    |   t in Tasks ];
array [Tasks] of int: task_mind = 
    [ min(o in optts[t])(optt_dur[o]) | t in Tasks ];
array [Tasks] of int: task_maxd = 
    [ max(o in optts[t])(optt_dur[o]) | t in Tasks ];

    % Additional deirved parameters for optional tasks
    %
array [OptTs] of int: optt_task =
    [ min(t in Tasks where o in optts[t])(t) | o in OptTs ];

int: min_dur = min(optt_dur);
int: max_dur = max(optt_dur);
set of int: Durs = min_dur..max_dur;

    % Parameters related to the planning horizon
    %
int: t_max = sum(t in Tasks)(max(o in optts[t])(optt_dur[o]));
set of int: Times = 0..t_max;

%-----------------------------------------------------------------------------%
% Variables

    % Start time variables for tasks
    %
array [Tasks] of var Times: start =
    [ let { var task_mins[t]..task_maxs[t]: s } in s | t in Tasks ];

    % Duration variables for tasks
    %
array [Tasks] of var Durs: dur =
    [ if task_mind[t] = task_maxd[t] then task_mind[t] else
        let { var task_mind[t]..task_maxd[t]: d } in d endif
    |   t in Tasks ];

    % Variables whether an optional task is executed
    %
array [OptTs] of var bool: b;

var Times: objective;

%-----------------------------------------------------------------------------%
% Constraints

    % Precedence relations
    %
constraint
    forall(j in Jobs, i in tasks[j] where i < last_task[j])(
        start[i] + dur[i] <= start[i + 1]
    );

    % Duration constraints
    %
constraint
    forall(o in OptTs)(
        let { int: t = optt_task[o] } in (
            if card(optts[t]) = 1 then
                b[o] = true
            else
                b[o] -> dur[t] = optt_dur[o]
            endif
        )
    );

    % Optional tasks' constraints
    %
constraint
    forall(t in Tasks where card(optts[t]) > 1)(
        ( sum(o in optts[t])(bool2int(b[o])) <= 1     )
    /\  ( exists(o in optts[t])(b[o])                 )
    );

constraint
    forall(t in Tasks where card(optts[t]) = 2)(
        let {
            int: o1 = min(optts[t]),
            int: o2 = max(optts[t])
        } in ( b[o1] <-> not(b[o2]) )
    );

    % Resource constraints
    %
constraint
    forall(m in Mach)(
        let {
            set of int: MTasks = { o | o in OptTs where optt_mach[o] = m }
        } in (
            cumulative(
                [ start[optt_task[o]] | o in MTasks ],
                [ optt_dur[o]         | o in MTasks ],
                [ bool2int(b[o])      | o in MTasks ],
                1
            )
        )
    );

    % Objective constraint
    %
constraint
    forall(j in Jobs)(start[last_task[j]] + dur[last_task[j]] <= objective);

%-----------------------------------------------------------------------------%
% Solve item

solve 
    :: search
    minimize objective;

%------------------------------------------------------------------------------%
% Searches

ann: s_mindur   = int_search(dur, smallest, indomain_min, complete);
ann: s_minstart = int_search(start, smallest, indomain_min, complete);
ann: s_bool     = bool_search(b, input_order, indomain_max, complete);
ann: s_obj      = int_search([objective], input_order, indomain_min, complete);

ann: search = seq_search([s_mindur, s_bool, s_minstart, s_obj]);

%-----------------------------------------------------------------------------%
% Output

output 
[   "objective = ", show(objective), ";\n",
    "start = ", show(start), ";\n",
    "dur = ", show(dur), ";\n",
    "b = ", show(b), ";\n"
];
