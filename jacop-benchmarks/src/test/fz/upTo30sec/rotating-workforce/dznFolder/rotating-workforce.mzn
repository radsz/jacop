%------------------------------------------------------------------------------%
% Rotating Workforce Scheduling
%
% The rotating workforce scheduling problem aims to schedule workers satisfying
% shift sequence constraints and ensuring enough shifts are covered on each day,
% where every worker completes the same schedule, just starting at different days 
% in the schedule.
%
% This model is taken from the publication of the paper listed below.
%
% Publication: 
%   Nysret Musliu, Andreas Schutt, Peter J. Stuckey (2018): "Solver independent
%   rotating workforce scheduling", CPAIOR 2018.
%   (https://link.springer.com/chapter/10.1007/978-3-319-93031-2_31)
% 
% Submitter: Andreas Schutt
%
%------------------------------------------------------------------------------%


%------------------------------------------------------------------------------%
% Input Parameters
%------------------------------------------------------------------------------%

%------------------------------------------------------------------------------%
% Schedule Parameters

int: week_length;   % Length of the schedule

int: nb_workers;    % Number of the workers/employees

int: min_daysoff;   % Minimal length of days-off blocks
int: max_daysoff;   % Maximal length of days-off blocks

int: min_work;      % Minimal length of work blocks
int: max_work;      % Maximal lenght of work blocks

%------------------------------------------------------------------------------%
% Shifts

int: nb_shifts;                            % Number of shifts
array[SHIFT] of string: shift_name;        % Name of shifts
array[SHIFT] of int:    shift_start;       % Start of shift
array[SHIFT] of int:    shift_length;      % Length of shift
array[SHIFT] of int:    shift_block_min;   % Minimal length of blocks
array[SHIFT] of int:    shift_block_max;   % Maximal length of blocks

%------------------------------------------------------------------------------%
% Temporal Requirements

array[SHIFT, DAY] of int: temp_req;    % Temporal requirements

%------------------------------------------------------------------------------%
% Forbidden Shift Sequences

int: nb_forbidden;                              % Number of forbidden shift sequences
array[FORBIDDEN] of int:  forbidden_before;     % The shift before in the forbidden sequence
array[FORBIDDEN] of int:  forbidden_after;      % The shift after in the forbidden sequence
array[FORBIDDEN] of bool: forbidden_daysoff;    % If a days-off period is between forbidden shifts

%------------------------------------------------------------------------------%
% Sorting of shifts

array[SHIFT0] of float: shift_sort;
shift_sort = sort_none;

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% Derived Parameters
%
% This file contains all parameters derived from the input parameters
%------------------------------------------------------------------------------%

%------------------------------------------------------------------------------%
% Instance Parameters

    % Problem size calculated by the total number of worker days and the number
    % of possible shifts per day
int: problem_size = schedule_length * card(SHIFT0);

%------------------------------------------------------------------------------%
% Schedule Parameters

    % The number of workers plus the number of workers repeated at the end of the schedule
int: nb_workers0 = nb_workers + 1;

    % The length of the schedule / the total number of worker days of the schedule
int: schedule_length  = week_length * nb_workers;

    % The length of the extended schedule / the total number of worker days of the extended schedule
int: schedule_length0 = week_length * nb_workers0;

set of int: DAY   = 1..week_length; % The length of a week for a worker
set of int: WEEK  = 1..nb_workers;  % The set of weeks in the schedule
set of int: WEEK0 = 1..nb_workers0; % The set of weeks in the extended schedule

set of int: SCHEDULE  = 1..schedule_length;     % The set of days in the planning horizon
set of int: SCHEDULE0 = 1..schedule_length0;    % The set of days in the planning horizon plus the extra week at the end

%------------------------------------------------------------------------------%
% Shifts

int: nb_shifts0 = nb_shifts + 1;    % The number of shifts including the off-duty days
set of int: SHIFT  = 1..nb_shifts;  % Set of shifts
set of int: SHIFT0 = 1..nb_shifts0; % Set of shifts including off-duty day
int: OFF = nb_shifts0;   % Identifier of the off-duty day

    % Total number of required shift days per shift
array[SHIFT] of int: nb_shift_days_req = [ sum(d in DAY)(temp_req[s, d]) | s in SHIFT ];

    % Minimal number of shift blocks per shift
array[SHIFT] of float: min_shift_blocks = [ int2float(nb_shift_days_req[s]) / int2float(shift_block_max[s]) | s in SHIFT ];

    % Maximimal number of shift blocks per shift
array[SHIFT] of float: max_shift_blocks = [ int2float(nb_shift_days_req[s]) / int2float(shift_block_min[s]) | s in SHIFT ];

%------------------------------------------------------------------------------%
% On-Duty Parameters

    % Total number of required worker days
int: nb_on_duty_days = sum(nb_shift_days_req);

    % Minimal number of on-duty blocks
float: min_on_duty_blocks = int2float(nb_on_duty_days) / int2float(max_work);

    % Maximal number of on-duty blocks
float: max_on_duty_blocks = int2float(nb_on_duty_days) / int2float(min_work);

    % Average number of off-duty days per week
float: avg_on_duty_days_per_week = int2float(nb_on_duty_days) / int2float(nb_workers);

%------------------------------------------------------------------------------%
% Off-Duty Parameters

    % Total number of off-duty days
int: nb_off_duty_days = schedule_length - nb_on_duty_days;

    % Minimal number of off-duty blocks
float: min_off_duty_blocks = int2float(nb_off_duty_days) / int2float(max_daysoff);

    % Maximal number of off-duty blocks
float: max_off_duty_blocks = int2float(nb_off_duty_days) / int2float(min_daysoff);

    % Average number of off-duty days per week
float: avg_off_duty_days_per_week = int2float(nb_off_duty_days) / int2float(nb_workers);

%------------------------------------------------------------------------------%
% Block Parameters

    % Minimal number of on- and off-duty blocks in the schedule
int: min_blocks =  ceil( max(min_on_duty_blocks, min_off_duty_blocks) );

    % Maximal number of on- and off-duty blocks in the schedule
int: max_blocks = floor( min(max_on_duty_blocks, max_off_duty_blocks) );

%------------------------------------------------------------------------------%
% Forbidden Shift Sequences

set of int: FORBIDDEN = 1..nb_forbidden;        % Set of forbidden shift sequences

%------------------------------------------------------------------------------%
% Mapping from sorted shifts to shifts

array[SHIFT0] of SHIFT0: map_sorted_shift = arg_sort(shift_sort);

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% Assertions
%
% This file contains assertion for checking the correctness of the input data.
%------------------------------------------------------------------------------%

constraint assert(not (OFF in SHIFT), "OFF (\(OFF)) must be different to elements in SHIFT (\(SHIFT))!\n");

constraint forall(s in SHIFT)(
    assert(shift_block_max[s] <= max_work, "The maximal shift length \(shift_name[s]) must be less than or equal to the maximal on-duty block length!\n")
);

% Cross-checking on the minimal and maximal number of on and off duty blocks
% NOTE that it is not wrapped in an assertion, so that the instance can fail
% on the solver level and the print out "=====UNSATISFIABLE=====" is made.
constraint ceil(min_on_duty_blocks ) <= floor(max_on_duty_blocks );
constraint ceil(min_off_duty_blocks) <= floor(max_off_duty_blocks);
constraint ceil(min_on_duty_blocks ) <= floor(max_off_duty_blocks);
constraint ceil(min_off_duty_blocks) <= floor(max_on_duty_blocks );

%------------------------------------------------------------------------------%
% Shift Sorting criteria

    % ID / No sorting
array[SHIFT0] of float: sort_none = [ s | s in SHIFT0 ];

    % OFF then input order
array[SHIFT0] of float: sort_off_then_input_order = [ 
    if s = OFF then 0.0 else int2float(s) endif
| s in SHIFT0 ];

    % input order then OFF
array[SHIFT0] of float: sort_input_order_then_off = [ 
    int2float(s) 
| s in SHIFT0 ];

    % OFF then reverse input order
array[SHIFT0] of float: sort_off_then_reverse_input_order = [ 
    int2float(nb_shifts0 - s)
| s in SHIFT0 ];

    % reverse input order then OFF
array[SHIFT0] of float: sort_reverse_input_order_then_off = [ 
    if s = OFF then int2float(nb_shifts0) else int2float(nb_shifts0 - s) endif
| s in SHIFT0 ];

array[SHIFT0] of float: sort_min_slack1 = [
    int2float(
        if s = OFF then
            floor(max_blocks) * max_daysoff - nb_off_duty_days
        else
            floor(min(max_blocks, max_shift_blocks[s])) * shift_block_max[s] - nb_shift_days_req[s]
        endif
    )
| s in SHIFT0 ];

    % Peter's one (over approximation of block usages of other shifts)
array[SHIFT0] of float: sort_min_slack2 = [
    int2float(
        if s = OFF then
            floor(max_blocks) * max_daysoff - nb_off_duty_days
        else
            min(
                floor(min(max_blocks, max_shift_blocks[s])) * shift_block_max[s] - nb_shift_days_req[s],
                max_work * (max_blocks - sum(s2 in SHIFT where s2 != s)(ceil(min_shift_blocks[s2]))) - nb_shift_days_req[s]
            )
        endif
    )
| s in SHIFT0];

    % Corrected Peter's one without over approximation
array[SHIFT0] of float: sort_min_slack3 = [
    if s = OFF then
        floor(max_blocks) * max_daysoff - nb_off_duty_days
    else
        min(
            floor(min(max_blocks, max_shift_blocks[s])) * shift_block_max[s] - nb_shift_days_req[s],
            max_work * max_blocks - sum(s2 in SHIFT where s2 != s)(nb_shift_days_req[s2]) - nb_shift_days_req[s]
        )
    endif
| s in SHIFT0];

    % Andreas' one
array[SHIFT0] of float: sort_min_block_diff1 = [
    if s = OFF then 
        max_blocks - min_on_duty_blocks
    else
        max_blocks - min_shift_blocks[s]
    endif
| s in SHIFT0 ];

array[SHIFT0] of float: sort_min_block_diff2 = [
    if s = OFF then 
        max_blocks - (max_blocks - min_off_duty_blocks) / 2
    else
        max_blocks - (min(max_blocks, min_shift_blocks[s]) - min_shift_blocks[s]) / 2
    endif
| s in SHIFT0 ];


%------------------------------------------------------------------------------%
% Variables and linking constraints between those variables.
%------------------------------------------------------------------------------%
% Variables

    % The schedule in that the shifts are represented by their identifiers
array[WEEK0,DAY] of var SHIFT0: plan = 
    if forall(sh in SHIFT0)(sh = map_sorted_shift[sh]) then
        plan_sort
    else
        array2d(WEEK0, DAY, [ map_sorted_shift[plan_sort[w,d]] | w in WEEK0, d in DAY ])
    endif;
    % The schedule representing `plan` in an one-dimensional array
array[SCHEDULE0] of var SHIFT0: dplan = array1d(plan);
    % The schedule in that the shifts are sorted with respect to a certain criteria
array[WEEK0,DAY] of var SHIFT0: plan_sort;


%------------------------------------------------------------------------------%
% Linking constraints between variables

    % Linking the first worker/week to the additional one at the end
    %
constraint forall(d in DAY)(
    plan[1, d] = plan[nb_workers0, d]
);

%------------------------------------------------------------------------------%
% Constraints for Modelling the Temporary Requirements of Shifts for each day
% via GCC
%------------------------------------------------------------------------------%
% Inlcudes

include "global_cardinality_low_up.mzn";

%------------------------------------------------------------------------------%
% Constraints

    % Requirements of shifts for over all days
    %
constraint forall(d in DAY)(
    global_cardinality_low_up(
        [ plan[w,d]      | w  in WEEK  ],
        [ sh             | sh in SHIFT ] ++ [ OFF ], 
        [ temp_req[sh,d] | sh in SHIFT ] ++ [ nb_workers - sum(sh in SHIFT)(temp_req[sh,d]) ], 
        [ temp_req[sh,d] | sh in SHIFT ] ++ [ nb_workers - sum(sh in SHIFT)(temp_req[sh,d]) ]
    )
    :: domain
);

%------------------------------------------------------------------------------%
% Constraints for Modelling the Constraints between Shifts using the Global
% Constraint 'regular'
%
% NOTE that this regular constraint assumes that the last day in the schedule
% is an off-day and minimal length of an off-day block is at most 2!
%------------------------------------------------------------------------------%
% Asumptions

constraint assert(
    min_daysoff <= 2,
    "Regular constraint assumes that the minimal length of days-off block is at most 2."
);

constraint assert(
    sum(sh in SHIFT)(temp_req[sh, week_length]) < nb_workers, 
    "Regular constraint assumes that the last day in schedule is a day-off."
);

%------------------------------------------------------------------------------%
% Includes

include "regular.mzn";

%------------------------------------------------------------------------------%
% Computing the parameters for the allowed transitions

    % Transitions with a sequence of length 3
array[SHIFT,SHIFT] of bool: transition3 = array2d(SHIFT,SHIFT, [ 
        not exists(f in FORBIDDEN where forbidden_daysoff[f])(
            forbidden_before[f] == i /\ forbidden_after[f] == j
        )
    | i,j in SHIFT ]
);
    % Transitions with a sequence of length 2
array[SHIFT,SHIFT] of bool: transition = array2d(SHIFT,SHIFT, [ 
        not exists(f in FORBIDDEN where not forbidden_daysoff[f])(
            forbidden_before[f] == i /\ forbidden_after[f] == j
        )
    | i,j in SHIFT ]
);
     
%------------------------------------------------------------------------------%
% Computing the parameters for the regular constraint

int: START = 1;     % Start (initial or first) state of the DFA
int: OFF1  = 2;     % The state of the DFA when the first day in the block is an off-duty day
                    % after the initial start or an on-duty block ending with a specific shift
int: OFF2  = nb_shifts0 + 1;    % The state of the DFA when the current block is an off-duty one
                                % and at least of length two

    % The number of (feasible) states
int: nb_states = nb_shifts + max_daysoff + sum(sh in SHIFT)(max_work * shift_block_max[sh]);

    % The state of the DFA when the first day in the block is an on-duty day for each shift
array[SHIFT] of int: first = [ 
    1 + nb_shifts + max_daysoff 
    + sum(s1 in SHIFT where s1 < sh)( max_work * shift_block_max[s1] )
| sh in SHIFT ]; 


    % The state of the DFA after the first on-duty day in a block succeeding an
    % on-duty block ending with shift sh
function STATE: off1(SHIFT: sh)  = 1 + sh;

    % The state of the DFA in an on-duty block, for which the current length 
    % is 'dayswork', the current shift 'shift' (at position 'dyaswork'), and
    % the current shift lengths 'days'
function STATE: state(SHIFT: shift, int: days, int: dayswork) = 
    first[shift] + (max_work * (days - 1)) + (dayswork - 1);

    % The set of (feasible) states and in the case also the set of accepting states
set of int: STATE = 1..nb_states;
    % The set of all states including the failing state
set of int: STATE0 = 0..nb_states;

    % The DFA
array[STATE, SHIFT0] of STATE0: dfa = array2d(STATE, SHIFT0,
    [   
        % Transition from the first state
        % previous state: none
        % states: 1
        if s = OFF then 
            % First day in the schedule is an off-duty day assume previous is off
            OFF2
        else 
            % First day in the schedule is an on-duty day
            first[s] 
        endif 
    | s in SHIFT0 
    ] ++ [ 
        % Transitions after the first off-duty day in a block
        % previous state: off-duty day (first in the block/sequence)
        % states: 2 -- nb_shifts0
        if s = OFF then 
            % Second off-duty day in an off-duty block
            if 1 < max_daysoff then 
                OFF2 
            else 
                0 
            endif
        elseif 1 >= min_daysoff /\ transition3[sh,s] then 
            % Switch from an off-duty block of length one to an on-duty block
            first[s]
        else 
            0 
        endif
    | sh in SHIFT, s in SHIFT0 
    ] ++ [ 
        % Transitions after a sequence of at least two off-duty days
        % previous state/day: off-duty day
        % states: nb_shifts0 + 1 -- nb_shifts0 + max_daysoff - 1
        if s = OFF then 
            % (d + 1)th off-duty day in an off-duty block
            if d < max_daysoff then 
                nb_shifts0 + d
            else 
                0 
            endif 
        elseif d >= min_daysoff then 
            % Switch from an of-duty block of length of at least two to an on-duty block
            first[s]                                  
        else 
            0 
        endif                         
    | d in 2..max_daysoff, s in SHIFT0 
    ] ++ [ 
        % Transitions after a sequence of on-duty days
        % previous state/day: on-duty day
        % states: nb_shifts0 + max_daysoff --
        if s = OFF then 
            % Switch from an on-duty block to an off-duty block
            if ds >= shift_block_min[sh] /\ dw >= min_work then
                off1(sh)
            else 
                0 
            endif   
        else 
            % Continuation of the on-duty block
            if s = sh then
                % Continuation with the same shift
                if ds < shift_block_max[sh] /\ dw < max_work then
                    state(sh, ds + 1, dw + 1)
                else 
                    0 
                endif
            else
                % Switch to another on-duty shift
                if ds >= shift_block_min[sh] /\ dw < max_work /\ transition[sh, s] then
                    state(s, 1, dw + 1)
                else 
                    0 
                endif
            endif
        endif 
    | sh in SHIFT, ds in 1..shift_block_max[sh], dw in 1..max_work, s in SHIFT0
    ]
);

%------------------------------------------------------------------------------%
% Constraining the day transitions

constraint regular(dplan, nb_states, nb_shifts0, dfa, START, STATE);

%------------------------------------------------------------------------------%
% Redundant constraints that is looking at the number of the remaining off-duty
% and on-duty blocks in the remaining schedule.
%------------------------------------------------------------------------------%


constraint redundant_constraint(
    let {
        % Count of the number of off-duty days from first day until the end of the week
        array[WEEK] of var 0..nb_off_duty_days: count_off_duty;
        % Count of the number of off-duty days after the end of the week
        array[WEEK] of var 0..nb_off_duty_days: rem_off = 
            [ nb_off_duty_days - count_off_duty[w] | w in WEEK ];
        % Count of the number of on-duty days after the end of the week
        array[WEEK] of var 0..nb_on_duty_days: rem_on =
            [ nb_on_duty_days - week_length * w + count_off_duty[w] | w in WEEK ];
        % Lower bound of off-duty blocks
        array[WEEK] of var int: lb_off_blocks = [ 
            (rem_off[w] div max_daysoff) + ((rem_off[w] mod max_daysoff) > 0) - (plan[1,1] != OFF /\ plan[w+1, 1] = OFF)
        | w in WEEK ];
        % Upper bound of on-duty blocks
        array[WEEK] of var int: ub_on_blocks = [ 
            (rem_on[w] div min_work) + (plan[1,1] != OFF /\ plan[w, week_length] != OFF)
        | w in WEEK ];
        % Lower bound of on-duty blocks
        array[WEEK] of var int: lb_on_blocks = [ 
            (rem_on[w] div max_work) + ((rem_on[w] mod max_work) > 0) - (plan[1,1] = OFF /\ plan[w+1, 1] != OFF)
        | w in WEEK ];
        % Upper bound of off-duty blocks
        array[WEEK] of var int: ub_off_blocks = [ 
            (rem_off[w] div min_daysoff) + (plan[1,1] = OFF /\ plan[w, week_length] = OFF)
        | w in WEEK ];
    } in (
        % First week is just the sum of the off-duty days in that week
        count_off_duty[1] = sum(d in DAY)( plan[1,d] = OFF )
        % The remaining weeks are the sum of the previous weeks and the current one
    /\  forall(w in 2..nb_workers)(
            count_off_duty[w] = count_off_duty[w - 1] + sum(d in DAY)( plan[w,d] = OFF )
        )
        % The sum of the last week must be equal to the number of off duty days
    /\  count_off_duty[nb_workers] = nb_off_duty_days
        % The lower bound on the remaining off-duty blocks must be not greater 
        % than the upper bound on the remaining on-duty blocks
    /\  forall(w in WEEK)(lb_off_blocks[w] <= ub_on_blocks[w])
        % The lower bound on the remaining on-duty blocks must be not greater 
        % than the upper bound on the remaining off-duty blocks
    /\  forall(w in WEEK)(lb_on_blocks[w] <= ub_off_blocks[w])
    )
);

 
%------------------------------------------------------------------------------%
% Symmetry breaking constraint which assigns an off-duty day at the end of
% the schedule and an on-duty day at the beginning if possible
%------------------------------------------------------------------------------%

constraint symmetry_breaking_constraint(
    if sum(sh in SHIFT)(temp_req[sh, week_length]) < nb_workers then
        % There must be at least one off-duty day at the end of the week
        plan[nb_workers, week_length] = OFF
    else
        true
    endif
/\  if 
        % Temporary requirements are the same over the week for each shift,
        % thus a symmetric solution can be obtained by day shifting a solution
        forall(sh in SHIFT, d in DAY where d < week_length)(
            temp_req[sh, d] = temp_req[sh, d + 1]
        )
        % There are more on-duty shifts at the beginning of the week in comparison
        % to the end of the week, thus there is at least one on-duty starts
        % at the beginning of the week in any solution
    \/  sum(sh in SHIFT)(temp_req[sh, week_length]) 
        < sum(sh in SHIFT)(temp_req[sh, 1])
    then
        % Fixing that the first day is an on-duty day in the schedule
        plan[1,1] != OFF
    else
        true
    endif
);

%------------------------------------------------------------------------------%
% Search

ann: ff_search = int_search(array1d(plan_sort), first_fail, indomain_min, complete);

%------------------------------------------------------------------------------%
% Solve item

solve :: ff_search satisfy;

%------------------------------------------------------------------------------%
% Output item

output [ 
    if d = 1 then
        "% "
    else
        ""
    endif ++
    if fix(plan[w,d]) in SHIFT then 
        shift_name[ fix(plan[w,d])  ] 
    else 
        "." 
    endif ++
    if d = week_length then 
        "\n" 
    else 
        " " 
    endif 
| w in WEEK, d in DAY 
] ++ [
    "plan_sort = array2d(\(WEEK0), \(DAY), \(plan_sort));\n"
];


