%
% Copyright 2022 Mikael Zayenz Lagerkvist
%
% Permission is hereby granted, free of charge, to any person obtaining a copy of 
% this software and associated documentation files (the "Software"), to deal in the 
% Software without restriction, including without limitation the rights to use, copy, 
% modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, 
% and to permit persons to whom the Software is furnished to do so, subject to the 
% following conditions:
%
% The above copyright notice and this permission notice shall be included in all 
% copies or substantial portions of the Software.
%
% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, 
% INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR 
% PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE 
% LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, 
% TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE 
% OR OTHER DEALINGS IN THE SOFTWARE.
%


%
% This is a model for the rotating workforce scheduling problem, loosley following the problem 
% and model described in "The Rotating Workforce Scheduling Problem" by Nysret Musliu, Andreas Schutt, 
% and Peter J. Stuckey, but with a slightly different set of constraints. The constraints are inspired 
% some common rules used in Sweden.
%
% The model uses global cardinality for the requirements, two different regular constraints, and 
% two different uses of sliding_sum. 
%
% There is a simple but effective search strategy defined that focuses first on weekend night shifts, 
% then on weekends, then on all night shifts, and then finally on the rest of the shifts. This is
% roughly in order of most constrained literals.
%
% The instances are all generated instances known to have at least one solution.
%

% Changes by the MiniZinc Challenge Organisers:
% - Changed search order to input_order

include "globals.mzn";


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int: days = 7;
enum Days = {Mon, Tue, Wed, Thu, Fri, Sat, Sun};
set of Days: Weekend = {Sat, Sun};

enum Shifts = {Day, Evening, Night};
enum ShiftsAndOff = {Off} ++ S(Shifts);
int: shifts = card(Shifts);

int: employees;
set of int: Employees = 1..employees;
% Alternate view of schedule
int: weeks = employees;
set of int: Weeks = Employees; 

array[Days, Shifts] of int: requirements;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Variables
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The actual schedule
array[Weeks, Days] of var ShiftsAndOff: schedule;

% Rolled out schedule with the first two weeks repeated
set of int: RepeatedWeeks = Weeks union weeks+1..weeks+2;
array[RepeatedWeeks, Days] of var ShiftsAndOff: repeated_schedule = array2d(RepeatedWeeks, Days, 
    [schedule[week, day] | week in Weeks, day in Days] ++
    schedule[1, ..] ++
    schedule[2, ..]
);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Requirements met for each day
constraint forall (day in Days) (
    global_cardinality_low_up(schedule[.., day], 
                              set2array(S(Shifts)), 
                              requirements[day, ..], 
                              requirements[day, ..])
);

% At least 2 consecutive days off each week
constraint forall (week in Weeks) (
    regular(schedule[week, ..], ".* Off Off .*")
);

% At most five days without rest
%constraint among_seq(repeated_schedule, {Off}, 6, 1, 6);
constraint sliding_sum(1, 6, 6, [s = Off | s in array1d(repeated_schedule)]);

% At least 1 out of 3 weekends off.
constraint let {
        array[RepeatedWeeks] of var bool: free_weekend = [
              forall (day in Weekend) (repeated_schedule[week, day] = Off)
          | week in RepeatedWeeks];
    } in
    sliding_sum(1, 3, 3, free_weekend);

% At most 2 night-shifts in a row, and then rest
constraint let {
      int: states = 5;
      set of int: States = 1..states;
      int: start_state = 1;
      set of int: accepting_states = States;
      array[States, ShiftsAndOff] of {0} union States: transitions =[|
      % O  D  E  N
        1, 5, 5, 2 | % State 1, base case: if night shift, go to state 2
        1, 0, 0, 3 | % State 2, 1 night shift: if off go to state 1, if night go to state 2, else fail
        1, 0, 0, 4 | % State 3, 2 night shift: if off go to state 1, if night go to state 3, else fail
        1, 0, 0, 0 | % State 4, 3 night shifts: if off go to state 1, all others fail
        1, 5, 5, 0 | % State 5, 3 night shifts: if off go to state 1, all others fail
      |];
    } in
    regular(array1d(repeated_schedule), states, ShiftsAndOff, transitions, start_state, accepting_states);
    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Search and output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Schedule as Boolean variables
array[Shifts, Days, Weeks] of var bool: sde = array3d(Shifts, Days, Weeks, [
      schedule[week, day] = S(shift)
    | shift in Shifts, day in Days, week in Weeks
]);

%ann: order = dom_w_deg;
ann: order = input_order;
%ann: order;
ann: heuristic = seq_search([
    bool_search(sde[Night, Weekend, ..], order, indomain_max),
    bool_search(sde[Night, .., ..],      order, indomain_max),
    bool_search(sde[.., Weekend, ..],    order, indomain_max),
    bool_search(sde[.., .., ..],         order, indomain_max),
]);
solve :: heuristic satisfy;

function string: display(ShiftsAndOff: shift) = 
    if shift = S(Day) then "D"
    elseif shift = S(Evening) then "E"
    elseif shift = S(Night) then "N"
    else "-" endif;
output [
    concat([ display(fix(schedule[w, d])) ++ " " | d in Days]) ++ "\n"
  | w in Weeks
];
