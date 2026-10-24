%-----------------------------------------------------------------------------
% Nurse scheduling problem
%
% Nina Narodytska
% 01.12.2007
%
% The nurse scheduling problem consists of assigning nurses to shifts to
% satisfy  nurses demand for each day.
% The model includes the following constraints:
% - each shift has a minimum required number of nurses
% - various regulation rules on each nurse schedule
% To run the model you need a data file from ./period_14 or ./period_28 to
% specify the minimum number of nurses required on each day[*]
%
%[*]Original benchmarks come from  http://www.projectmanagment.ugent.be/nsp.php
% They specify minimal required staff allocation for each shift and individual
% preferences for each nurse.  We ignore these preference and replace them with
% a set of constraints that model common workload restrictions for all nurses.
% The number of nurses in each instance is set to the maximal number of nurses
% required for any day over the period multiplied by 1.5.

% To test the model:
%
% nsp_1.mzn --data test.dzn
%-----------------------------------------------------------------------------

include "globals.mzn";
include "test.rules";

%-------------------------------------------------
% Model parameters
%-------------------------------------------------


int: n_nurses;         % The number of nurses
int: sched_period;     % The scheduling period
int: n_shifts;         % The number of shifts:
                       %    1 stands for a day shift
                       %    2 stands for an evening shift
                       %    3 stands for a night shift
                       %    4 stands for day-off
int: n_rules;          % The number of regulation rules

set of int: period           = 1..sched_period;
set of int: shifts           = 1..n_shifts;
set of int: shifts_and_off   = 1..n_shifts + 1;
set of int: nurses           = 1..n_nurses;
set of int: rules            = 1..n_rules;



array [period, shifts] of 0..n_nurses: nurses_coverage;
% nurses_coverage[i,j] -- required number of nurses for shift j in day i

% additional regulation rules
array [rules] of set of int: rules_sets;
array [rules] of int: rules_lbs;
array [rules] of int: rules_ubs;
array [rules] of int: rules_windows;


%-------------------------------------------------
% Model variables
%-------------------------------------------------

array [nurses, period] of var shifts_and_off:  nurses_schedule;
array [period, shifts] of var int:             coverage;
array [shifts] of var int:                     shifts_values;

%-------------------------------------------------
% Model constraints
%-------------------------------------------------
%-----------------
%-- nurses demand
%------------------
%daily nurses demand
constraint
   forall (i in period, j in shifts) (
            coverage[i,j] >= nurses_coverage[i,j]
    );

% encoding for shifts
% 1 stands for a day shift
% 2 stands for an evening shift
% 3 stands for a night shift
constraint
    forall (j in shifts) (
            shifts_values[j] = j
    );

predicate day_distribute (int: i) = (
	 let {
	 	array [shifts] of var int: row_coverage =
	 		[coverage[i,j]| j in shifts]
	 } in
	 	distribute (row_coverage, shifts_values, [nurses_schedule[j,i]| j in nurses])
	);

% the distribute constraint
constraint
	forall (i in period)  (
		(day_distribute (i))
	);

%---------------------
%-- regulation rules
%---------------------

% apply a regulation rule to each nurse schedule
% ith rule to jth nurse
predicate apply_rule_for_nurse (int: i, int: j) =
	 let {
	 	array [period] of var 0..1: rule_for_nurse} in (
		(
			forall (k in period) (
				(nurses_schedule[j,k] in rules_sets[i])<-> rule_for_nurse[k] = 1
			)
			/\
            sliding_sum (rules_lbs[i], rules_ubs[i], rules_windows[i], rule_for_nurse)
		)
);
constraint
	forall (i in rules, j in nurses)  (
		apply_rule_for_nurse (i, j)
	);




solve satisfy;


%-------------------------------------------------
% Output
%--------------------------------------------------


output [
"Problem description: \n",
"\t number of nurses = ", show(n_nurses), "\n",
"\t scheduling period =  ", show(shifts_values), "\n",
"\t coverage matrix = ", show(nurses_coverage), "\n",
"\t lower bounds = ", show(rules_lbs), "\n",
"\t upper bounds = ", show(rules_ubs), "\n",
"\t windows = ", show(rules_windows), "\n",
"\t sets = ", show(rules_sets),"\n \n",
"Solution: \n",
"\t nurses_schedule =   \n \t", show(nurses_schedule), "\n"];
