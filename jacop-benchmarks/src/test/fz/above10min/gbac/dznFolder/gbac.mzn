%------------------------------------------------------------------------------%
%% Generalised Balanced Academic Curriculum problem
%% 
%% Problem 64 in CSPlib: 
%%   http://www.csplib.org/Problems/prob064/
%%
%% See http://satt.diegm.uniud.it/projects/gbac/
%% for a detailed explanation of the problem.
%%   Note that the distance from the ideal load,
%% which is a part of the objective, is computed
%% using the squared error. This is following
%% http://dx.doi.org/10.1007/978-3-540-88439-2_11
%% and allows the found objective value to be
%% compared with found objectives reported on
%% http://satt.diegm.uniud.it/projects/gbac/
%%
%
%------------------------------------------------------------------------------%
% Model by Jean-Noel Monette
% Modified by Gustav Bjordal
% with help by Fatima Zohra Lebbah, Justin Pearson, and Pierre Flener
%
%------------------------------------------------------------------------------%
% Includes
include "globals.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: n_courses;
set of int: courses = 1..n_courses;
int: n_periods;
set of int: periods = 1..n_periods;
int: n_curricula;
set of int: curricula = 1..n_curricula;
array[curricula] of set of courses: courses_of;
int: n_precedences;
set of int: precedences = 1..n_precedences;
array[precedences,1..2] of int: precedes;

int: min_courses;
int: max_courses;

array[courses] of int: course_load;
int: max_load = sum(c in courses)(course_load[c]);

array [curricula] of int: total_load = [sum(i in courses_of[c])(course_load[i]) | c in curricula];
array [curricula] of int: ideal_load_floor = [total_load[c] div n_periods | c in curricula];
array [curricula] of int: ideal_load_ceil = [total_load[c] div n_periods + (if total_load[c] mod n_periods ==0 then 0 else 1 endif) | c in curricula];

int: n_undesirables;
set of int: undesirables = 1..n_undesirables;
array [undesirables,1..2] of int: undesirable;

%weight of the load balancing
int: w1;
%weight of the undesirable assignment violations
int: w2;


%------------------------------------------------------------------------------%
% Variables

%decision variable
array [courses] of var periods: period_of;


%------------------------------------------------------------------------------%
% Constraints

%course load of all periods for each curriculum
constraint forall(c in curricula)(
  global_cardinality_low_up_closed(
      [period_of[i]|i in courses_of[c]],
      [i|i in periods],
      [min_courses |i in periods],
      [max_courses |i in periods])
);

%prerequisites
constraint forall(i in precedences)(
 period_of[precedes[i,1]] < period_of[precedes[i,2]]
);


%period load
constraint forall(c in curricula)(
  bin_packing_load(
      [load_of[c,p]   |p in periods],
      [period_of[i]   |i in courses_of[c]],
      [course_load[i] |i in courses_of[c]])
);

%violation
var 0..n_undesirables: undesirable_violation = sum(i in undesirables)(
   bool2int(period_of[undesirable[i,1]]==undesirable[i,2])
);

%load of periods
array [curricula,periods] of var 0..max_load: load_of;

%course balance delta
array [curricula,periods] of var 0..max_load: delta;
var int: norm = sum([delta[c,p]*delta[c,p]|c in curricula, p in periods]);

%norm
constraint forall(c in curricula, p in periods)(
  delta[c,p] = max(load_of[c,p]-ideal_load_ceil[c],
                    ideal_load_floor[c]-load_of[c,p])
);

%objective
var int: objective;
constraint objective = w1 * norm + w2 * undesirable_violation;

%------------------------------------------------------------------------------%
% Search and solve item

solve :: int_search(period_of,first_fail,indomain_min,complete) minimize objective;

%------------------------------------------------------------------------------%
% Output

output 
    ["objective = ", show(objective)] ++[";\n"] ++
["period_of = ", show(period_of)] ++ [";\n"];
