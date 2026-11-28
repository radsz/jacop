% Cross-checked regression test, written for the global cardinality review (models that rely on global_cardinality).
% Search annotation made input_order/indomain_min on all decision variables, so
% every solver reaches the same solution.
% Assign tasks to workers with skill restrictions; workloads are GCC counters.
% Minimise the spread between the busiest and the idlest worker.
include "globals.mzn";
int: tasks = 42; int: workers = 7;
array[1..tasks] of set of int: skill = [ {w | w in 1..workers where (t * 7 + w * 3) mod 5 != 0} | t in 1..tasks ];
array[1..tasks] of var 1..workers: a;
array[1..workers] of var 0..tasks: load;
constraint forall(t in 1..tasks)(a[t] in skill[t]);
constraint global_cardinality(a, [w | w in 1..workers], load);
constraint forall(t in 1..tasks-1 where t mod 4 != 0)(a[t] != a[t+1]);
var 0..tasks: spread = max(load) - min(load);
solve :: seq_search([
    int_search(array1d(a) ++ array1d(load), input_order, indomain_min, complete)])
  minimize spread;
output ["spread = \(spread);\na = \(a);\n"];
