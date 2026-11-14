% Cross-checked regression test, written for the global cardinality review (models that rely on global_cardinality).
% Search annotation made input_order/indomain_min on all decision variables, so
% every solver reaches the same solution.
% Nurse rostering: daily shift coverage and per-nurse workload are GCC with bounds.
include "globals.mzn";
int: nurses = 5; int: days = 6;
set of int: SHIFT = 0..3; % 0 = off, 1 = day, 2 = evening, 3 = night
array[1..nurses, 1..days] of var SHIFT: r;
% coverage per day: off, day, evening, night
constraint forall(d in 1..days)(global_cardinality_low_up_closed([r[n,d] | n in 1..nurses], [0,1,2,3], [1,2,1,1], [2,3,2,2]));
% per nurse over the horizon
constraint forall(n in 1..nurses)(global_cardinality_low_up([r[n,d] | d in 1..days], [0,3], [1,0], [3,2]));
% no day or evening shift right after a night shift
constraint forall(n in 1..nurses, d in 1..days-1)(r[n,d] = 3 -> r[n,d+1] in {0,3});
% at most 2 night shifts in a row
constraint forall(n in 1..nurses, d in 1..days-2)(r[n,d] = 3 /\ r[n,d+1] = 3 -> r[n,d+2] != 3);
% fewest shift changes from one day to the next
var 0..nurses*days: changes = sum(n in 1..nurses, d in 1..days-1)(bool2int(r[n,d] != r[n,d+1]));
solve :: seq_search([
    int_search([r[n,d] | d in 1..days, n in 1..nurses], input_order, indomain_min),
    int_search(array1d(r), input_order, indomain_min, complete)])
  minimize changes;
output ["changes = \(changes);\nr = \(r);\n"];
