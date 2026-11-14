include "globals.mzn";

int: n = 3;

array[1..n] of var 1..n: x;

constraint
   alldifferent(x)
;

solve :: warm_start(x, [3, 2, 1]) :: int_search(x, input_order, indomain_min)satisfy;

% solve :: warm_start([x[1]], [3])
%       :: warm_start([x[3]], [1])
%       :: int_search(x, input_order, indomain_min)satisfy;

% solve :: seq_search([warm_start(x, [3, 2, 1]), int_search(x, input_order, indomain_min)]) satisfy;
