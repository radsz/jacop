% The standard library makes the whole model unsatisfiable when kind can take a value outside
% the index set of shape, so the reference states the domain of kind explicitly.
include "globals.mzn";
array[1..2, 1..1] of int: rs = [| 1 | 2 |];
array[1..2, 1..1] of int: ro = [| 0 | 0 |];
array[1..2] of set of 1..2: sh = [{1}, {2}];
array[1..3, 1..1] of var 0..3: x;
array[1..3] of var 0..3: kind;
constraint forall(o in 1..3)(kind[o] in 1..2);
constraint geost(1, rs, ro, sh, x, kind);
solve satisfy;
