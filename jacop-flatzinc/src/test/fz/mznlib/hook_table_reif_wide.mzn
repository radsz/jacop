include "globals.mzn";
% Reified table over seven variables; the standard library cannot reify a table over
% more than five variables, so decomp/hook_table_reif_wide.mzn states the same model with exists/forall.
array[1..7] of var 0..2: x;
array[1..2] of var bool: b;
array[1..5, 1..7] of int: t1 = [|0,1,2,0,1,2,0|1,1,1,1,1,1,1|2,0,1,2,0,1,2|0,0,0,1,1,1,2|2,2,1,1,0,0,0|];
array[1..4, 1..7] of int: t2 = [|1,1,1,1,1,1,1|0,1,0,1,0,1,0|2,2,2,0,0,0,1|0,0,0,1,1,1,2|];
constraint b[1] <-> table(x, t1);
constraint b[2] -> table([x[7], x[6], x[5], x[4], x[3], x[2], x[1]], t2);
constraint not table([x[1], x[3], x[5], x[7], x[2], x[4]], [|0,0,0,0,0,0|1,1,1,1,1,1|2,2,2,2,2,2|]);
constraint x[1] + x[2] + x[3] >= 2 /\ x[4] + x[5] <= 3;
solve satisfy;
output ["x=\(x) b=\(b)\n"];
