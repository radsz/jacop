% The model of ../hook_table_reif_wide.mzn with the tables stated as exists/forall.
array[1..7] of var 0..2: x;
array[1..2] of var bool: b;
array[1..5, 1..7] of int: t1 = [|0,1,2,0,1,2,0|1,1,1,1,1,1,1|2,0,1,2,0,1,2|0,0,0,1,1,1,2|2,2,1,1,0,0,0|];
array[1..4, 1..7] of int: t2 = [|1,1,1,1,1,1,1|0,1,0,1,0,1,0|2,2,2,0,0,0,1|0,0,0,1,1,1,2|];
array[1..7] of var int: y = [x[7], x[6], x[5], x[4], x[3], x[2], x[1]];
array[1..6] of var int: z = [x[1], x[3], x[5], x[7], x[2], x[4]];
constraint b[1] <-> exists(r in 1..5)(forall(j in 1..7)(x[j] = t1[r, j]));
constraint b[2] -> exists(r in 1..4)(forall(j in 1..7)(y[j] = t2[r, j]));
constraint not exists(v in 0..2)(forall(j in 1..6)(z[j] = v));
constraint x[1] + x[2] + x[3] >= 2 /\ x[4] + x[5] <= 3;
solve satisfy;
output ["x=\(x) b=\(b)\n"];
