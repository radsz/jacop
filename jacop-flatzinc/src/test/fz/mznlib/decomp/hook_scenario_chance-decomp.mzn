% The expansion of hook_scenario_chance.mzn: one Boolean per scenario and a weighted sum.
array[0..3] of var -1..3: x;
var -40..40: z;
constraint x[1] != 1;
array[1..4, 1..5] of int: a = [| 1, 1, 0, 0, 1
                               | 0, 2, -1, 1, 0
                               | -1, 0, 1, 1, 0
                               | 1, 1, 1, 1, 0 |];
array[1..5] of var int: y :: no_output = [x[0], x[1], x[2], x[3], x[0]];
array[1..4] of int: b = [3, 2, 1, 4];
array[1..4] of int: p = [3, 2, 4, 1];
array[1..4] of var bool: ok :: no_output;
constraint forall(s in 1..4)(ok[s] <-> sum(i in 1..5)(a[s, i] * y[i]) <= b[s]);
constraint sum(s in 1..4)(p[s] * bool2int(ok[s])) >= 6;
constraint z = 5 * x[0] - 10 * x[1] + 15 * x[2];
solve satisfy;
