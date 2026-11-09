% The expansion of hook_chance_table.mzn: one Boolean per scenario, true exactly when x is a tuple
% of each of its tables, and the weighted sum of the Booleans.
array[0..2] of var 0..2: x;
var 0..12: p;
var bool: t1 = x[0] in {0, 1};
var bool: t2 = (x[1] = 0 /\ x[2] = 1) \/ (x[1] = 1 /\ x[2] = 2) \/ (x[1] = 2 /\ x[2] = 2);
var bool: t3 = (x[0] = 2 /\ x[2] = 0) \/ (x[0] = 1 /\ x[2] = 1);
var bool: t4 = false;
constraint p = 3 * bool2int(t1 /\ t2) + 2 * bool2int(t3) + 4 * bool2int(t2) + 1
               + 2 * bool2int(t4) + 0 * bool2int(t1 /\ t3);
constraint p >= 6;
solve satisfy;
