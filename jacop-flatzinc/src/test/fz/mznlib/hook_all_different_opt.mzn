include "globals.mzn";
% all_different on optional variables with 0 in the domains, on AlldifferentExcept with a value
% below the domains for absent variables. o and v name the parts of x so that both FlatZinc
% files print the same solutions.
array[1..4] of var bool: o;
array[1..4] of var 0..2: v;
array[1..4] of var opt 0..2: x = [if o[i] then v[i] else <> endif | i in 1..4];
constraint forall(i in 1..4)(not o[i] -> v[i] = 0);
constraint all_different(x);
var bool: o2;
var 1..3: v2;
constraint not o2 -> v2 = 1;
array[1..3] of var opt 1..3: y = [<>, if o2 then v2 else <> endif, 3];
constraint all_different(y);
constraint all_different([x[2], x[2], x[1]]);
solve satisfy;
