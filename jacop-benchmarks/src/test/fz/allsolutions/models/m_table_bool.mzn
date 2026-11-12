include "globals.mzn";
array[1..3] of var bool: a;
array[1..4] of var 0..2: x;
constraint table(a, [| true, false, true | false, true, true | true, true, false | false, false, false |]);
constraint table(x[1..2], [| 0, 1 | 1, 2 | 2, 0 | 2, 2 |]);
constraint a[1] -> x[3] > x[4];
solve satisfy;
