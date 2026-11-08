include "disjunctive_setup.mzn";
array[1..4] of var 0..9: s;
array[1..4] of var 1..2: d;
array[1..4] of int: f = [1, 2, 1, 2];
array[1..2, 1..2] of int: t = [| 0, 2 | 1, 0 |];
constraint disjunctive_setup(s, d, f, t);
constraint forall(i in 1..4)(s[i] + d[i] <= 10);
constraint sum(d) = 6;
solve satisfy;
