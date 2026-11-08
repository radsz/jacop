include "disjunctive_setup.mzn";
array[1..4] of var opt 0..6: s;
array[1..4] of int: d = [2, 1, 2, 1];
array[1..4] of int: f = [1, 2, 1, 2];
array[1..2, 1..2] of int: t = [| 0, 2 | 1, 0 |];
constraint disjunctive_setup(s, d, f, t);
constraint forall(i in 1..4)(occurs(s[i]) -> deopt(s[i]) + d[i] <= 7);
constraint sum(i in 1..4)(bool2int(occurs(s[i]))) >= 3;
solve satisfy;
