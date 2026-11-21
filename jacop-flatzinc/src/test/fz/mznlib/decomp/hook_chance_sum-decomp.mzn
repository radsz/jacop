% The expansion of hook_chance_sum.mzn: the 8 joint scenarios of the three weights, one Boolean per
% scenario and a weighted sum over 4^3.
array[0..2] of var 0..2: x;
var 0..12: c;
array[1..3, 1..2] of int: v = [| 1, 3 | 2, 2 | 0, 5 |];
array[1..3, 1..2] of int: p = [| 1, 3 | 2, 2 | 3, 1 |];
array[0..7] of var bool: ok :: no_output;
constraint forall(s in 0..7)(
  ok[s] <-> sum(i in 1..3)(v[i, (s div pow(2, i - 1)) mod 2 + 1] * x[i - 1]) <= c);
constraint sum(s in 0..7)(product(i in 1..3)(p[i, (s div pow(2, i - 1)) mod 2 + 1]) * bool2int(ok[s]))
  >= 3 * 4 * 4;
solve satisfy;
