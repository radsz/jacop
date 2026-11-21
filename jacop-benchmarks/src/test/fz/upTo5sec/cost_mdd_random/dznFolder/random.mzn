% K random cost MDDs over shared variables (see scripts/gen.py).
include "globals.mzn";
int: n; int: d; int: m; int: K;
array[1..K, 1..m] of 1..n: scope;
array[1..K] of int: N;
array[1..K] of int: E_;
array[int] of int: LEVEL; array[int] of int: FROM; array[int] of int: COST; array[int] of int: TO;
array[int] of set of int: LABEL;
array[1..K] of int: noff = [sum(N[1..k-1]) | k in 1..K];
array[1..K] of int: eoff = [sum(E_[1..k-1]) | k in 1..K];
array[1..n] of var 1..d: x;
array[1..K] of var 0..10 * m: c;
constraint forall(k in 1..K)(
  cost_mdd([x[scope[k, i]] | i in 1..m], N[k], [LEVEL[noff[k] + i] | i in 1..N[k]], E_[k],
           [FROM[eoff[k] + i] | i in 1..E_[k]], [LABEL[eoff[k] + i] | i in 1..E_[k]],
           [COST[eoff[k] + i] | i in 1..E_[k]], [TO[eoff[k] + i] | i in 1..E_[k]], c[k]));
var int: objective = sum(c);
solve :: int_search(x, first_fail, indomain_min) minimize objective;
