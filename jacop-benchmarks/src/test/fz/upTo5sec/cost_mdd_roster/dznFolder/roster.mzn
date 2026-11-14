% Rostering with one cost MDD per employee (see scripts/gen.py).
include "globals.mzn";
int: E; int: D; int: S; int: K;
array[1..D, 1..S] of int: demand;
array[1..K] of int: N;
array[1..K] of int: E_;
array[int] of int: LEVEL; array[int] of int: FROM; array[int] of int: COST; array[int] of int: TO;
array[int] of set of int: LABEL;
array[1..K] of int: noff = [sum(N[1..k-1]) | k in 1..K];
array[1..K] of int: eoff = [sum(E_[1..k-1]) | k in 1..K];
array[1..E, 1..D] of var 1..S: x;
array[1..E] of var 0..1000: c;
constraint forall(e in 1..E)(
  cost_mdd(x[e, ..], N[e], [LEVEL[noff[e] + i] | i in 1..N[e]], E_[e],
           [FROM[eoff[e] + i] | i in 1..E_[e]], [LABEL[eoff[e] + i] | i in 1..E_[e]],
           [COST[eoff[e] + i] | i in 1..E_[e]], [TO[eoff[e] + i] | i in 1..E_[e]], c[e]));
constraint forall(d in 1..D, s in 2..S)(count(x[.., d], s) >= demand[d, s]);
var int: objective = sum(c);
solve :: int_search([x[e, d] | d in 1..D, e in 1..E], first_fail, indomain_min) minimize objective;
