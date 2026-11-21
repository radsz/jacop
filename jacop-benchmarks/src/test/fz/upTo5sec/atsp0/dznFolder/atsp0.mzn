include "globals.mzn";
% asymmetric TSP with a 0-based successor array, branch and bound with fixed search, no restarts
int: n;
array[1..n,1..n] of int: c;
array[0..n-1] of var 0..n-1: x;
var int: cost;
constraint cost = sum(i in 0..n-1)(c[i+1,x[i]+1]);
constraint circuit(x);
solve :: int_search(x, first_fail, indomain_min) minimize cost;
