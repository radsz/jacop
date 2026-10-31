% Each row's arg_max (the first column holding the row maximum) is a distinct column, on a
% variable matrix with fixed row and column sums and a zero diagonal. Search on the matrix only,
% so the index is reached through arg_max propagation. Minimises a weighted sum of the indices.
include "globals.mzn";
int: n; int: d;
array[1..n, 1..n] of var 0..d: x;
array[1..n] of var 1..n: p;
constraint forall(r in 1..n)(arg_max(row(x, r)) = p[r]);
constraint all_different(p);
constraint forall(r in 1..n)(sum(row(x, r)) = d + r mod 2);
constraint forall(c in 1..n)(sum(col(x, c)) = d + (c + 1) mod 2);
constraint forall(r in 1..n)(x[r, r] = 0);
var int: obj = sum(r in 1..n)(r * p[r]);
solve :: int_search([x[r,c] | r, c in 1..n], input_order, indomain_min) minimize obj;
output ["x = \(x);\np = \(p);\nobj = \(obj);\n"];
