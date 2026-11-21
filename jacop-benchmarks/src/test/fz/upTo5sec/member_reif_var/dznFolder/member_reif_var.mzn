% Exactly k rows contain their target t[r] (reified int member), where each target is a variable
% with two candidate values, so a row can contain its target before the target is fixed. Fixed row
% sums and column-sum windows. Search fixes the matrix first, then the targets.
include "globals.mzn";
int: n; int: d; int: k;
array[1..n, 1..n] of var 1..d: x;
array[1..n] of var 1..d: t;
array[1..n] of var bool: b;
constraint forall(r in 1..n)(b[r] = member(row(x, r), t[r]));
constraint sum(b) = k;
constraint forall(r in 1..n)(t[r] in {1 + (r mod d), 1 + ((r + 1) mod d)});
constraint forall(r in 1..n)(sum(row(x, r)) = n + r);
constraint forall(c in 1..n)(sum(col(x, c)) in n + 1 .. n + 3);
solve :: seq_search([int_search([x[r,c] | r, c in 1..n], input_order, indomain_min), int_search(t, input_order, indomain_min)]) satisfy;
output ["x = \(x);\nt = \(t);\nb = \(b);\n"];
