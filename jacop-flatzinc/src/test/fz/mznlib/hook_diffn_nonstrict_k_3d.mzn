% diffn_nonstrict_k in 3 dimensions (posted as DiffnK): a box with size 0 in some dimension is
% ignored. Each box is in the shelf (all sizes positive) or out of it (all sizes 0), as in
% products-and-shelves, and box 1 has its own size 0 in the second dimension as well.
include "globals.mzn";
array[1..3, 1..3] of var 0..2: p;
array[1..3] of var bool: pr;
var 0..1: w;
array[1..3, 1..3] of var 0..2: s = array2d(1..3, 1..3,
  [2 * pr[1], w * pr[1], 1 * pr[1],  1 * pr[2], 2 * pr[2], 1 * pr[2],  2 * pr[3], 1 * pr[3], 2 * pr[3]]);
constraint forall(i in 1..3, j in 1..3)(p[i, j] + s[i, j] <= 2);
constraint sum(pr) >= 2;
constraint diffn_nonstrict_k(p, s);
solve satisfy;
