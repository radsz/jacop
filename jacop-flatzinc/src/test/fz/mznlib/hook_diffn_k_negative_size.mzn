% diffn_k and diffn_nonstrict_k with a size that can be negative use the decomposition, since
% DiffnK requires sizes of at least 0.
include "globals.mzn";
array[1..2, 1..3] of var 0..1: p;
var -1..1: n;
array[1..2, 1..3] of var int: s = array2d(1..2, 1..3, [1, 1, n,  1, 1, 1]);
constraint diffn_k(p, s);
array[1..2, 1..3] of var 0..1: q;
array[1..2, 1..3] of var int: t = array2d(1..2, 1..3, [1, n, 1,  1, 1, 1]);
constraint diffn_nonstrict_k(q, t);
solve satisfy;
