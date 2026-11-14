% diffn_k with variable sizes in 3 dimensions (posted as DiffnK), boxes numbered from 0. A box
% with size 0 in some dimension still overlaps a box it lies strictly inside.
include "globals.mzn";
array[0..2, 1..3] of var 0..1: p;
var 1..2: a;
var 0..1: b;
var {1, 3}: c;
array[0..2, 1..3] of var int: s = array2d(0..2, 1..3, [1, 1, a,  b, 1, 1,  1, c, 1]);
constraint diffn_k(p, s);
solve satisfy;
