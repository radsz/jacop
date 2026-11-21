% diffn_k with fixed sizes in 3 dimensions (posted as geost), boxes numbered from 0.
include "globals.mzn";
array[0..2, 1..3] of var 0..1: p;
array[0..2, 1..3] of int: s = array2d(0..2, 1..3, [1, 1, 1,  1, 1, 1,  1, 2, 1]);
constraint diffn_k(p, s);
solve satisfy;
