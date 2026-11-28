% geost where objects share their kind variable and a variable is both a coordinate and a kind.
include "globals.mzn";
array[1..2, 1..2] of int: rs = [| 1, 1 | 2, 1 |];
array[1..2, 1..2] of int: ro = [| 0, 0 | 0, 0 |];
array[1..2] of set of 1..2: sh = [{1}, {2}];
var 1..2: k;
var 0..2: a;
var 0..2: b;
var 0..2: c;
constraint geost(2, rs, ro, sh, [| a, b | c, b | a, k |], [k, k, 1]);
solve satisfy;
