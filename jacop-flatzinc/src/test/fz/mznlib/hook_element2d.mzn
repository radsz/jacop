% 2D element: a fixed array becomes a table over both indices and the value, an array of
% variables keeps the linearised index.
array[2..3, 0..2] of int: m = array2d(2..3, 0..2, [3, 1, 4, 1, 5, 9]);
var 0..4: r;
var -1..3: c;
var 0..9: v;
constraint m[r, c] = v;
array[1..2, 1..2] of bool: bm = [| true, false | false, false |];
var 1..3: r2;
var 0..2: c2;
var bool: bv;
constraint bm[r2, c2] = bv;
array[1..2, 2..3] of var 0..2: vm;
var 0..3: r3;
var 1..4: c3;
var 0..2: v3;
constraint vm[r3, c3] = v3;
solve satisfy;
