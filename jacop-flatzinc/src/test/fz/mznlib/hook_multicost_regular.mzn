include "globals.mzn";
% Three cost_regular over the same word and automaton, merged into one MultiCostRegular:
% shifts D, E, N, O (1..4); after a night only a night or a day off. Hours, nights and days off
% have tight bounds, so the counters conflict.
array[1..6] of var 1..4: x;
var 30..36: hours;
var 1..2: nights;
var 2..3: off;
array[1..2, 1..4] of 0..2: d = [| 1, 1, 2, 1 | 0, 0, 2, 1 |];
array[1..2, 1..4] of int: h = [| 8, 8, 10, 0 | 8, 8, 10, 0 |];
array[1..2, 1..4] of int: n = [| 0, 0, 1, 0 | 0, 0, 1, 0 |];
array[1..2, 1..4] of int: o = [| 0, 0, 0, 1 | 0, 0, 0, 1 |];
constraint cost_regular(x, 2, 4, d, 1, 1..2, h, hours);
constraint cost_regular(x, 2, 4, d, 1, 1..2, n, nights);
constraint cost_regular(x, 2, 4, d, 1, 1..2, o, off);
solve satisfy;
output ["x=\(x) hours=\(hours) nights=\(nights) off=\(off)\n"];
