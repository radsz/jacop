include "globals.mzn";
% Negated, reified and half-reified table over integers (the standard library
% cannot reify a Boolean table, so it has no decomposition to compare against),
% with a repeated variable and a fixed variable in the scope.
array[1..4] of var 0..3: x;
array[1..3] of var 0..1: y;
array[1..4] of var bool: b;
var 1..1: one;
constraint not table([x[1], x[2], x[3]], [|0,1,2|1,1,1|2,3,0|3,3,3|0,0,0|1,2,3|]);
constraint b[1] <-> table([x[2], x[3], x[2]], [|1,0,1|2,2,2|3,1,2|0,0,1|]);
constraint b[2] -> table([x[3], x[4]], [|0,1|1,2|2,3|3,0|]);
constraint b[3] <-> table([x[4], one, x[1]], [|0,1,3|1,0,1|2,1,2|3,1,0|]);
constraint b[4] -> table(y, [|1,0,1|0,1,1|]);
constraint not table(y, [|0,0,0|]);
constraint b[1] \/ b[2];
solve satisfy;
output ["x=\(x) y=\(y) b=\(b)\n"];
