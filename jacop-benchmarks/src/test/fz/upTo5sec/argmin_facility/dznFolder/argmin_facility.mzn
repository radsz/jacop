% Facility location: each customer goes to the nearest open facility (arg_min over a variable
% cost row), minimise fixed costs plus distances. Branches on the open decisions.
include "globals.mzn";
int: f; int: c; int: seed;
array[1..c, 1..f] of int: dist = array2d(1..c, 1..f, [ 1 + ((i * 7919 + j * 104729 + seed * 31) mod 40) | i in 1..c, j in 1..f]);
array[1..f] of int: fixed = [ 20 + ((j * 15485863 + seed) mod 30) | j in 1..f];
array[1..f] of var bool: open;
array[1..c, 1..f] of var 1..1000: eff;
constraint forall(i in 1..c, j in 1..f)(eff[i,j] = dist[i,j] + 900 * (1 - bool2int(open[j])));
array[1..c] of var 1..f: to;
constraint forall(i in 1..c)(to[i] = arg_min(row(eff, i)));
constraint forall(i in 1..c)(open[to[i]]);
var int: obj = sum(j in 1..f)(fixed[j] * bool2int(open[j])) + sum(i in 1..c)(dist[i, to[i]]);
solve :: seq_search([bool_search(open, input_order, indomain_min), int_search(to, input_order, indomain_min)]) minimize obj;
output ["open = \(open);\nto = \(to);\nobj = \(obj);\n"];
