% Weighted set cover: choose candidate sets whose union is a superset of the universe.
int: n = 24;
int: m = 18;
set of int: U = 1..n;
array[1..m] of set of int: S = [
  {1,2,3,7,11}, {2,4,6,8,10,12}, {3,5,9,13,17}, {1,14,15,16},
  {17,18,19,20}, {5,10,15,20,21}, {21,22,23,24}, {6,12,18,24},
  {7,8,9,19,22}, {11,13,23}, {4,14,16,18}, {1,5,9,13,21,24},
  {2,3,20,22}, {10,11,12,13,14}, {15,16,17,23,24}, {6,7,8,19},
  {3,4,9,10,18,22}, {1,2,11,12,20,23}];
array[1..m] of int: cost = [5,6,5,4,4,5,4,4,5,3,4,6,4,5,5,4,6,6];
array[1..m] of var bool: pick;
var set of U: covered = array_union(i in 1..m)(if pick[i] then S[i] else {} endif);
constraint covered superset U;
var int: total = sum(i in 1..m)(bool2int(pick[i]) * cost[i]);
solve minimize total;
output ["pick = \(pick);\ntotal = \(total);\n"];
