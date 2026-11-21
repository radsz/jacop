% Package installation: every installed package needs its dependencies installed.
int: n = 20;
array[1..n] of set of 1..n: deps = [
  {}, {1}, {1}, {2,3}, {2}, {4}, {5,6}, {3}, {8}, {7,9},
  {1}, {11}, {11,12}, {5}, {14,8}, {13}, {16,10}, {15}, {6,18}, {}];
array[1..n] of int: size = [3,2,4,1,2,5,3,2,1,4,2,3,1,2,3,2,1,4,2,6];
% alternative providers: need at least one of each group
array[1..3] of set of 1..n: oneof = [{10,17}, {19,15}, {12,20}];
set of 1..n: target = {7};
array[1..2,1..2] of int: conflicts = [|9,13|18,12|];
var set of 1..n: inst;
constraint forall(p in 1..n)(p in inst -> inst superset deps[p]);
constraint inst superset target;
constraint forall(g in 1..3)(card(inst intersect oneof[g]) >= 1);
constraint forall(c in 1..2)(not (conflicts[c,1] in inst /\ conflicts[c,2] in inst));
var int: total = sum(p in 1..n)(bool2int(p in inst) * size[p]);
solve minimize total;
output ["inst = \(inst);\ntotal = \(total);\n"];
