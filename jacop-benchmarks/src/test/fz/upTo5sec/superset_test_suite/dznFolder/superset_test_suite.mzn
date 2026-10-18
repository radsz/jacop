% Test-suite minimisation: covered requirements must be a superset of the mandatory ones;
% optional requirement groups give a bonus when fully covered.
int: nt = 15;
int: nr = 20;
array[1..nt] of set of 1..nr: covers = [
  {1,2,3}, {4,5}, {6,7,8}, {9,10}, {11,12,13}, {14,15}, {16,17}, {18,19,20},
  {1,4,6,9}, {2,5,11,14}, {3,7,16,18}, {8,10,12,19}, {13,15,17,20}, {1,11}, {6,16}];
array[1..nt] of int: runtime = [3,2,3,2,3,2,2,3,5,5,5,5,5,2,2];
set of 1..nr: mandatory = {1,2,4,6,9,11,13};
array[1..4] of set of 1..nr: group = [{14,15}, {16,17,18}, {8,10,12}, {19,20}];
array[1..4] of int: bonus = [4,6,5,4];
var set of 1..nt: suite;
var set of 1..nr: cov = array_union(t in 1..nt)(if t in suite then covers[t] else {} endif);
constraint cov superset mandatory;
array[1..4] of var bool: full;
constraint forall(g in 1..4)(full[g] <-> cov superset group[g]);
var int: obj = sum(t in 1..nt)(bool2int(t in suite) * runtime[t]) - sum(g in 1..4)(bool2int(full[g]) * bonus[g]);
solve minimize obj;
output ["suite = \(suite);\nfull = \(full);\nobj = \(obj);\n"];
