% Product line configuration: a feature requires other features; some features exclude others.
int: nf = 18;
array[1..nf] of set of 1..nf: req = [
  {}, {1}, {1}, {2}, {2,3}, {3}, {4}, {5}, {6}, {1},
  {10}, {10,7}, {11}, {8,9}, {13}, {12,14}, {15}, {16,17}];
array[1..nf] of int: gain = [0,3,4,5,6,4,7,6,5,2,4,8,5,9,6,10,7,12];
array[1..nf] of int: cost = [1,2,2,3,4,2,4,3,3,1,2,5,3,6,4,6,4,8];
array[1..3] of set of 1..nf: excl = [{4,6}, {9,13}, {12,15}];
int: budget = 30;
var set of 1..nf: prod;
constraint 1 in prod;
constraint forall(f in 1..nf)(f in prod -> prod superset req[f]);
constraint forall(k in 1..3)(card(prod intersect excl[k]) <= 1);
constraint sum(f in 1..nf)(bool2int(f in prod) * cost[f]) <= budget;
var int: obj = sum(f in 1..nf)(bool2int(f in prod) * gain[f]);
solve maximize obj;
output ["prod = \(prod);\nobj = \(obj);\n"];
