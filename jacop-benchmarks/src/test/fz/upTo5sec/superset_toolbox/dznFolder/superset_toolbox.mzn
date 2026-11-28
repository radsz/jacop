% Load a van with tools under a weight limit; a job can be served iff the van's tools are a
% superset of the tools the job requires.
int: nt = 14;
int: nj = 12;
array[1..nt] of int: weight = [4,2,6,3,5,1,7,2,4,3,5,6,2,3];
array[1..nj] of set of 1..nt: needs = [
  {1,2}, {3}, {2,4,6}, {5,7}, {8,9}, {1,10,6}, {11,12},
  {3,13}, {4,14}, {9,10,13}, {5,6,8}, {7,12,14}];
array[1..nj] of int: pay = [7,6,9,11,8,10,12,7,6,11,9,14];
int: cap = 25;
var set of 1..nt: van;
array[1..nj] of var bool: served;
constraint sum(t in 1..nt)(bool2int(t in van) * weight[t]) <= cap;
constraint forall(j in 1..nj)(served[j] <-> van superset needs[j]);
constraint sum(j in 1..nj)(bool2int(served[j])) <= 6;
var int: obj = sum(j in 1..nj)(bool2int(served[j]) * pay[j]);
solve maximize obj;
output ["van = \(van);\nserved = \(served);\nobj = \(obj);\n"];
