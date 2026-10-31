% Form two disjoint project teams; each team's skills must be a superset of the project needs.
int: nw = 12;
int: ns = 10;
array[1..nw] of set of 1..ns: skill = [
  {1,2}, {3,4}, {5,6}, {7,8}, {9,10}, {1,3,5},
  {2,4,6}, {7,9}, {8,10}, {1,10}, {4,5,7}, {2,6,9}];
array[1..nw] of int: salary = [4,4,4,4,4,6,6,4,4,3,5,5];
array[1..2] of set of 1..ns: need = [{1,2,3,4,5,6}, {5,6,7,8,9,10}];
array[1..2] of var set of 1..nw: team;
array[1..2] of var set of 1..ns: has;
constraint forall(p in 1..2)(
  has[p] = array_union(w in 1..nw)(if w in team[p] then skill[w] else {} endif));
constraint forall(p in 1..2)(has[p] superset need[p]);
constraint team[1] intersect team[2] = {};
var int: cost = sum(p in 1..2, w in 1..nw)(bool2int(w in team[p]) * salary[w]);
solve minimize cost;
output ["team = \(team);\ncost = \(cost);\n"];
