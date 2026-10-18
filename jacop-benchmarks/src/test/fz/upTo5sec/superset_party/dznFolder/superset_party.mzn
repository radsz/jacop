% Invite guests to a party; a guest is happy iff the invited set is a superset of their friends.
int: ng = 16;
array[1..ng] of set of 1..ng: friends = [
  {2,3}, {1,4}, {1,5}, {2,6}, {3,7}, {4,8}, {5,9}, {6,10},
  {7,11}, {8,12}, {9,13}, {10,14}, {11,15}, {12,16}, {13,1}, {14,2}];
array[1..ng] of int: weight = [3,2,4,1,5,2,3,4,2,5,1,3,4,2,3,5];
int: capacity = 9;
var set of 1..ng: inv;
array[1..ng] of var bool: happy;
constraint card(inv) <= capacity;
constraint forall(g in 1..ng)(happy[g] <-> (g in inv /\ inv superset friends[g]));
var int: obj = sum(g in 1..ng)(bool2int(happy[g]) * weight[g]);
solve maximize obj;
output ["inv = \(inv);\nobj = \(obj);\n"];
