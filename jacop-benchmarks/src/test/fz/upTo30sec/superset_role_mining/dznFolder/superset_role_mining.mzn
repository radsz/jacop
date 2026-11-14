% Assign roles to users so that granted permissions are a superset of what each user needs,
% minimising excess permissions and number of role assignments.
int: nu = 8;
int: nr = 7;
int: np = 12;
array[1..nr] of set of 1..np: grants = [
  {1,2,3}, {4,5}, {6,7,8}, {1,4,9}, {10,11}, {2,6,12}, {3,5,7,11}];
array[1..nu] of set of 1..np: need = [
  {1,2}, {4,5,9}, {6,8}, {1,10}, {2,12}, {3,5,11}, {7,10,11}, {1,4,6}];
array[1..nu] of var set of 1..nr: roles;
array[1..nu] of var set of 1..np: perms;
constraint forall(u in 1..nu)(
  perms[u] = array_union(r in 1..nr)(if r in roles[u] then grants[r] else {} endif));
constraint forall(u in 1..nu)(perms[u] superset need[u]);
var int: excess = sum(u in 1..nu)(card(perms[u]) - card(need[u]));
var int: obj = 10 * excess + sum(u in 1..nu)(card(roles[u]));
solve minimize obj;
output ["roles = \(roles);\nobj = \(obj);\n"];
