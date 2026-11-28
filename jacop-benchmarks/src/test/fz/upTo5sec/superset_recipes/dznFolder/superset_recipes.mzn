% Stock a pantry within budget; a dish can be cooked iff the pantry is a superset of its ingredients.
int: ni = 16;
int: nd = 14;
array[1..nd] of set of 1..ni: ing = [
  {1,2,3}, {1,4}, {2,5,6}, {3,7}, {4,8,9}, {5,10}, {6,11,12},
  {7,13}, {8,14}, {1,9,15}, {10,16}, {2,12,13}, {3,11,14}, {4,15,16}];
array[1..ni] of int: price = [2,3,2,4,3,3,2,5,2,4,3,2,3,4,2,3];
array[1..nd] of int: value = [6,5,7,4,8,5,6,6,5,7,6,6,7,8];
int: budget = 22;
var set of 1..ni: pantry;
array[1..nd] of var bool: cook;
constraint forall(d in 1..nd)(cook[d] <-> pantry superset ing[d]);
constraint sum(i in 1..ni)(bool2int(i in pantry) * price[i]) <= budget;
var int: score = sum(d in 1..nd)(bool2int(cook[d]) * value[d]);
solve maximize score;
output ["pantry = \(pantry);\ncook = \(cook);\nscore = \(score);\n"];
