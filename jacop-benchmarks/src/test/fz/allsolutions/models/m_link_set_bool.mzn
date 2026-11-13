include "globals.mzn";
% a set of 1..4 linked to its characteristic booleans
var set of 1..4: s;
array[1..4] of var bool: b;
constraint link_set_to_booleans(s, b);
constraint card(s) >= 2;
constraint b[1] -> b[3];
solve satisfy;
