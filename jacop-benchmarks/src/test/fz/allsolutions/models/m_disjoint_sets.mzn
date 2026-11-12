include "globals.mzn";
var set of 1..4: s;
var set of 1..4: t;
array[1..3] of var set of 1..3: p;
constraint disjoint(s, t);
constraint card(s) >= 1 /\ card(t) <= 2;
constraint partition_set(p, 1..3);
solve satisfy;
