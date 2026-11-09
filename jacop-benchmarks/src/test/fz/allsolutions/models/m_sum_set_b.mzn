include "globals.mzn";
var set of 0..4: s; var set of 0..4: t;
var 0..20: w; var 0..30: u;
constraint sum_set([0, 1, 2, 3, 4], [2, 2, 3, 0, 1], s, w);
constraint sum_set([0, 1, 2, 3, 4], [1, 4, 2, 3, 5], t, u);
constraint w = u /\ card(s) >= 2;
solve satisfy;
