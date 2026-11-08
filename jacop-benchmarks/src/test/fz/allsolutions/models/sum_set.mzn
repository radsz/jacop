include "globals.mzn";
var set of 1..5: s;
var 0..20: w;
constraint sum_set([1, 2, 3, 4, 5], [3, 1, 4, 1, 5], s, w);
constraint w <= 6;
solve satisfy;
