include "globals.mzn";
% alldifferent over optional values: absent values are ignored, at least two are present
array[1..4] of var opt 1..3: x;
constraint alldifferent(x);
constraint sum(i in 1..4)(bool2int(occurs(x[i]))) >= 2;
solve satisfy;
