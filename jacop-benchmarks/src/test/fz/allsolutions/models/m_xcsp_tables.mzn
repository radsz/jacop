include "globals.mzn";
include "fzn_xcsp_negative_table.mzn";
include "fzn_xcsp_short_table.mzn";
% a negative table on x and a short table with wildcard -1 on y
array[1..3] of var 0..3: x;
array[1..3] of var 0..3: y;
constraint fzn_xcsp_negative_table(x, [|0, 1, 2|1, 1, 1|2, 2, 0|3, 0, 1|0, 0, 0|]);
constraint fzn_xcsp_short_table(y, [|0, -1, 2|1, 1, -1|-1, 3, 3|2, 0, 1|], -1);
constraint x[1] <= y[1];
solve satisfy;
