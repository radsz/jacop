include "globals.mzn";
array[1..5] of var 1..3: bin;
array[1..3] of var 0..9: load;
constraint bin_packing_load(load, bin, [3, 2, 4, 1, 2]);
constraint bin_packing_capa([6, 5, 7], bin, [3, 2, 4, 1, 2]);
constraint load[1] >= 2;
solve satisfy;
