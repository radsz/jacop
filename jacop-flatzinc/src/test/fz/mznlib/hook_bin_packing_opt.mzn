include "globals.mzn";
% bin_packing, bin_packing_capa and bin_packing_load with optional bins: absent items are not packed.
array[1..4] of var bool: p;
array[1..4] of var 1..3: x;
array[1..4] of var opt 1..3: bin = [if p[i] then x[i] else <> endif | i in 1..4];
array[1..3] of var 0..6: load;
constraint bin_packing(5, bin, [2, 3, 2, 1]);
constraint bin_packing_capa([4, 3, 5], bin, [2, 3, 2, 1]);
constraint bin_packing_load(load, bin, [2, 3, 2, 1]);
constraint sum(p) >= 3;
solve satisfy;
output ["p=\(p) x=\(x) load=\(load)\n"];
