include "globals.mzn";
% bin_packing_capa where the bin variables do not reach the first bin: capacities stay indexed by bin.
array[1..3] of var 2..3: bin;
constraint bin_packing_capa([1, 3, 4], bin, [2, 2, 1]);
solve satisfy;
output ["bin=\(bin)\n"];
