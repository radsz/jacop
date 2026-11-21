% Cross-checked regression test, from Hakan Kjellerstrand's bin_packing_me.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: a small instance with the bin_packing_capa and bin_packing globals.
% Bin packing in MiniZinc, with the bin_packing globals.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: num_stuff = 6;
array[1..num_stuff] of int: stuff = [4, 3, 3, 2, 2, 1];
int: num_bins = 3;
array[1..num_stuff] of var 1..num_bins: bin;
array[1..num_bins] of int: capacity = [6, 5, 5];
array[1..num_stuff] of var 1..num_bins: bin2;

solve satisfy;

constraint
  bin_packing_capa(capacity, bin, stuff) /\
  bin[1] = 1 /\ bin[2] <= 2 /\
  bin_packing(6, bin2, stuff) /\
  bin2[1] = 1 /\ bin2[2] = 2 /\ bin2[3] = 3 /\ bin2[4] < bin2[5]
;

output [ "bin: ", show(bin), " bin2: ", show(bin2), "\n" ];
