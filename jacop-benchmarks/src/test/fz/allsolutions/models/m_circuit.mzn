include "globals.mzn";
% a Hamiltonian circuit over nodes 1..5 (index set from 1, so jacop_circuit) with one arc banned
array[1..5] of var 1..5: x;
constraint circuit(x);
constraint x[1] != 2;
constraint x[3] < x[4];
solve satisfy;
