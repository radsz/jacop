include "globals.mzn";
% second undirected graph: a 5-cycle with two chords
int: N = 5; int: E = 7;
array[1..E] of int: from = [1, 2, 3, 4, 5, 1, 2];
array[1..E] of int: to =   [2, 3, 4, 5, 1, 3, 4];
array[1..E] of int: w =    [1, 2, 1, 2, 1, 3, 2];
array[1..N] of var bool: ns1; array[1..E] of var bool: es1;
array[1..N] of var bool: ns2; array[1..E] of var bool: es2;
array[1..N] of var bool: ns3; array[1..E] of var bool: es3;
array[1..N] of var bool: ns4; array[1..E] of var bool: es4;
array[1..E] of var bool: es5;
var 0..20: K1; var 0..20: K3; var 0..20: K5;
constraint bounded_path(N, E, from, to, w, 2, 5, ns1, es1, K1) /\ K1 <= 4;
constraint tree(N, E, from, to, 1, ns2, es2) /\ sum(ns2) = 2;
constraint steiner(N, E, from, to, w, ns3, es3, K3) /\ ns3[1] /\ ns3[4] /\ K3 <= 4;
constraint path(N, E, from, to, 3, 1, ns4, es4);
constraint weighted_spanning_tree(N, E, from, to, w, es5, K5) /\ K5 <= 5;
constraint connected(from, to, ns2, es2);
solve satisfy;
