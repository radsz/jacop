include "globals.mzn";
% second directed graph: 5 nodes, a cycle with chords, other roots and weights
int: N = 5; int: E = 8;
array[1..E] of int: from = [1, 2, 3, 4, 5, 1, 3, 2];
array[1..E] of int: to =   [2, 3, 4, 5, 1, 3, 5, 5];
array[1..E] of int: w =    [2, 1, 3, 1, 2, 2, 1, 4];
array[1..N] of var bool: ns1; array[1..E] of var bool: es1;
array[1..N] of var bool: ns2; array[1..E] of var bool: es2;
array[1..N] of var bool: ns3; array[1..E] of var bool: es3;
array[1..N] of var bool: ns4; array[1..E] of var bool: es4;
array[1..E] of var bool: es5;
var 0..20: K1; var 0..20: K3; var 0..20: K5;
constraint bounded_dpath(N, E, from, to, w, 2, 1, ns1, es1, K1) /\ K1 <= 6;
constraint dtree(N, E, from, to, 3, ns2, es2) /\ ns2[2];
constraint dsteiner(N, E, from, to, w, 1, ns3, es3, K3) /\ ns3[5] /\ K3 <= 4;
constraint dreachable(N, E, from, to, 4, ns4, es4) /\ sum(es4) <= 3;
constraint d_weighted_spanning_tree(N, E, from, to, w, 2, es5, K5) /\ K5 <= 8;
constraint dpath(N, E, from, to, 1, 4, ns1, es1) \/ true;
solve satisfy;
