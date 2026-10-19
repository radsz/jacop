% Cross-checked regression test, from Hakan Kjellerstrand's map.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: value precedence (seq_precede_chain, value_precede) and member, also reified, added to the coloring.
% Map coloring in MiniZinc, with value precedence symmetry breaking.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 6; % number of countries
array[1..n] of var 1..4: country; % = [belgium, denmark, france, germany, netherlands, luxembourg];
array[1..n] of var 1..4: country2;
array[1..n,1..n] of 0..1: connections = array2d(1..n, 1..n,
[    0,   0,   1,   1,   1,   1,
     0,   0,   0,   1,   0,   0,
     1,   0,   0,   1,   1,   0,
     1,   1,   1,   0,   1,   1,
     1,   0,   1,   1,   0,   0,
     1,   0,   0,   1,   0,   0
]);
var bool: uses_four;

predicate coloring(array[int,int] of int: conn, array[int] of var int: countries, int: num_countries) =
           forall(i,j in 1..num_countries where i < j /\ conn[i,j] = 1) (
              countries[i] != countries[j]
           )
;

constraint
    coloring(connections, country, n) /\
    seq_precede_chain(country) /\
    (uses_four <-> member(country, 4)) /\
    coloring(connections, country2, n) /\
    value_precede(1, 2, country2) /\
    value_precede(2, 3, country2) /\
    member(country2, 1) /\
    country2[2] = 1
;

solve satisfy;

output [
   show(country), " ", show(uses_four), " ", show(country2), "\n"
];
