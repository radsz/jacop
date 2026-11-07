%------------------------------------------------------------------------------
% Peaceable Queens
%
% On a n-by-n chessboard, maximize the number of black and white queens on the
% board such that queens from opposing sides do not attack each other. The
% number of black queens must be equal to the number of white queens.
%
% Model by: Hendrik 'Henk' Bierlee
% All known optimal solutions are on https://oeis.org/A250000
% Some insight into the problem is due to Smith et. al, CP'2004
% Thanks to Jip J. Dekker for the idea to use regular.
%------------------------------------------------------------------------------
% Copyright 2021 Hendrik Bierlee
%
% Permission is hereby granted, free of charge, to any person obtaining a copy
% of this software and associated documentation files (the "Software"), to deal
% in the Software without restriction, including without limitation the rights
% to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
% copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions:
%
% The above copyright notice and this permission notice shall be included in all
% copies or substantial portions of the Software.
%
% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
% SOFTWARE.
%------------------------------------------------------------------------------

include "regular.mzn";
include "value_precede.mzn";
include "lex_lesseq.mzn";

int: n;  % board dimensions
enum Square = {EMPTY,BLACK,WHITE};

array[1..n,1..n] of var Square: x :: add_to_output;

var int: objective = count(x_i_j in array1d(x))(x_i_j == BLACK);

array[Square,Square] of int: d = [|
  EMPTY,BLACK,WHITE|
  BLACK,BLACK,    0|
  WHITE,    0,WHITE|];

% A DFA enforcing no white queens after black queens, and v.v.
predicate at_peace(array[int] of var int: x) = 
  regular(
    x,
    3, % Q = 3 states (excluding fail state 0)
    3, % S = 3 inputs
    d, % d = (input,states) -> status union {0}
    EMPTY, % starting state
    1..3, % accepting states: all except 0
  );

% Every row and column
constraint forall(i in 1..n)(
  at_peace(x[i,..]) /\ at_peace(x[..,i])
);

% All down-right diagonals (except corners)
constraint forall(k in 3..2*n-1)(
  at_peace([ x[i,j] | i,j in 1..n where i+j == k ])
);

% All up-right diagonals (except corners)
constraint forall(k in -n+2..n-2)(
  at_peace([ x[i,j] | i,j in 1..n where i-j == k ])
);

% Equal number of black and white queens
constraint objective == count(x_i_j in array1d(x))(x_i_j == WHITE);

% Predicates for symmetry breaking on a square
predicate var_sqr_sym(array[int,int] of var int: x) =
  let { int: n = card(index_set_1of2(x));
        int: n2 = card(index_set_2of2(x));
        constraint assert(n = n2,"square symmetry applied to non-square array");
        int: l = n * n;
        array[1..l] of var int:
          y = [ x[i,j] | i in index_set_1of2(x),
                         j in index_set_2of2(x) ];
        array[1..8,1..l] of 1..l:
          p = array2d(1..8,1..l,
            [ if k == 1 then i*n + j - n 
              elseif k == 2 then (n - j)*n + i           % r270
              elseif k == 3 then (n - i)*n + (n - j)+1   % r180
              elseif k == 4 then (j*n - n) + (n - i + 1) % r90
              elseif k == 5 then (n - i)*n + j           % x flip
              elseif k == 6 then (i*n - n) + (n - j + 1) % y flip
              elseif k == 7 then (n - j)*n + (n - i + 1) % d2 flip
              else               (j*n - n) + i           % d1 flip
              endif
            | k in 1..8, i,j in 1..n]) }
  in var_perm_sym(y,p);

predicate var_perm_sym(array[int] of var int: x,
                       array[int,int] of int: p) =
  let { int: l = min(index_set_1of2(p)),
        int: u = max(index_set_1of2(p)),
	array[1..length(x)] of var int:
          y = [ x[i] | i in index_set(x) ] }
  in
  forall (i, j in l..u where i != j) (
    var_perm_sym_pairwise(y,
      [ p[i,k] | k in index_set_2of2(p) ],
      [ p[j,k] | k in index_set_2of2(p) ])
  );

predicate var_perm_sym_pairwise(
    array[int] of var int: x,
    array[int] of int: p1,
    array[int] of int: p2) =
  let { int: n = length(x),
        array[1..n] of 1..n:
          invp1 = [ j | i, j in 1..n
                      where p1[j] = i ] }
  in
  lex_lesseq(x, [ x[p2[invp1[i]]] | i in 1..n ]);


% Symmetry: every solution can be rotated and/or reflected
constraint symmetry_breaking_constraint(var_sqr_sym(x));

% Symmetry: all white queens can be exchanged for all black queens
constraint symmetry_breaking_constraint(value_precede(BLACK,WHITE,array1d(x)));


% All the known optimal values from https://oeis.org/A250000
array[int] of int: OPT = [0, 0, 1, 2, 4, 5, 7, 9, 12, 14, 17, 21, 24, 28, 32];
% constraint objective >= OPT[n];

solve :: int_search(array1d(x), input_order, indomain_min, complete) maximize objective;

output [
          if fix(x[i,j]) == BLACK then "B" elseif fix(x[i,j]) == WHITE then "W" else "." endif
          % if fix(x[i,j]) == 2 then "B" elseif fix(x[i,j]) == 3 then "W" else "." endif
          ++ if j == n then "\n" else "" endif
    | i,j in 1..n] ++ ["n = \(n);\nobjective = \(objective);\noptimal = "]
      ++ if n <= length(OPT) then [ show(OPT[n]) ] else [ "?" ] endif ++ [";"];

