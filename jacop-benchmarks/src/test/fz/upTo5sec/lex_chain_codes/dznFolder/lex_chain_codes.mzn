include "globals.mzn";
% Lexicographic order of the columns of a matrix, as one lex_chain global (chain = 1)
% or as lex constraints between neighbouring columns (chain = 0).

int: chain = 1;

predicate cols_lesseq(array[int, int] of var int: a) =
  if chain = 1 then lex_chain_lesseq(a)
  else forall (j in index_set_2of2(a) where j + 1 in index_set_2of2(a))
         (lex_lesseq(col(a, j), col(a, j + 1))) endif;

predicate cols_less(array[int, int] of var int: a) =
  if chain = 1 then lex_chain_less(a)
  else forall (j in index_set_2of2(a) where j + 1 in index_set_2of2(a))
         (lex_less(col(a, j), col(a, j + 1))) endif;

predicate cols_lesseq_bool(array[int, int] of var bool: a) =
  if chain = 1 then lex_chain_lesseq(a)
  else forall (j in index_set_2of2(a) where j + 1 in index_set_2of2(a))
         (lex_lesseq(col(a, j), col(a, j + 1))) endif;

predicate cols_less_bool(array[int, int] of var bool: a) =
  if chain = 1 then lex_chain_less(a)
  else forall (j in index_set_2of2(a) where j + 1 in index_set_2of2(a))
         (lex_less(col(a, j), col(a, j + 1))) endif;

% partitioning orbitope: every row has exactly one 1, columns non-increasing
predicate cols_orbitope(array[int, int] of var 0..1: a) =
  if chain = 1 then lex_chain_greatereq_orbitope(a, 1)
  else forall (i in index_set_1of2(a)) (sum(row(a, i)) = 1) /\
       forall (j in index_set_2of2(a) where j + 1 in index_set_2of2(a))
         (lex_greatereq(col(a, j), col(a, j + 1))) endif;

function array[int, int] of var int: transp(array[int, int] of var int: a) =
  array2d(index_set_2of2(a), index_set_1of2(a), [a[i, j] | j in index_set_2of2(a), i in index_set_1of2(a)]);
function array[int, int] of var bool: transp(array[int, int] of var bool: a) =
  array2d(index_set_2of2(a), index_set_1of2(a), [a[i, j] | j in index_set_2of2(a), i in index_set_1of2(a)]);
% Constant weight binary code: nc codewords of length n and weight w with pairwise Hamming
% distance at least d. Codewords (columns) strictly increasing, coordinates (rows) non-decreasing.
int: n; int: w; int: d; int: nc;
array[1..n, 1..nc] of var 0..1: c;
constraint forall (j in 1..nc) (sum (i in 1..n) (c[i, j]) = w);
% distance >= d between weight-w words means at most w - d/2 common ones
constraint forall (j1, j2 in 1..nc where j1 < j2) (sum (i in 1..n) (c[i, j1] * c[i, j2]) <= w - d div 2);
constraint cols_less(c);
constraint cols_lesseq(transp(c));
solve :: int_search([c[i, j] | j in 1..nc, i in 1..n], input_order, indomain_max) satisfy;
output ["c = \(c);\n"];
