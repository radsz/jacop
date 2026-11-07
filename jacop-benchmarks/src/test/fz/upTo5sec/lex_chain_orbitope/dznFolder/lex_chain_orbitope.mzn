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
% Graph colouring with a vertex x colour 0/1 matrix and interchangeable colours: the colour
% columns form a partitioning orbitope (columns non-increasing, one colour per vertex).
int: nv; int: k; int: ne;
array[1..ne, 1..2] of int: e;
array[1..nv, 1..k] of var 0..1: a;
constraint forall (i in 1..ne, c in 1..k) (a[e[i, 1], c] + a[e[i, 2], c] <= 1);
constraint cols_orbitope(a);
solve :: int_search([a[i, c] | i in 1..nv, c in 1..k], input_order, indomain_max) satisfy;
output ["a = \(a);\n"];
