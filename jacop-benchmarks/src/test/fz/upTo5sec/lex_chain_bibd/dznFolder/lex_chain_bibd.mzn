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
% BIBD (CSPLib 28): v x b 0/1 incidence matrix, rows sum to r, columns to k, two rows share
% lambda columns. Rows and columns are interchangeable: double lex on both.
int: v; int: b; int: r; int: k; int: lambda;
array[1..v, 1..b] of var bool: m;
constraint forall (i in 1..v) (sum (j in 1..b) (bool2int(m[i, j])) = r);
constraint forall (j in 1..b) (sum (i in 1..v) (bool2int(m[i, j])) = k);
constraint forall (i1, i2 in 1..v where i1 < i2)
  (sum (j in 1..b) (bool2int(m[i1, j] /\ m[i2, j])) = lambda);
constraint cols_lesseq_bool(m);
constraint cols_lesseq_bool(transp(m));
solve :: bool_search([m[i, j] | i in 1..v, j in 1..b], input_order, indomain_max) satisfy;
output ["m = \(m);\n"];
