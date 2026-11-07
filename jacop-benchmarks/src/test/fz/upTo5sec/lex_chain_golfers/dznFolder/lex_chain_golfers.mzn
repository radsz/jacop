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
% Social golfers (CSPLib 10), integer model: x[p, wk] is the group of player p in week wk.
% Weeks (columns) strictly increasing, players (rows) non-decreasing.
int: weeks; int: groups; int: size;
int: players = groups * size;
array[1..players, 1..weeks] of var 1..groups: x;
constraint forall (wk in 1..weeks, g in 1..groups) (sum (p in 1..players) (bool2int(x[p, wk] = g)) = size);
constraint forall (p1, p2 in 1..players where p1 < p2)
  (sum (wk in 1..weeks) (bool2int(x[p1, wk] = x[p2, wk])) <= 1);
constraint cols_less(x);
constraint cols_lesseq(transp(x));
solve :: int_search([x[p, wk] | wk in 1..weeks, p in 1..players], input_order, indomain_min) satisfy;
output ["x = \(x);\n"];
