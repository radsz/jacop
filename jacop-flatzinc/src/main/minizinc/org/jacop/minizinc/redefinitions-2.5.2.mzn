% This file contains redefinitions of standard builtins for version 2.5.2
% that can be overridden by solvers.

include "table.mzn";

% A fixed array becomes a table over (idx1, idx2, y), which is domain consistent on both indices
% together; the linearised index idx1 * dim + idx2 is kept for arrays of variables and for very
% large arrays.
predicate array_var_int_element2d_nonshifted(
  var int: idx1,
  var int: idx2,
  array [int, int] of var int: xs,
  var int: y,
) =
  if is_fixed(xs) /\ length(xs) <= 10000 then
    table([idx1, idx2, y],
          array2d(1..length(xs), 1..3,
                  [[i, j, fix(xs[i, j])][k] | i in index_set_1of2(xs), j in index_set_2of2(xs),
                                              k in 1..3]))
  else
    let {
      int: dim = card(index_set_2of2(xs));
      int: min_flat = min(index_set_1of2(xs)) * dim + min(index_set_2of2(xs)) - 1;
    } in array_var_int_element_nonshifted((idx1 * dim + idx2 - min_flat) :: domain, array1d(xs), y)
  endif;

predicate array_var_bool_element2d_nonshifted(
  var int: idx1,
  var int: idx2,
  array [int, int] of var bool: xs,
  var bool: y,
) =
  if is_fixed(xs) /\ length(xs) <= 10000 then
    table([idx1, idx2, bool2int(y)],
          array2d(1..length(xs), 1..3,
                  [[i, j, bool2int(fix(xs[i, j]))][k] | i in index_set_1of2(xs),
                                                        j in index_set_2of2(xs), k in 1..3]))
  else
    let {
      int: dim = card(index_set_2of2(xs));
      int: min_flat = min(index_set_1of2(xs)) * dim + min(index_set_2of2(xs)) - 1;
    } in array_var_bool_element_nonshifted((idx1 * dim + idx2 - min_flat) :: domain, array1d(xs), y)
  endif;

predicate array_var_float_element2d_nonshifted(
  var int: idx1,
  var int: idx2,
  array [int, int] of var float: xs,
  var float: y,
) =
  let {
    int: dim = card(index_set_2of2(xs));
    int: min_flat = min(index_set_1of2(xs)) * dim + min(index_set_2of2(xs)) - 1;
  } in array_var_float_element_nonshifted((idx1 * dim + idx2 - min_flat) :: domain, array1d(xs), y);

predicate array_var_set_element2d_nonshifted(
  var int: idx1,
  var int: idx2,
  array [int, int] of var set of int: xs,
  var set of int: y,
) =
  let {
    int: dim = card(index_set_2of2(xs));
    int: min_flat = min(index_set_1of2(xs)) * dim + min(index_set_2of2(xs)) - 1;
  } in array_var_set_element_nonshifted((idx1 * dim + idx2 - min_flat) :: domain, array1d(xs), y);
