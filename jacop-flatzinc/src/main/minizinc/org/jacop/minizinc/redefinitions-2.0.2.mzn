% This file contains redefinitions of standard builtins for version 2.0.2
% that can be overridden by solvers.

predicate symmetry_breaking_constraint(var bool: b) = b;

predicate redundant_constraint(var bool: b) = b;

% Element on an array whose first index is min_index, so JaCoP's element constraints take the
% index offset instead of an auxiliary variable for idx - (min_index - 1).
predicate jacop_array_var_int_element_nonshifted(var int: idx, array [int] of var int: xs,
                                                 var int: y, int: min_index);

predicate jacop_array_var_bool_element_nonshifted(var int: idx, array [int] of var bool: xs,
                                                  var bool: y, int: min_index);

predicate array_var_bool_element_nonshifted(var int: idx, array [int] of var bool: xs, var bool: y) =
  jacop_array_var_bool_element_nonshifted(idx, array1d(xs), y, min(index_set(xs)));

predicate array_var_int_element_nonshifted(var int: idx, array [int] of var int: xs, var int: y) =
  jacop_array_var_int_element_nonshifted(idx, array1d(xs), y, min(index_set(xs)));

predicate array_var_float_element_nonshifted(
  var int: idx,
  array [int] of var float: xs,
  var float: y,
) = array_var_float_element((idx - (min(index_set(xs)) - 1)) :: domain, array1d(xs), y);

predicate array_var_set_element_nonshifted(
  var int: idx,
  array [int] of var set of int: xs,
  var set of int: y,
) = array_var_set_element((idx - (min(index_set(xs)) - 1)) :: domain, array1d(xs), y);
