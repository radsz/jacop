% This file contains redefinitions of standard builtins that can be overridden
% by solvers.

predicate float_sinh(var float: x, var float: y) =
    y = (exp(x)-exp(-x))/2.0;

predicate float_cosh(var float: x, var float: y) =
    y = (exp(x)+exp(-x))/2.0;

predicate float_tanh(var float: x, var float: y) =
    let {
      var float: e2x = exp(2.0*x),
    } in
    y = (e2x - 1.0)/(e2x + 1.0);



predicate array_bool_and_imp(array [int] of var bool: as, var bool: r);
predicate array_bool_or_imp(array [int] of var bool: as, var bool: r);
predicate array_bool_xor_imp(array [int] of var bool: as, var bool: r);

predicate bool_and_imp(var bool: a, var bool: b, var bool: r);
predicate bool_clause_imp(array [int] of var bool: as,
                          array [int] of var bool: bs, var bool: r);
predicate bool_ge_imp(var bool: a, var bool: b, var bool: r);
predicate bool_gt_imp(var bool: a, var bool: b, var bool: r);
predicate bool_le_imp(var bool: a, var bool: b, var bool: r);
predicate bool_lt_imp(var bool: a, var bool: b, var bool: r);
predicate bool_eq_imp(var bool: a, var bool: b, var bool: r);
predicate bool_ne_imp(var bool: a, var bool: b, var bool: r);
predicate bool_or_imp(var bool: a, var bool: b, var bool: r);
predicate bool_xor_imp(var bool: a, var bool: b, var bool: r);

predicate bool_lin_eq_imp(array [int] of int: as, array [int] of var bool: bs,
                          var int: c, var bool: r) =
    let {
      int: ni_min = min(index_set(as)),
      int: ni_max = max(index_set(as))+1,
      array[ni_min..ni_max] of var int: nbs = [c] ++ [bool2int(bs[i]) | i in index_set(bs)],
      array[ni_min..ni_max] of int: nas = [-1] ++ [as[i] | i in index_set(as)],
   } in
   int_lin_eq_imp(nas, nbs, 0, r);
predicate bool_lin_ge_imp(array [int] of int: as, array [int] of var bool: bs,
                          var int: c, var bool: r) =
    let {
      int: ni_min = min(index_set(as)),
      int: ni_max = max(index_set(as))+1,
      array[ni_min..ni_max] of var int: nbs = [c] ++ [bool2int(bs[i]) | i in index_set(bs)],
      array[ni_min..ni_max] of int: nas = [-1] ++ [as[i] | i in index_set(as)],
   } in
   int_lin_ge_imp(nas, nbs, 0, r);
predicate bool_lin_gt_imp(array [int] of int: as, array [int] of var bool: bs,
                          var int: c, var bool: r) =
    let {
      int: ni_min = min(index_set(as)),
      int: ni_max = max(index_set(as))+1,
      array[ni_min..ni_max] of var int: nbs = [c] ++ [bool2int(bs[i]) | i in index_set(bs)],
      array[ni_min..ni_max] of int: nas = [-1] ++ [as[i] | i in index_set(as)],
   } in
   int_lin_gt_imp(nas, nbs, 0, r);
predicate bool_lin_le_imp(array [int] of int: as, array [int] of var bool: bs,
                          var int: c, var bool: r) =
    let {
      int: ni_min = min(index_set(as)),
      int: ni_max = max(index_set(as))+1,
      array[ni_min..ni_max] of var int: nbs = [c] ++ [bool2int(bs[i]) | i in index_set(bs)],
      array[ni_min..ni_max] of int: nas = [-1] ++ [as[i] | i in index_set(as)],
   } in
   int_lin_le_imp(nas, nbs, 0, r);
predicate bool_lin_lt_imp(array [int] of int: as, array [int] of var bool: bs,
                          var int: c, var bool: r) =
    let {
      int: ni_min = min(index_set(as)),
      int: ni_max = max(index_set(as))+1,
      array[ni_min..ni_max] of var int: nbs = [c] ++ [bool2int(bs[i]) | i in index_set(bs)],
      array[ni_min..ni_max] of int: nas = [-1] ++ [as[i] | i in index_set(as)],
   } in
   int_lin_lt_imp(nas, nbs, 0, r);
predicate bool_lin_ne_imp(array [int] of int: as, array [int] of var bool: bs,
                          var int: c, var bool: r) =
    let {
      int: ni_min = min(index_set(as)),
      int: ni_max = max(index_set(as))+1,
      array[ni_min..ni_max] of var int: nbs = [c] ++ [bool2int(bs[i]) | i in index_set(bs)],
      array[ni_min..ni_max] of int: nas = [-1] ++ [as[i] | i in index_set(as)],
   } in
   int_lin_ne_imp(nas, nbs, 0, r);

predicate int_eq_imp(var int: a, var int: b, var bool: r);
predicate int_ge_imp(var int: a, var int: b, var bool: r);
predicate int_gt_imp(var int: a, var int: b, var bool: r);
predicate int_le_imp(var int: a, var int: b, var bool: r);
predicate int_lt_imp(var int: a, var int: b, var bool: r);
predicate int_ne_imp(var int: a, var int: b, var bool: r);

predicate int_lin_eq_imp(array [int] of int: as, array [int] of var int: bs,
                         int: c, var bool: r);
predicate int_lin_ge_imp(array [int] of int: as, array [int] of var int: bs,
                         int: c, var bool: r);
predicate int_lin_gt_imp(array [int] of int: as, array [int] of var int: bs,
                         int: c, var bool: r);
predicate int_lin_le_imp(array [int] of int: as, array [int] of var int: bs,
                         int: c, var bool: r);
predicate int_lin_lt_imp(array [int] of int: as, array [int] of var int: bs,
                         int: c, var bool: r);
predicate int_lin_ne_imp(array [int] of int: as, array [int] of var int: bs,
                         int: c, var bool: r);

predicate set_in_imp(var int: x, set of int: S, var bool: r);
