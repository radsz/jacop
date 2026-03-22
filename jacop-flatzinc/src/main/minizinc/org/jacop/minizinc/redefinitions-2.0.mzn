% This file contains redefinitions of standard builtins that can be overridden
% by solvers.

predicate bool_clause_reif(array[int] of var bool: as,
                           array[int] of var bool: bs,
                           var bool: b);

predicate array_int_maximum(var int: m, array[int] of var int: x) =
       jacop_maximum(m, x);

predicate array_float_maximum(var float: m, array[int] of var float: x) =
    jacop_float_maximum(x, m);

predicate array_int_minimum(var int: m, array[int] of var int: x) =
     jacop_minimum(m, x);

predicate array_float_minimum(var float: m, array[int] of var float: x) =
    jacop_float_minimum(x, m);

predicate jacop_float_minimum(array[int] of var float: x, var float: m);

predicate jacop_minimum(var int: m, array[int] of var int: x);

predicate jacop_maximum(var int: m, array[int] of var int: x);

predicate jacop_float_maximum(array[int] of var float: x, var float: m);

