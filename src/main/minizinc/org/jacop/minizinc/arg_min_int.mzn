predicate minimum_arg_int(array[int] of var int: x, var int: i) =
  jacop_minimum_arg_int(x,i);

predicate jacop_minimum_arg_int(array[int] of var int: x, var int: i);

% predicate jacop_minimum_arg_int_reif(array[int] of var int: x, var int: i, var bool: b) =
%     abort("Reified minimum_arg/2 is not supported.");
