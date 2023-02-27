include "fzn_ceil.mzn";

predicate ceil(var float: p, var int: x) =
   fzn_ceil(p, x);

function var int: ceil(var float: p) :: promise_total =
   let {
       var int: x ::is_defined_var;
       constraint fzn_ceil(p, x) ::defines_var(x); }
   in x;
