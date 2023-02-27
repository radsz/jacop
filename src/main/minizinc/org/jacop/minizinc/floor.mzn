include "fzn_floor.mzn";

predicate floor(var float: p, var int: x) =
   fzn_floor(p, x);

function var int: floor(var float: p) :: promise_total =
   let {
       var int: x ::is_defined_var;
       constraint fzn_floor(p, x) ::defines_var(x); }
   in x;
