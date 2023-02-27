include "fzn_round.mzn";

predicate round(var float: p, var int: x) =
   fzn_round(p, x);

function var int: round(var float: p) :: promise_total =
   let {
       var int: x ::is_defined_var;
       constraint fzn_round(p, x) ::defines_var(x); }
   in x;
