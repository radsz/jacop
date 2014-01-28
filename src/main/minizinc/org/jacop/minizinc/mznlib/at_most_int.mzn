%-----------------------------------------------------------------------------%
% Requires at most 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%
include "among.mzn";

predicate at_most_int(int: n, array[int] of var int: x, int: v) =
	  let {
	      var 0..n: var_n,
	      set of int: set_v={v}
	  }
	  in 
	     among(var_n, x, set_v);

%    sum(i in index_set(x)) ( bool2int(x[i] == v) ) <= n;

