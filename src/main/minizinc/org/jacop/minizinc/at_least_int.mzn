%-----------------------------------------------------------------------------%
% Requires at least 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%
include "among.mzn";

predicate at_least_int(int: n, array[int] of var int: x, int: v) =
	  let {
	      int: max_n = max(index_set(x)),
	      var n..max_n: var_n,
	      set of int: set_v={v}
	  }
	  in 
	     among(var_n, x, set_v);

%    sum(i in index_set(x)) ( bool2int(x[i] == v) ) >= n;

