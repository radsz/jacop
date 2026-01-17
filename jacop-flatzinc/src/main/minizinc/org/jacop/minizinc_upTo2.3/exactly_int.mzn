%-----------------------------------------------------------------------------%
% Requires exactly 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%

include "count.mzn";

predicate exactly_int(int: n, array[int] of var int: x, int: v) =
	  % let {
	  %     set of int: set_v={v}
	  % }
	  % in 
	  %    among(n, x, set_v);
	  count(x, v, n);


%    n == sum(i in index_set(x)) ( bool2int(x[i] == v) );
