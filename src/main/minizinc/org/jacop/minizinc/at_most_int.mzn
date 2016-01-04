%-----------------------------------------------------------------------------%
% Requires at most 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%
% include "among.mzn";
include "count.mzn";

predicate at_most_int(int: n, array[int] of var int: x, int: v) =
	  % let {
	  %     var 0..n: var_n,
	  %     set of int: set_v={v}
	  % }
	  % in 
	  %    among(var_n, x, set_v);
	  let {
	      var 0..n: var_n,
	  }
	  in 
	     count(x, v, var_n);

%    sum(i in index_set(x)) ( bool2int(x[i] == v) ) <= n;

predicate at_most_int_reif(int: n, array[int] of var int: x, int: v, var bool: b) =
	  let {
	      int: max_n = max(index_set(x)),
	      var 0..max_n: var_n
	  }
	  in 
	     count(x, v, var_n)
	     /\
	     (n >= var_n) <-> b;
