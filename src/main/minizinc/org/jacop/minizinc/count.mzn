include "count_eq.mzn";

/** @group globals.counting
  Constrains \a c to be the number of occurrences of \a y in \a x. 
*/
predicate count(array[int] of var int: x, var int: y, var int: c) =
    count_eq(x, y, c);

predicate count(array[int] of var int: x, int: y, var int: c) =
    jacop_count(x, y, c);

%-----------------------------------------------------------------------------%
% Reified version of count.
%-----------------------------------------------------------------------------%
predicate count_reif(array[int] of var int: x, int: y, var int: c, var bool: b) =
	  let { 
          int: l = min(index_set(x)),
          int: u = max(index_set(x)),
	  int: mm = u - l + 1, 
	  var 0..mm: ni
	  }
	  in
	  jacop_count(x, y, ni)
	  /\
	  (b <-> ni = c)
;


%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

