include "among_var.mzn";

/** @group globals.counting
  Constrains \a c to be the number of occurrences of \a y in \a x. 
*/
predicate count_eq(array[int] of var int: x, var int: y, var int: c) =
%    c = sum(i in index_set(x)) ( bool2int(x[i] == y) );
     among_var(c, x, [y]);
     
predicate count_eq(array[int] of var int: x, int: y, var int: c) =
    jacop_count(x, y, c);
%     let {
%         set of int: set_y = {y}
%	 }
%     in 
%         among(c, x, set_y);

predicate jacop_count(array[int] of var int: x, int: y, var int: c);

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
