predicate jacop_diff2_strict(array[int] of var int: x, array[int] of var int: y,
	        	     array[int] of var int: lx, array[int] of var int: ly);

predicate fzn_diffn(array[int] of var int: x,
                array[int] of var int: y,
                array[int] of var int: dx,
                array[int] of var int: dy) =
    jacop_diff2_strict(x, y, dx, dy)
    ;

