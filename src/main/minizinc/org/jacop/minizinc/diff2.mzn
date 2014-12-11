%-----------------------------------------------------------------------------%
% Requires that rectangles specified by r do not overlap
% rectangles can be specifid by a vector [x_i, y_i, lx_i, ly_i] or
% as four vectors x, y, lx and ly
%-----------------------------------------------------------------------------%
predicate diff2(array[int,int] of var int: r) =

    let { int: lr2 = min(index_set_2of2(r)),
          int: ur2 = max(index_set_2of2(r)),
          int : s2 = (ur2 - lr2 + 1),
	}
        in
	  assert( s2 = 4,
	    "diff2: size of a rectangle must be 4",
             jacop_diff2(r)
	  );

predicate diff2(array[int] of var int: x, array[int] of var int: y,
	        array[int] of var int: lx, array[int] of var int: ly) =
           jacop_list_diff2(x, y, lx, ly);


predicate jacop_diff2(array[int,int] of var int: r);

predicate jacop_list_diff2(array[int] of var int: x, array[int] of var int: y,
	                   array[int] of var int: lx, array[int] of var int: ly);