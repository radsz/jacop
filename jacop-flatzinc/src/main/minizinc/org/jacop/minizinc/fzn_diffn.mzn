predicate jacop_diff2_strict(array[int] of var int: x, array[int] of var int: y,
	        	     array[int] of var int: lx, array[int] of var int: ly);

predicate fzn_diffn(array[int] of var int: x,
                array[int] of var int: y,
                array[int] of var int: dx,
                array[int] of var int: dy) =
    if lb_array(dx) >= 0 /\ lb_array(dy) >= 0 then
      jacop_diff2_strict(x, y, dx, dy)
    else % a negative size: Diffn assumes sizes >= 0
      forall (i, j in index_set(x) where i < j)
        (x[i] + dx[i] <= x[j] \/ y[i] + dy[i] <= y[j] \/
         x[j] + dx[j] <= x[i] \/ y[j] + dy[j] <= y[i])
    endif;
