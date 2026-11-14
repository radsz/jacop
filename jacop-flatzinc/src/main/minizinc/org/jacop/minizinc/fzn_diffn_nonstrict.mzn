include "diff2.mzn";

predicate fzn_diffn_nonstrict(array[int] of var int: x,
                          array[int] of var int: y,
                          array[int] of var int: dx,
                          array[int] of var int: dy) =
    if lb_array(dx) >= 0 /\ lb_array(dy) >= 0 then
        diff2(x, y, dx, dy)
    else % a negative size: Diff2 assumes sizes >= 0
      forall (i, j in index_set(x) where i < j)
        (dx[i] = 0 \/ dx[j] = 0 \/ dy[i] = 0 \/ dy[j] = 0 \/
         x[i] + dx[i] <= x[j] \/ y[i] + dy[i] <= y[j] \/
         x[j] + dx[j] <= x[i] \/ y[j] + dy[j] <= y[i])
    endif;
