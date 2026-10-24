include "diff2.mzn";

predicate fzn_diffn_nonstrict(array[int] of var int: x,
                          array[int] of var int: y,
                          array[int] of var int: dx,
                          array[int] of var int: dy) =
        diff2(x, y, dx, dy)
    ;
