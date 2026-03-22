predicate fzn_count_eq_reif(array[int] of var int: x, var int: y, var int: c, var bool: b) =
    if is_fixed(y) then
       jacop_count_reif(x, fix(y), c, b)
    else
       jacop_count_var_reif(x, y, c, b)
       % b <-> count_eq(x,y)=c
    endif;

predicate jacop_count_reif(array[int] of var int: x, int: y, var int: c, var bool: b);
predicate jacop_count_var_reif(array[int] of var int: x, var int: y, var int: c, var bool: b);
