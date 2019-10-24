predicate jacop_count(array[int] of var int: x, int: y, var int: c);

predicate fzn_count_eq(array[int] of var int: x, var int: y, var int: c) =
    if is_fixed(y) then
        jacop_count(x, fix(y), c)
    else
        c = sum(i in index_set(x)) ( bool2int(x[i] == y) )
    endif;
%     among_var(c, x, [y]);  %% this is less efficinet, even generating less search nodes... :(
     
