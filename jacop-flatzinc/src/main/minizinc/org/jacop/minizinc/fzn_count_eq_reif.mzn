predicate fzn_count_eq_reif(array[int] of var int: x, var int: y, var int: c, var bool: b) =
    if is_fixed(y) then
       jacop_count_reif(x, fix(y), c, b)
    else
       % With a variable value, the count is decomposed into one literal x[i] = y per variable
       % instead of the reified CountVar (jacop_count_var_reif). MiniZinc shares a literal x = y
       % between the counts that compare the same two variables (the neighbour colours of a
       % grid in amaze), and lazy clause generation learns on these literals: the fixed search of
       % amaze 2012-06-29 proves the optimum in 10 s instead of 183 s.
       b <-> (c = sum(i in index_set(x)) (bool2int(x[i] == y)))
    endif;

predicate jacop_count_reif(array[int] of var int: x, int: y, var int: c, var bool: b);
predicate jacop_count_var_reif(array[int] of var int: x, var int: y, var int: c, var bool: b);
