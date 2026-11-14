predicate jacop_int_set_channel(array[int] of var int: x, 
                                 array[int] of var set of int: y, int: xoff, int: yoff);

predicate fzn_int_set_channel(array[int] of var int: x,
                              array[int] of var set of int: y) =
    if (length(x)=0 \/ length(y)=0 \/ min(index_set(x)) < 0 \/ min(index_set(y)) < 0) then
        forall(i in index_set(x)) (x[i] in index_set(y)) /\
        forall(j in index_set(y)) (y[j] subset index_set(x)) /\
        forall(i in index_set(x), j in index_set(y))
            (x[i]=j <-> i in y[j])
    else
       jacop_int_set_channel(x, y, min(index_set(x)), min(index_set(y)))
    endif;
