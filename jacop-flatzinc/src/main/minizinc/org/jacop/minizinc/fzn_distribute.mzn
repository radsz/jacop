include "fzn_count_eq.mzn";

predicate fzn_distribute(array[int] of var int: card,
                     array[int] of var int: value,
                     array[int] of var int: base) =
        forall (i in index_set(card)) (
	    fzn_count_eq(base, value[i], card[i])
        )
    ;
