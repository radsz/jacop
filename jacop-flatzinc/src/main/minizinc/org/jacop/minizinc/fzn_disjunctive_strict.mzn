include "fzn_diffn.mzn";
include "fzn_cumulative.mzn";

predicate fzn_disjunctive_strict(array[int] of var int: s,
                             array[int] of var int: d) =
        forall (i in index_set(d)) (d[i] >= 0) /\
        if (lb_array(d) > 0) then
           fzn_cumulative(s, d, [1 | i in index_set(d)], 1)
        else
	   fzn_diffn(s, [0 | i in index_set(s)], d, [1 | i in index_set(d)])
        endif;

