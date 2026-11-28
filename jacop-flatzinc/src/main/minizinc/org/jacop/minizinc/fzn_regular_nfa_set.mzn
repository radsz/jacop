include "fzn_regular_nfa.mzn";

predicate fzn_regular_nfa(array[int] of var int: xs, int: Q, set of int: S,
                          array[int,int] of set of int: d, int: q0, set of int: F) =
    if length(xs) = 0 then
        q0 in F
    else
        jacop_regular_nfa(xs, Q, S, array1d(d), q0, F, min(index_set_1of2(d)),
                          min(index_set_2of2(d)), card(index_set_2of2(d)))
    endif;
