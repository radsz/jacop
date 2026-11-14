predicate jacop_regular_nfa(array[int] of var int: xs, int: Q, set of int: S,
                            array[int] of set of int: d, int: q0, set of int: F,
                            int: min_state, int: min_symbol, int: symbols);

% Nondeterministic automaton: d[q, s] is the set of states reached from q with symbol s.
predicate fzn_regular_nfa(array[int] of var int: xs, int: Q, int: S,
                          array[int,int] of set of int: d, int: q0, set of int: F) =
    if length(xs) = 0 then
        q0 in F
    else
        jacop_regular_nfa(xs, Q, 1..S, array1d(d), q0, F, min(index_set_1of2(d)),
                          min(index_set_2of2(d)), card(index_set_2of2(d)))
    endif;
