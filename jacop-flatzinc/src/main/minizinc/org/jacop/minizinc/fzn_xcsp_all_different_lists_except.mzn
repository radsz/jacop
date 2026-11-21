% The rows of x are pairwise different tuples unless their tuple is a row of e (XCSP3 allDifferent
% over lists with except), posted as JaCoP's AllDifferentLists. Like fzn_xcsp_all_different_lists,
% it replaces the pairwise decomposition of the radsz/xcsp-competition include.
predicate jacop_all_different_lists_except(array[int] of var int: x, int: rows, array[int] of int: e);

predicate fzn_xcsp_all_different_lists_except(array[int, int] of var int: x, array[int, int] of int: e) =
     jacop_all_different_lists_except(array1d(x), card(index_set_1of2(x)), array1d(e));
