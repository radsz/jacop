% The rows of x are pairwise different tuples (XCSP3 allDifferent over lists), posted as JaCoP's
% AllDifferentLists. The XCSP3 translations of radsz/xcsp-competition call this predicate; their own
% definition is the pairwise decomposition, m(m-1)/2 disjunctions for m rows, which the solver
% library replaces (it comes before the -I include directories).
predicate jacop_all_different_lists(array[int] of var int: x, int: rows);

predicate fzn_xcsp_all_different_lists(array[int, int] of var int: x) =
     jacop_all_different_lists(array1d(x), card(index_set_1of2(x)));
