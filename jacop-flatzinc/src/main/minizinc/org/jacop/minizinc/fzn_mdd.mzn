predicate jacop_mdd(array[int] of var int: x, array[int] of int: level,
                    array[int] of int: from, array[int] of set of int: label,
                    array[int] of int: to);

% The parameter arrays are passed as they are: array1d makes a new array at each call, and
% MiniZinc keeps only a few of them for reuse, so WordDesign2-words-mdd-025 (XCSP 2023, 300 calls
% on one diagram of 1.8 million edges) got 31 copies of it in its FlatZinc (1.1 GB, 7 GB to
% flatten). FlatZinc renumbers an array that does not start at 1.
predicate fzn_mdd(array[int] of var int: x, int: N, array[int] of int: level,
                 int: E, array[int] of int: from, array[int] of set of int: label,
                 array[int] of int: to) =
     jacop_mdd(array1d(x), level, from, label, to);
