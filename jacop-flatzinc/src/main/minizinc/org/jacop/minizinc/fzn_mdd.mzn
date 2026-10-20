predicate jacop_mdd(array[int] of var int: x, array[int] of int: level,
                    array[int] of int: from, array[int] of set of int: label,
                    array[int] of int: to);

predicate fzn_mdd(array[int] of var int: x, int: N, array[int] of int: level,
                 int: E, array[int] of int: from, array[int] of set of int: label,
                 array[int] of int: to) =
     jacop_mdd(array1d(x), array1d(level), array1d(from), array1d(label), array1d(to));
