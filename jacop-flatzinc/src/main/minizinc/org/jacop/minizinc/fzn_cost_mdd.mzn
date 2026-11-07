predicate jacop_cost_mdd(array[int] of var int: x, array[int] of int: level,
                         array[int] of int: from, array[int] of set of int: label,
                         array[int] of int: cost, array[int] of int: to, var int: total_cost);

predicate fzn_cost_mdd(array[int] of var int: xs, int: N, array[int] of int: level,
                       int: E, array[int] of int: from, array[int] of set of int: label,
                       array[int] of int: cost, array[int] of int: to, var int: total_cost) =
     jacop_cost_mdd(array1d(xs), array1d(level), array1d(from), array1d(label), array1d(cost),
                    array1d(to), total_cost);
