predicate jacop_cost_regular(array[int] of var int: x, int: Q, int: S,
                             array[int] of int: d, int: q0, set of int: F,
                             array[int] of int: c, var int: C);

predicate fzn_cost_regular(array[int] of var int: x, int: Q, int: S,
                           array[int,int] of int: d, int: q0, set of int: F,
                           array[int,int] of int: c, var int: C) =
     jacop_cost_regular(array1d(x), Q, S, array1d(d), q0, F, array1d(c), C);
