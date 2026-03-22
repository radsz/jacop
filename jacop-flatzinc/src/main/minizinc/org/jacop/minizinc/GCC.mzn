predicate jacop_gcc(array [int] of var int: x, array [int] of var int: c, int: index);

predicate GCC(array [int] of var int: x, array [int] of var int: c) =
   jacop_gcc(x, c, min(index_set(c)));
