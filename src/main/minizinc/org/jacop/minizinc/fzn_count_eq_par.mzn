predicate jacop_count(array[int] of var int: x, int: y, var int: c);

predicate fzn_count_eq_par(array[int] of var int: x, int: y, int: c) =
   jacop_count(x, y, c)

%-----------------------------------------------------------------------------%
