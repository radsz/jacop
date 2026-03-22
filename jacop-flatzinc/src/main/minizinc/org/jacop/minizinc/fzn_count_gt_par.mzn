predicate jacop_atmost(array[int] of var int: x, int: y, int: c);

predicate fzn_count_gt_par(array[int] of var int: x, int: y, int: c) =
   jacop_atmost(x, y, c - 1);

%-----------------------------------------------------------------------------%
