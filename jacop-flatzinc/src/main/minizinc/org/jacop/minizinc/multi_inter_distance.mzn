%-----------------------------------------------------------------------------%
% Defines JaCoP predicate multi_inter_distance: for every v at most m of the
% variables x take a value in v..v+p-1.
% x - start times of tasks of length p on m identical machines.
% m - the number of machines.
% p - the length of the tasks.
%-----------------------------------------------------------------------------%
predicate multi_inter_distance(array[int] of var int: x, int: m, int: p) =
	  jacop_multi_inter_distance(x, m, p);

predicate jacop_multi_inter_distance(array[int] of var int: x, int: m, int: p);
