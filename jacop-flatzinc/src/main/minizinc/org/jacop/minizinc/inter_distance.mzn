%-----------------------------------------------------------------------------%
% Defines JaCoP predicate inter_distance: |x[i] - x[j]| >= p for all i != j.
% x - start times of tasks of length p on one machine.
% p - the minimal distance between two start times.
%-----------------------------------------------------------------------------%
predicate inter_distance(array[int] of var int: x, int: p) =
	  jacop_inter_distance(x, p);

predicate jacop_inter_distance(array[int] of var int: x, int: p);
