%------------------------------------------------------------------------%
%   Magic sequence (naive model)
%------------------------------------------------------------------------%
%
% This model uses the basic naive model with reification, without any
% implied constraints. The model tests the solvers ability to handle
% many simple constraints at the same time, for a problem of size 50
% roughly 5000 propagators are needed.
%
%------------------------------------------------------------------------%


% Length of sequence
int: n;

% Sequence
array [1..n] of var 0..n-1: s;

predicate number_of_v(array [int] of var int: xs, var int: x, int: v) =
	x == sum (i in index_set(xs)) (bool2int(xs[i] == v));

constraint
	forall (i in index_set(s)) (
		number_of_v(s, s[i], i-1)
	);

solve :: int_search(s, input_order, indomain_min, complete)
	satisfy;

output
    ["n = ", show(n), ";\n"] ++
    ["s = ", show(s), ";\n"];

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
