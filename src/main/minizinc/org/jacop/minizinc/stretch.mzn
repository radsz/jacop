%-----------------------------------------------------------------------------%
% Defines JaCoP decomposed predicate stretch
% values - a list of values which can be taken by variables.
% min - the minimal sequence length for each value.
% max - the maximal sequence length for each value.
% x - variables which assignment is constrained by Stretch constraint.
% 
%-----------------------------------------------------------------------------%
predicate stretch(array[int] of int: values, array[int] of int: min_v, array[int] of int: max_v, 
	          array[int] of var int: x) =
		  jacop_stretch(values, min_v, max_v, x);

predicate jacop_stretch(array[int] of int: values, array[int] of int: min_v, array[int] of int: max_v, 
	          array[int] of var int: x);