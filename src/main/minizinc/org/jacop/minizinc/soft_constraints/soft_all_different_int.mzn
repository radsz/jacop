%-----------------------------------------------------------------------------%
% Constrains the array of objects 'x' to be all different with a tolerance 
% defined by d.
%-----------------------------------------------------------------------------%
predicate soft_all_different_int(array[int] of var int: x, var int: d, bool: useDec) =
	  jacop_softalldiff(x, d, useDec);

%    = forall(i,j in index_set(x) where i < j) ( x[i] != x[j] );

predicate jacop_softalldiff(array[int] of var int: x, var int: d, bool: useDec);
