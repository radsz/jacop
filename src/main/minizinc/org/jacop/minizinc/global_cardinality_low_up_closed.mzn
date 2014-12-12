%-----------------------------------------------------------------------------%
% Requires that the number of occurences of 'cover[i]' in 'x' is between
% 'lbound[i]' and 'ubound[i]'.
% The elements of 'x' must take their values from 'cover'.
%-----------------------------------------------------------------------------%

predicate global_cardinality_low_up_closed(array[int] of var int: x,
                                           array[int] of int: cover,
				           array[int] of int: lbound,
                                           array[int] of int: ubound) =
    assert(index_set(lbound) = index_set(ubound) /\ index_set(lbound) = index_set(cover),
        "global_cardinality_low_up_closed: lbound, ubound and cover must have identical index sets",
    jacop_global_cardinality_low_up_closed(x, cover, lbound, ubound)
    /\
    % Implied condition
    length(x) in sum(lbound)..sum(ubound)
    );


predicate jacop_global_cardinality_low_up_closed(array[int] of var int: x,
                                                 array[int] of int: cover,
				                 array[int] of int: lbound,
                                                 array[int] of int: ubound);

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
