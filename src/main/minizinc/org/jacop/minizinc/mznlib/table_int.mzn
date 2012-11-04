%-----------------------------------------------------------------------------%
% A table constraint: table(x, t) represents the constraint x in t where we
% consider each row in t to be a tuple and t as a set of tuples.
%-----------------------------------------------------------------------------%

predicate table_int(array[int] of var int: x, array[int, int] of int: t) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
	jacop_table_int(x, t)
    );

predicate jacop_table_int(array[int] of var int: x, array[int, int] of int: t);

%        let { int: l = min(index_set(x)),
%              int: u = max(index_set(x)),
%              int: lt = min(index_set_1of2(t)),
%              int: ut = max(index_set_1of2(t)),
%              var lt..ut: i } 
%        in
%              forall(j in l..u) (
%                t[i,j] = x[j]
%              )
%    );
