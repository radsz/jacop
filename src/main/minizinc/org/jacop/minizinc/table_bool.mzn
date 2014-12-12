%-----------------------------------------------------------------------------%
% A table constraint: table(x, t) represents the constraint x in t where we
% consider each row in t to be a tuple and t as a set of tuples.
%-----------------------------------------------------------------------------%

predicate table_bool(array[int] of var bool: x, array[int, int] of bool: t) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
	 jacop_table_bool(x, t)
    );

predicate jacop_table_bool(array[int] of var bool: x, array[int, int] of bool: t);

predicate table_bool_reif(array[int] of var bool: x, array[int, int] of bool: t,
      var bool: b) = 
   abort("Reified table/2 for Booleans is not supported.");
