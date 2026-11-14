%-----------------------------------------------------------------------------%
% Channeling constraint x = i <-> b[i].
%-----------------------------------------------------------------------------%
predicate jacop_channel(var int: x, array[int] of var bool: b, set of int: values);

% b[i] is true for x = i, so x takes a value of index_set(b), whatever dom(x) is.
predicate channel(var int: x, array[int] of var bool: b) =
   x in index_set(b) /\ jacop_channel(x, b, index_set(b));

predicate channel(var int: x, array[int] of var bool: b, set of int: values) =
   jacop_channel(x, b, values);
