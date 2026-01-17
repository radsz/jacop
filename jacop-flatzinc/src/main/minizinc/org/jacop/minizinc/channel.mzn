%-----------------------------------------------------------------------------%
% Channeling constraint x = i <-> b[i].
%-----------------------------------------------------------------------------%
predicate jacop_channel(var int: x, array[int] of var bool: b, set of int: values);

predicate channel(var int: x, array[int] of var bool: b) =
   jacop_channel(x, b, dom(x));

predicate channel(var int: x, array[int] of var bool: b, set of int: values) =
   jacop_channel(x, b, values);
