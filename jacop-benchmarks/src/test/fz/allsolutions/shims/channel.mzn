predicate channel(var int: x, array[int] of var bool: b) =
  x in index_set(b) /\ forall(i in index_set(b))(b[i] <-> x = i);
predicate channel(var int: x, array[int] of var bool: b, set of int: values) =
  forall(i in index_set(b))(b[i] <-> x = i);
