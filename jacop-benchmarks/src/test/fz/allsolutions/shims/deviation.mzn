predicate deviation(array[int] of var int: x, int: s, var int: d) =
  sum(x) = s /\ d = sum(i in index_set(x))(abs(length(x) * x[i] - s));
predicate deviation(array[int] of var int: x, int: a, int: b, int: s, var int: d) =
  sum(x) = s /\ d = sum(i in index_set(x))(abs(a * x[i] - b));
predicate spread(array[int] of var int: x, int: s, var int: d) =
  sum(x) = s /\ d = sum(i in index_set(x))((length(x) * x[i] - s) * (length(x) * x[i] - s));
predicate spread(array[int] of var int: x, int: a, int: b, int: s, var int: d) =
  sum(x) = s /\ d = sum(i in index_set(x))((a * x[i] - b) * (a * x[i] - b));
