predicate inter_distance(array[int] of var int: x, int: p) =
  forall(i, j in index_set(x) where i < j)(abs(x[i] - x[j]) >= p);
