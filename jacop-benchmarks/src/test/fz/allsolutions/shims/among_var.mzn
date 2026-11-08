predicate among_var(var int: n, array[int] of var int: x, array[int] of var int: v) =
  n = sum(i in index_set(x))(bool2int(exists(j in index_set(v))(x[i] = v[j])));
predicate among_var_reif(var int: n, array[int] of var int: x, array[int] of var int: v, var bool: b) =
  b <-> (n = sum(i in index_set(x))(bool2int(exists(j in index_set(v))(x[i] = v[j]))));
