% Hard counters are the counts of the values. Value based: cost is the sum of
% |count - soft counter| over the values; variable based: max(shortage, excess) of the
% counts against the soft counters.
predicate soft_global_cardinality_int(array[int] of var int: x, array[int] of int: values,
    array[int] of var int: hard_counters, array[int] of var int: soft_counters, var int: cost) =
  forall(i in index_set(values))(hard_counters[i] = sum(j in index_set(x))(bool2int(x[j] = values[i]))) /\
  cost = sum(i in index_set(values))(abs(hard_counters[i] - soft_counters[i]));
predicate soft_global_cardinality_int(array[int] of var int: x, array[int] of int: values,
    array[int] of var int: hard_counters, array[int] of var int: soft_counters, var int: cost,
    bool: variableBased) =
  if variableBased then
    forall(i in index_set(values))(hard_counters[i] = sum(j in index_set(x))(bool2int(x[j] = values[i]))) /\
    cost = max(sum(i in index_set(values))(max(0, soft_counters[i] - hard_counters[i])),
               sum(i in index_set(values))(max(0, hard_counters[i] - soft_counters[i])))
  else
    soft_global_cardinality_int(x, values, hard_counters, soft_counters, cost)
  endif;
