predicate multi_inter_distance(array[int] of var int: x, int: m, int: p) =
  forall(v in lb_array(x)..ub_array(x))(
    sum(i in index_set(x))(bool2int(x[i] >= v /\ x[i] <= v + p - 1)) <= m);
