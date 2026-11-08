predicate reservoir(array[int] of var int: times, array[int] of int: changes,
                    int: min_level, int: max_level) =
  forall(j in index_set(times))(
    let { var int: level = sum(i in index_set(times))(changes[i] * bool2int(times[i] <= times[j])) }
    in min_level <= level /\ level <= max_level);
