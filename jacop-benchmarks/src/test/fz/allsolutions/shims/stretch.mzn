% every maximal run of value values[k] has a length in min_v[k]..max_v[k]; x takes only these values
predicate stretch(array[int] of int: values, array[int] of int: min_v, array[int] of int: max_v,
                  array[int] of var int: x) =
  let { int: l = min(index_set(x)), int: u = max(index_set(x)) } in
  forall(i in index_set(x))(x[i] in {values[k] | k in index_set(values)}) /\
  forall(k in index_set(values), i in l..u)(
    let { var bool: start = if i = l then x[i] = values[k] else x[i] = values[k] /\ x[i - 1] != values[k] endif } in
    start -> (
      if i + min_v[k] - 1 > u then false
      else forall(j in i..i + min_v[k] - 1)(x[j] = values[k]) endif /\
      if i + max_v[k] <= u then exists(j in i..i + max_v[k])(x[j] != values[k]) else true endif));
