predicate disjunctive_setup(array[int] of var int: s, array[int] of var int: d,
                            array[int] of int: f, array[int, int] of int: t) =
  forall(i in index_set(d))(d[i] >= 0) /\
  forall(i, j in index_set(s) where i < j)(
    s[i] + d[i] + t[f[i], f[j]] <= s[j] \/ s[j] + d[j] + t[f[j], f[i]] <= s[i]);
predicate disjunctive_setup(array[int] of var opt int: s, array[int] of var int: d,
                            array[int] of int: f, array[int, int] of int: t) =
  forall(i in index_set(d))(d[i] >= 0) /\
  forall(i, j in index_set(s) where i < j)(
    (occurs(s[i]) /\ occurs(s[j])) ->
    (deopt(s[i]) + d[i] + t[f[i], f[j]] <= deopt(s[j]) \/ deopt(s[j]) + d[j] + t[f[j], f[i]] <= deopt(s[i])));
