predicate jacop_disjunctive_strict_optional(array[int] of var int: start,
    array[int] of var int: dur, array[int] of var bool: o);

predicate fzn_disjunctive_strict_opt(array[int] of var opt int: s,
                                     array[int] of var int: d) =
    forall (i in index_set(d)) (d[i] >= 0)
    /\
    jacop_disjunctive_strict_optional(
                [if is_fixed(si) /\ absent(fix(si)) then 0 else deopt(si) endif | si in s],
                [fix(di) | di in d],
                [ occurs(si) | si in s ]
          );
