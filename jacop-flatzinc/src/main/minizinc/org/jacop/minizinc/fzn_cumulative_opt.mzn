predicate jacop_cumulative_optional(array[int] of var int: start,
  array[int] of var int: dur, array[int] of var int: res,
  var int: limit, array[int] of var bool: o);

predicate fzn_cumulative_opt(array[int] of var opt int: s,
                     array[int] of var int: d,
                     array[int] of var int: r, var int: b) =
    jacop_cumulative_optional([if is_fixed(si) /\ absent(fix(si)) then 0 else deopt(si) endif | si in s ],
                              d, r, b, [ occurs(si) | si in s ]);
