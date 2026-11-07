predicate jacop_span(var bool: p0, var int: s0, var int: d0,
    array[int] of var bool: p, array[int] of var int: s, array[int] of var int: d);

predicate fzn_span(var opt int: span_start, var int: span_duration,
                   array[int] of var opt int: start,
                   array[int] of var int: duration) =
    jacop_span(occurs(span_start),
               if is_fixed(span_start) /\ absent(fix(span_start)) then 0
               else deopt(span_start) endif,
               span_duration,
               [ occurs(si) | si in start ],
               [ if is_fixed(si) /\ absent(fix(si)) then 0 else deopt(si) endif | si in start ],
               duration);
