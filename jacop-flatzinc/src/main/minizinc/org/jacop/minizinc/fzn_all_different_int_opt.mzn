predicate jacop_alldifferent_opt(array[int] of var int: x, array[int] of var bool: occurs);

% Absent variables take a value below every domain that AlldifferentExcept ignores.
predicate fzn_all_different_int_opt(array[int] of var opt int: xs) =
    jacop_alldifferent_opt(
        [if is_fixed(x) /\ absent(fix(x)) then 0 else deopt(x) endif | x in xs],
        [occurs(x) | x in xs]);
