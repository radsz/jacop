include "globals.mzn";
% Strict disjunctive on optional tasks with variable durations, which did not compile because the
% durations were passed through fix(). Named o and st keep the output the same in both FlatZinc files.
array[1..3] of var bool: o;
array[1..3] of var 0..5: st;
array[1..3] of var 1..3: d;
array[1..3] of var opt 0..5: s = [if o[i] then st[i] else <> endif | i in 1..3];
constraint forall(i in 1..3)(not o[i] -> st[i] = 0);
constraint disjunctive_strict(s, d);
constraint sum(o) >= 2;
solve satisfy;
