/* Set `out` to be a random value between `low` and `high` (inclusive) from a uniform distribution */
predicate fzn_on_restart_uniform_int(int: low, int: high, var int: out) = jacop_on_restart_uniform_int(low, high, out);

predicate jacop_on_restart_uniform_int(int: low, int: high, var int: out);
