/* Set `out` to be a random value between `low` and `high` (inclusive) from a uniform distribution */
predicate fzn_on_restart_uniform_float(float: low, float: high, var float: out) = jacop_on_restart_uniform_float(low, high, out);

predicate jacop_on_restart_uniform_float(float: low, float: high, var float: out);
