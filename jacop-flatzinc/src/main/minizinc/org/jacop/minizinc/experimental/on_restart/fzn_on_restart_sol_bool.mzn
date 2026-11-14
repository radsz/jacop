/* Set `out` to be a the last solution value of `input` on each restart */
predicate fzn_on_restart_sol_bool(var bool: input, var bool: out) = jacop_on_restart_sol_bool(input, out);

predicate jacop_on_restart_sol_bool(var bool: input, var bool: out);
