/* Set `out` to be a the last assigned value of `input` on each restart */
predicate fzn_on_restart_last_val_int(var int: input, var int: out) = jacop_on_restart_last_val_int(input, out);

predicate jacop_on_restart_last_val_int(var int: input, var int: out);
