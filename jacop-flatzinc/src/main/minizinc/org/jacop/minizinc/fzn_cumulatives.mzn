include "fzn_cumulative_opt.mzn";
include "fzn_cumulatives_decomp.mzn";

% cumulatives with an upper bound and non-negative requirements is posted as one
% optional cumulative per machine; a task is present on machine k iff machine[i] = k.
% Lower bounds and negative requirements keep the standard decomposition.
predicate fzn_cumulatives(array[int] of var int: start,
                          array[int] of var int: duration,
                          array[int] of var int: resource,
                          array[int] of var int: machine,
                          array[int] of var int: bound,
                          bool: is_upper_bound,
                          int: min_machine) =
  if is_upper_bound /\ lb_array(duration) >= 0 /\ lb_array(resource) >= 0 /\ lb_array(bound) >= 0 then
    forall (k in index_set(bound)) (
      let {
        array[int] of int: ts = [i | i in index_set(start) where k in dom(machine[i])];
      } in
      if length(ts) > 0 then
        jacop_cumulative_optional([start[i] | i in ts], [duration[i] | i in ts],
                                  [resource[i] | i in ts], bound[k],
                                  [machine[i] = k | i in ts])
      endif
    )
  else
    fzn_cumulatives_decomp(start, duration, resource, machine, bound, is_upper_bound)
  endif;
