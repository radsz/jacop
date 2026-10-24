include "fzn_cumulative_opt.mzn";
include "fzn_cumulatives_decomp.mzn";

% Optional cumulatives: a task is present on machine k iff it occurs and machine[i] = k.
predicate fzn_cumulatives_opt(array[int] of var opt int: start,
                              array[int] of var int: duration,
                              array[int] of var int: resource,
                              array[int] of var int: machine,
                              array[int] of var int: bound,
                              bool: is_upper_bound,
                              int: min_machine) =
  if is_upper_bound /\ lb_array(duration) >= 0 /\ lb_array(resource) >= 0 /\ lb_array(bound) >= 0 then
    forall (k in index_set(bound)) (
      let {
        array[int] of int: ts = [i | i in index_set(start)
                                   where k in dom(machine[i]) /\ not (is_fixed(occurs(start[i])) /\ not fix(occurs(start[i])))];
      } in
      if length(ts) > 0 then
        jacop_cumulative_optional([deopt(start[i]) | i in ts], [duration[i] | i in ts],
                                  [resource[i] | i in ts], bound[k],
                                  [occurs(start[i]) /\ machine[i] = k | i in ts])
      endif
    )
  else
    fzn_cumulatives_decomp([si default 0 | si in start],
                           [if occurs(start[i]) then duration[i] else 0 endif | i in index_set(start)],
                           resource, machine, bound, is_upper_bound)
  endif;
