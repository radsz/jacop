%-----------------------------------------------------------------------------%
% Counts 'values' on the list of  'x'
% It is soft in a sense that every violation of 'soft_counters' contributes
% to the violation 'cost'. It is hard in a sense that it does enforce 'hard_counters' bound.
% It uses value based violation metric.
% -----------------------------------------------------------------------------%
predicate soft_global_cardinality_int(array[int] of var int: x, array[int] of int: values,
                                      array[int] of var int: hard_counters, array[int] of var int: soft_counters,
				      var int: cost) =
	  jacop_softgcc(x, values, hard_counters, soft_counters, cost);

predicate jacop_softgcc(array[int] of var int: x, array[int] of int: values,
                        array[int] of var int: hard_counters, array[int] of var int: soft_counters,
			var int: cost);

%-----------------------------------------------------------------------------%
% The same with a choice of the violation measure. With variableBased = false
% it is the value based measure above. With variableBased = true 'cost' is the
% smallest number of variables of 'x' that must change their value (to any
% value) so that every value 'values[i]' occurs 'soft_counters[i]' times; it is
% max(shortage, excess) of the counts against the soft counters, and requires
% sum(soft_counters) <= length(x).
% -----------------------------------------------------------------------------%
predicate soft_global_cardinality_int(array[int] of var int: x, array[int] of int: values,
                                      array[int] of var int: hard_counters, array[int] of var int: soft_counters,
				      var int: cost, bool: variableBased) =
	  if variableBased then
	    jacop_softgcc_var(x, values, hard_counters, soft_counters, cost)
	  else
	    jacop_softgcc(x, values, hard_counters, soft_counters, cost)
	  endif;

predicate jacop_softgcc_var(array[int] of var int: x, array[int] of int: values,
                            array[int] of var int: hard_counters, array[int] of var int: soft_counters,
			    var int: cost);
