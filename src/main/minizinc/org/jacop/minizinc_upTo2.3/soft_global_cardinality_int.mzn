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