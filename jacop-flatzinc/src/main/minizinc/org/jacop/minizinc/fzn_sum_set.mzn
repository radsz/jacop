predicate jacop_sum_set(array[int] of int: values, array[int] of int: weights,
                        var set of int: selected, var int: total);

% SumWeightedSet needs non-negative weights; negative ones keep the decomposition.
predicate fzn_sum_set(array[int] of int: values, array[int] of int: weights,
                      var set of int: selected, var int: total) =
    if length(weights) > 0 /\ min(weights) >= 0 then
        jacop_sum_set(array1d(values), array1d(weights), selected, total)
    else
        total == sum(j in index_set(values)) ((values[j] in selected) * weights[j])
    endif;
