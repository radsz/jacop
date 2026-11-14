predicate jacop_knapsack(array[int] of int:w, array[int] of int:p, 
         var int: W, var int: P, array[int] of var int:x);

predicate fzn_knapsack(array[int] of int: w, array[int] of int:p, 
                   array[int] of var int:x, var int: W, var int: P) = 
	let {
	   % jacop_knapsack requires positive weights and profits; other items are added linearly
	   set of int: items = {i | i in index_set(x) where w[i] > 0 /\ p[i] > 0},
	   var 0..ub(W): weight,
	   var 0..ub(P): profit,
	} in
	    forall(i in index_set(x))(x[i] >= 0)
	    /\
	    if card(items) = 0 then
	      weight = 0 /\ profit = 0
	    else
	      jacop_knapsack([w[i] | i in items], [p[i] | i in items], weight, profit, [x[i] | i in items])
	    endif
	    /\
	    W = weight + sum(i in index_set(x) where w[i] > 0 /\ p[i] = 0) (w[i]*x[i])
	    /\
	    P = profit + sum(i in index_set(x) where w[i] = 0) (p[i]*x[i])
	;

