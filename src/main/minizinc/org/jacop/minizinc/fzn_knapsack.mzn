predicate jacop_knapsack(array[int] of int:w, array[int] of int:p, 
         var int: W, var int: P, array[int] of var int:x);

predicate fzn_knapsack(array[int] of int: w, array[int] of int:p, 
                   array[int] of var int:x, var int: W, var int: P) = 
	let {
	   var 0..ub(P): profit,
	} in 
	    jacop_knapsack([w[i] | i in index_set(w) where w[i] > 0], [p[i] | i in index_set(p) where w[i] > 0], W, profit, [x[i] | i in index_set(x) where w[i] > 0])
	    /\
	    P = profit + sum( i in index_set(p) where w[i]=0) (p[i]*x[i]) 
	;

