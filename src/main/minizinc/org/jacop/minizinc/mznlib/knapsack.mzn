predicate knapsack(array[int] of int: w, array[int] of int:p, 
                   array[int] of var int:x, var int: W, var int: P) = 
	assert(index_set(w) = index_set(p),  
		"index set of weights must be equal index set of profits",
	assert(lb_array(x) >= 0,
		"variables in knapsack must be non-negative",
	assert(lb_array(w) >= 0,
		"weights in knapsack must be non-negative",

	% Decomposition
%	P = sum(i in 1..n) (x[i]*p[i])
%	/\
%	W = sum(i in 1..n) (x[i]*w[i])

	 jacop_knapsack(w,p,W,P,x)

	 )));

predicate
jacop_knapsack(array[int] of int:w, array[int] of int:p, 
         var int: W, var int: P, array[int] of var int:x);
