%-----------------------------------------------------------------------------%
% Defines decomposition for knapsack constraint.
% w- defines size for items to be packed
% p- defines profit for each item
% x- defines how many items is packed of each kind
% W- defines total size of all items in the knapsack
% P- defines total profit in the knapsack
%-----------------------------------------------------------------------------%

predicate knapsack(array[int] of int: w, array[int] of int:p, 
                   array[int] of var int:x, var int: W, var int: P) = 
	assert(index_set(w) = index_set(p) /\ index_set(w) = index_set(x),
		"index set of weights must be equal index set of profits and index set of items",
	assert(lb_array(x) >= 0,
		"variables in knapsack must be non-negative",
	assert(lb(W) >= 0,
		"size of knapsack must be non-negative",
	assert(lb(P) >= 0,
		"profit in knapsack must be non-negative",

	% ==== Decomposition ====
%	P = sum(i in index_set(p)) (x[i]*p[i])
%	/\
%	W = sum(i in index_set(w)) (x[i]*w[i])
	% =======================

	let {
	   var 0..ub(P): profit,
	} in 
	    jacop_knapsack([w[i] | i in index_set(w) where w[i] > 0], [p[i] | i in index_set(p) where w[i] > 0], W, profit, [x[i] | i in index_set(x) where w[i] > 0])
	    /\
	    P = profit + sum( i in index_set(p)) (p[i]*x[i]*bool2int(w[i]=0)) 
	 ))));

predicate
jacop_knapsack(array[int] of int:w, array[int] of int:p, 
         var int: W, var int: P, array[int] of var int:x);
