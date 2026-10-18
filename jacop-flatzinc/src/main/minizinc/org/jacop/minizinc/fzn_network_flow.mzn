predicate jacop_networkflow(array[int] of int: arc, 
	  	            array[int] of var int: flow, array[int] of var int: weight,
	  	            array[int] of int: balance, var int: cost);

predicate fzn_network_flow(array[int,1..2] of int: arc, 
	  	                 array[int] of int: balance,
                       array[int] of var int: flow) = 
	let {
	  % with unit weights the cost is the total flow, which also bounds the cost variable
	  var int: cost = sum(flow);
	  array[index_set_1of2(arc)] of int: weight = [1 | i in index_set_1of2(arc)];
	} in
	   jacop_networkflow(array1d(arc), flow, weight, balance, cost)
	;
