predicate jacop_networkflow(array[int] of int: arc, 
	  	            array[int] of var int: flow, array[int] of var int: weight,
	  	            array[int] of int: balance, var int: cost);

predicate fzn_network_flow_cost(array[int,1..2] of int: arc, 
	  	      array[int] of int: balance,
	  	      array[int] of int: weight,
            array[int] of var int: flow, var int: cost) = 
	let {
	  % nodes are renumbered from 1 to match the positions in the balance array
	  int: first = min(index_set(balance));
	} in
               jacop_networkflow([arc[i, j] - first + 1 | i in index_set_1of2(arc), j in 1..2],
                                 flow, weight, balance, cost)
	  % the network bounds the cost only from below; the sum bounds it from both sides
	  /\ cost = sum(i in index_set_1of2(arc))(weight[i] * flow[i])
	;
