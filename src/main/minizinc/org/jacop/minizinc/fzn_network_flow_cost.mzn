predicate jacop_networkflow(array[int, int] of int: arc, 
	  	            array[int] of var int: flow, array[int] of var int: weight,
	  	            array[int] of int: balance, var int: cost);

predicate fzn_network_flow_cost(array[int,1..2] of int: arc, 
	  	      array[int] of int: balance,
	  	      array[int] of int: weight,
            array[int] of var int: flow, var int: cost) = 
	jacop_networkflow(arc, flow, weight, balance, cost)
	;
