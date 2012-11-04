%-----------------------------------------------------------------------------%
% Defines decomposition on network flow constraint.
% arc- defines for each position on the array a pair [source, sink] nodes
% flow- defines the variable defining posisble low and upper bound for the flow on each arc.
% weight- defines the unit cost of the flow through the arc.
% balance- defines, for each node, the difference between input and output flow.
% cost- defines the current cost of the flow.
%-----------------------------------------------------------------------------%

predicate networkflow(array[int,int] of int: arc, 
	  	      array[int] of var int: flow, array[int] of var int: weight,
	  	      array[int] of int: balance, var int: cost) = 

    let { int: source_arc = min(index_set_2of2(arc)),
    	  int: sink_arc = max(index_set_2of2(arc))
	}
	in
  	assert (
	   min(index_set(balance)) == 1 /\
	   sink_arc - source_arc == 1 /\
	   index_set_1of2(arc) == index_set(flow) /\
	   index_set(flow) == index_set(weight) /\
	   lb_array(arc) >= min(index_set(balance)) /\ 
	   ub_array(arc) <= max(index_set(balance)),
	   "networkflow: wrong sizes of input array parameters",

%	   cost = sum(i in index_set(flow)) (flow[i] * weight[i]) 
%	   /\
%	   forall (i in index_set(balance)) (
%	      sum (j in  index_set_1of2(arc) where i == arc[j,source_arc]) (flow[j]) - 
%	         sum (j in index_set_1of2(arc) where i == arc[j,sink_arc]) (flow[j]) = balance[i] 
%           )

	    jacop_networkflow(arc, flow, weight, balance, cost)
	);

predicate jacop_networkflow(array[int, int] of int: arc, 
	  	            array[int] of var int: flow, array[int] of var int: weight,
	  	            array[int] of int: balance, var int: cost);