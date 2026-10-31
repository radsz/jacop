%----------------------------------------------------------%
% Rehan Abdul Aziz <raziz@student.unimelb.edu.au>
%
% Road construction problem.
% 
%----------------------------------------------------------%

%input
int: n;
set of int: N = 1..n;
array[N,N] of int: distance;
array[N,N] of int: cost;
int: budget;
int: M = 1000000;

%decision variables
array[N,N,N] of var 0..M: sp;
array[N,N] of var bool: construct;

constraint forall (x in N) (
	construct[x,x] = false 
/\ 	forall (s in N) (sp[x,x,s] = 0)
);

constraint forall (x,y in N where x<y) (
	let { var 0..1: c = bool2int(construct[x,y]) } in
		sp[x,y,1] = distance[x,y]*c + M*(1 - c)
);

constraint forall (x,y in N where x < y) (
	construct[y,x] = construct[x,y] 
/\	forall(s in N) (sp[y,x,s] = sp[x,y,s])
);

constraint forall (x,y in N, s in 1..n-1 where x<y) (
	sp[x,y,s+1] = 
		min(
			[sp[x,y,s]] ++ 
			[ sp[x,z,s] + if y<z then sp[y,z,s] else sp[z,y,s] endif
			| z in N where x<z /\ y!=z]
		)
);

constraint sum (x,y in N where x<y) 
	(cost[x,y] * bool2int(construct[x,y])) <= budget;

int: obj_min = sum(x, y in N where x < y)( lb(sp[x, y, n]) );
int: obj_max = sum(x, y in N where x < y)( ub(sp[x, y, n]) );
var obj_min..obj_max: objective;

constraint objective = sum (x,y in N where x<y) (sp[x,y,n]);

solve 
	:: seq_search([
		bool_search([construct[x,y] | x,y in N], input_order, indomain_max, complete),
		int_search([objective], input_order, indomain_min, complete)
	])
	minimize objective;

output [ 
    "construct = array2d(", show(N), ", ", show(N), ", ", show(construct), ");\n",
    "objective = ", show(objective), ";\n" 
];
