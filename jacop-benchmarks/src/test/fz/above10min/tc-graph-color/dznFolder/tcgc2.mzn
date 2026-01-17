%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%       Time-changing Graph Coloring Problem
%       
%       Given:
%         - a graph (by the head and tail of 
%             each edge)
%         - an initial valid coloring with "c" colors
%         - an ending valid coloring with "c" colors
%         - a maximum number fo steps "max_s"
%         - a number of possible modifications "k"
%
%        Objective: minimize the number of steps "s"
%        that it takes to convert the inital coloring
%        into the end coloring by applying at most "k"
%        changes of colors at each step, while always
%        maintaining a valid coloring.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


   
int: nbV;
int: nbE;
set of int: EDGES = 1..nbE;
set of int: NODES = 1..nbV;
set of int: COLORS = 1..c;

array [EDGES] of NODES: heads;
array [EDGES] of NODES: tails; 

array [NODES] of int: init;
array [NODES] of int: end;
int: c = max(init ++ end);


int: max_s = 10;
var 2..max_s: s;
set of int: STEPS = 1..max_s;
int: k;

predicate valid_coloring(array [NODES] of var COLORS: coloring, array [EDGES] of NODES: xs, array [EDGES] of NODES: ys) =
	forall (e in EDGES) (coloring[xs[e]] != coloring[ys[e]]);


array [STEPS,NODES] of var COLORS: a;
constraint forall(n in NODES) (a[1,n] = init[n]);
constraint forall(n in NODES) (a[s,n] = end[n]); 

constraint forall (s in STEPS) (valid_coloring([a[s,n] | n in NODES],heads,tails));

constraint forall (i in 1..max_s-1) ( i < s -> sum (n in NODES) (a[i,n] != a[i+1,n]) <= k);
constraint forall (i in 1..max_s-1) (i >= s -> forall (n in NODES) (a[i,n] == a[i+1,n]));

solve 
::seq_search([
	int_search([s],input_order,indomain_min,complete),
	int_search([a[s,n] | s in STEPS, n in NODES],input_order,indomain_min,complete)
	])
   minimize objective;
%var 2..max_s: objective;
%
int: obj_ub = (k * max_s + 1) * max_s + k * max_s;
var 0..obj_ub: objective;

constraint objective = (k * max_s + 1) * s + sum(i in 1..max_s-1, n in NODES)(a[i,n]!=a[i+1,n]);

output [
    "a = array2d(STEPS,NODES,\(a));\n",
    "s = \(s);\n",
    "objective = \(objective);\n",
];

