
int: n; % size of board

array [0..n+1,0..n+1] of var 0..1: x;
array [0..n+1,0..n+1] of var 0..2: w;
array [0..n+1] of var 0..2*(n+2)*(n+2): wastage_sum; 
var 0..n*n: OBJECTIVE;

% wastage relation

predicate still_life(array [int] of var 0..1: x, var 0..2: w) = (
	let { 
		var 0..8: s1 = x[1] + x[2] + x[3] + x[4] + x[6] + x[7] + x[8] + x[9],
		var 0..8: s2 = x[1]*x[3] + x[3]*x[9] + x[9]*x[7] + x[7]*x[1] + x[2] + x[4] + x[6] + x[8],
		var 0..4: s3 = x[2] + x[4] + x[6] + x[8]
	} in 
	(x[5] = 1 -> s1 >= 2) /\
	(x[5] = 1 -> s1 <= 3) /\
	(x[5] = 0 -> s1 != 3) /\
	((x[5] = 1 /\ s2 <= 1) -> w >= 1) /\
	((x[5] = 1 /\ s2 <= 0) -> w >= 2) /\
	((x[5] = 0 /\ s3 >= 4) -> w >= 2) /\
	((x[5] = 0 /\ s3 <= 1) -> w >= 1) /\
	((x[5] = 0 /\ s3 <= 0) -> w >= 2)
);
	
% boundary conditions	

constraint forall (i in 0..n+1) (
	x[0,i] = 0 /\ x[n+1,i] = 0 /\ x[i,0] = 0 /\ x[i,n+1] = 0
);

constraint forall (i in 2..n-1) (
	x[1,i-1] + x[1,i] + x[1,i+1] <= 2
);

constraint forall (i in 2..n-1) (
	x[n,i-1] + x[n,i] + x[n,i+1] <= 2
);

constraint forall (i in 2..n-1) (
	x[i-1,1] + x[i,1] + x[i+1,1] <= 2
);

constraint forall (i in 2..n-1) (
	x[i-1,n] + x[i,n] + x[i+1,n] <= 2
);

% still life + wastage constraints

constraint forall (i, j in 1..n) (
	still_life([x[k,l] | k in i-1..i+1, l in j-1..j+1], w[i,j])
);

constraint forall (i in 1..n) (
	w[0,i] + x[1,i] = 1 /\
	w[n+1,i] + x[n,i] = 1 /\
	w[i,0] + x[i,1] = 1 /\
	w[i,n+1] + x[i,n] = 1
);



% sum wastage row by row

constraint wastage_sum[0] = sum (j in 0..n+1) (w[0,j]);
constraint forall (i in 1..n+1) (wastage_sum[i] = wastage_sum[i-1] + sum (j in 0..n+1) (w[i,j]));

constraint 4*OBJECTIVE = 2*n*n + 4*n - wastage_sum[n+1];

%constraint OBJECTIVE = sum (i, j in 1..n) (x[i,j]);

% redundant constraints using results from Chu et al. (2012).

constraint forall (i in 0..n) (wastage_sum[n+1] >= wastage_sum[i] + 2*((n-i) div 3) + n div 3);

% solve goal

solve :: int_search([x[i,j] | i, j in 1..n], input_order, indomain_max, complete) maximize OBJECTIVE;

output [
    "x = ", show(x), "\n",
    "w = ", show(w), "\n",
    "OBJECTIVE = ", show(OBJECTIVE)
];
