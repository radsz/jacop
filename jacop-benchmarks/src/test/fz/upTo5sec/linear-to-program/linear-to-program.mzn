% Main author: Jean-Noel Monette, Uppsala University

% This model finds a shortest program to compute a linear combination
% of variables. The difficulty is that the program can only use the
% binary plus and the unary minus. To symbolic program is linked to a
% set of examples against which it must conform. This is one part of a
% counter-example guided loop, where examples are added when a counter
% example is found for the generated programs. The counter-example
% generation is the other part and not included in this problem, which
% only does the program generation. 
% As an example:
% if the linear combination is -2 * p0 + -1 * p1 + 2 * p2, then a
% shortest program (among others) might be:
% x3 = p0 + p0
% x4 = p1 + x3
% x5 = p2 + p2
% x6 = - x4
% x7 = x5 + x6
% return x7
% 


include "globals.mzn";

%------------------------------------------------------------------------------%
% Input parameters

int: N; % maximum number of lines in the program
int: M; % number of input params
array[P] of int: coef; % coefficients of the linear combination

int: Np; %number of plus symbols
int: Smax; % number of examples
array[S,P] of int: RP; % array of real parameters (indexed by examples and positions)


%------------------------------------------------------------------------------%
% sets/ranges

set of int: P 	= 0..M-1; 		% set of input parameters
set of int: R 	= M..M+N-1; 	% set of return variables
set of int: LN 	= M..M+N-1; 	% domain of line numbers
set of int: ALN = 0..M+N-1; 	% domain of line numbers plus input params
set of int: I = 0..sum(i in R)(if i< M+Np then 2 else 1 endif)-1; % set of (local) input variables 
array[R] of set of int: Ii = array1d(R, 
	[ 	if i==M then 0..1 
		else sum(j in M..i-1)(if j < M+Np then 2 else 1 endif) 
			..sum(j in M..i)(if j < M+ Np then 2 else 1 endif)-1 
		endif
	| i in R]);
set of int: S = 1..Smax; % set of examples

%model

%------------------------------------------------------------------------------%
%variables and constraints for a Well-Formed-Program

array[R] of var LN: line_o;
array[I] of var ALN: line_i;
var R: objective;

	% each component is on a different line
constraint alldifferent(line_o); 

	% ordering of the lines (components use output of previous lines)
constraint forall(i in R, j in Ii[i]) (line_i[j] < line_o[i]);

%symmetry breaking of the program
constraint 
	forall(i in M..M+Np-2) (line_o[i]   < line_o[i+1]) % all plus are equivalent
 /\ forall(i in M+Np..M+N-2)(line_o[i] < line_o[i+1])  % all minus are equivalent
 /\ forall(i in M..M+Np-1)(line_i[min(Ii[i])] <= line_i[min(Ii[i])+1]); % plus is commutative




%variables and constraint for each example
int: max_x_ = 2 * max(max(s in S,p in P)(abs(RP[s,p])), max(s in S)(abs(x_O[s])));

array[S,R] of var -max_x_..max_x_: x_o;
array[S,I] of var -max_x_..max_x_: x_i;
array[S] of int: x_O = array1d(S, [sum(p in P)(coef[p] * RP[s,p]) | s in S]);

constraint forall(s in S,r in R)(
        if r<M+Np then 
                x_o[s,r] == x_i[s,min(Ii[r])] + x_i[s,min(Ii[r])+1]
        else
                x_o[s,r] == - x_i[s,min(Ii[r])]
        endif 
);


%link between the examples and the program
constraint 
	forall(s in S)(
		% links the general output
		forall(r in R)( line_o[r]==objective -> x_o[s,r]==x_O[s] ) 
		% links the general inputs
 	/\	forall(j in I)( line_i[j]<M -> x_i[s,j]==RP[s,line_i[j]] ) 
		% links the output/input of the intermediate lines
	/\	forall(r in R,j in I)( line_o[r]==line_i[j] -> x_o[s,r]==x_i[s,j]) 
	/\	forall(r in R,j in Ii[r])( line_o[r] > objective -> line_i[j] == 0 ) 
	);


solve 
	:: seq_search([
		int_search([objective],  input_order, indomain_min, complete),
      	int_search(line_o, first_fail, indomain_min, complete),
		int_search(line_i, first_fail, indomain_min, complete),
		int_search([x_o[s,r] | s in S, r in R], first_fail, indomain_min, complete),
		int_search([x_i[s,i] | s in S, i in I], first_fail, indomain_min, complete)
	]) 
   	minimize objective;

output 
["line_o = array1d(R,",show(line_o),");\n"] ++
["line_i = array1d(I,",show(line_i),");\n"] ++
["objective = ",show(objective),";\n\n"] ++
[	let {
		int: k = min(j in R where fix(line_o[j])==i)(j)
	} in (
		"x" ++ show(i) ++ " = " ++ 
		if k < M+Np then
			if fix(line_i[min(Ii[k])]) < M then "p" else "x" endif 
			++ show(line_i[min(Ii[k])]) ++ " + " ++
			if fix(line_i[min(Ii[k])+1]) < M then "p" else "x" endif
			++ show(line_i[min(Ii[k])+1]) 
		else 
			"- " ++ 
			if fix(line_i[min(Ii[k])]) < M then "p" else "x" endif
			++ show(line_i[min(Ii[k])]) 
		endif 
        ++ "\n"
	)
|	i in R where i <= fix(objective) ] ++
["return x" ++ show(objective) ++ "\n"]
;
