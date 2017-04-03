% Model for filter scheduling and resource assignment
%
% Author: Krzysztof Kuchcinski

include "globals.mzn";

int : n; % number of operations
set of int : add;
set of int : mul;
set of int : Last;	% last/1 is a built-in function in Zinc.
int : del_add;
int : del_mul;
int : number_add;
int : number_mul;

array[1..n] of set of int : dependencies;

array[1..n] of var 0..100 : t;
array[1..n] of var 1..10 : r;
array[1..n] of var 1..10 : d = [ if i in add then del_add else del_mul endif | i in 1..n ];
array[1..card(add)] of var 0..1000 : t_add = [t[i] | i in add];
array[1..card(mul)] of var 0..1000 : t_mul = [t[i] | i in mul];
var 0..1000: objective;

constraint  % to be sure that the model is correct- can be removed
	add intersect mul = {}
	/\
	card(add) + card(mul) = n;	

constraint % dependencies
    forall (i in 1..n, j in dependencies[i]) (
	   t[i] + d[i] <= t[j]
    );

constraint 
    forall (i in 1..n) (
       if (i in add) then r[i] <= number_add else r[i] <= number_mul endif
       );

constraint
     let {
       array[1..card(add)] of var int : t_add = [ t[i] | i in add],
       array[1..card(add)] of var int : r_add = [ r[i] | i in add],
       array[1..card(add)] of var int : d_add = [ del_add | i in add],
       array[1..card(add)] of var int : h_add = [ 1 | i in add]
     }
     in 
       diffn(t_add, r_add, d_add, h_add)
;

constraint
     let {
       array[1..card(mul)] of var int : t_mul = [ t[i] | i in mul],
       array[1..card(mul)] of var int : r_mul = [ r[i] | i in mul],
       array[1..card(mul)] of var int : d_mul = [ del_mul | i in mul],
       array[1..card(mul)] of var int : h_mul = [ 1 | i in mul]
     }
     in 
       diffn(t_mul, r_mul, d_mul, h_mul)
;
	

constraint
    let {
      array[1..card(Last)] of var 0..1000 : opp = [ t[i] + d[i] | i in Last]
    }
    in
      maximum(objective, opp);

solve 
	:: seq_search([
    	int_search(t, smallest, indomain_min, complete),
      	int_search(r, input_order, indomain_min, complete)
	]) 
	minimize objective;

output [
   "objective = ", show(objective), ";\n",
   "t = ", show(t), ";\n",
   "r = ", show(r), ";\n"
];
