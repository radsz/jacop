%
% Model for filter scheduling and resource assignment
%

include "diffn.mzn";
include "maximum.mzn";

int : n; % number of operations
set of int : add;
set of int : mul;
set of int : last;
int : del_add;
int : del_mul;
int : number_add;
int : number_mul;

array[1..n] of set of int : dependencies;

array[1..n] of var 0..1000 : t;
array[1..n] of var 1..10 : r;
array[1..n] of var 1..10 : d = [ if i in add then del_add else del_mul endif | i in 1..n ];
array[1..card(add)] of var 0..1000 : t_add = [t[i] | i in add];
array[1..card(mul)] of var 0..1000 : t_mul = [t[i] | i in mul];
var int : end;

% Decomposition if solver does not support diff2 or similar constraint
%
%predicate diff2(array[int] of var int: x, array[int] of var int: y,
%	        array[int] of var int: lx, array[int] of var int: ly) =
%		forall(i in min(index_set(x)) .. max(index_set(x))-1, 
%		       j in i+1 .. max(index_set(x)) )
%		(
%		x[i] + lx[i] <= x[j]
%		\/
%		x[j] + lx[j] <= x[i]
%		\/
%		y[i] + ly[i] <= y[j]
%		\/
%		y[j] + ly[j] <= y[i]
%);

constraint  % to be sure that the model is correct
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

% constraint
%     let {
%        array[1..card(add), 1..4] of var int : rect = array2d(1..card(add), 1..4, 
%                      [ if j == 1 then t[i] else 
%                         if j == 2 then r[i] else 
%                          if j == 3 then del_add else 
%                            1 endif 
%                          endif 
%                        endif | i in add, j in 1..4])
%     }
%     in
%       diff2(rect);

% constraint
%     let {
%        array[1..card(mul), 1..4] of var int : rect = array2d(1..card(mul), 1..4, 
%                      [ if j == 1 then t[i] else 
%                         if j == 2 then r[i] else 
%                          if j == 3 then del_mul else 
%                            1 endif 
%                          endif 
%                        endif | i in mul, j in 1..4])
%     }
%     in
%       diff2(rect);

constraint
     let {
       array[1..card(add)] of var int : t_add = [ t[i] | i in add],
       array[1..card(add)] of var int : r_add = [ r[i] | i in add],
       array[1..card(add)] of var int : d_add = [ del_add | i in add],
       array[1..card(add)] of var int : h_add = [ 1 | i in add]
     }
     in 
       diffn(t_add, r_add, d_add, h_add);

constraint
     let {
       array[1..card(mul)] of var int : t_mul = [ t[i] | i in mul],
       array[1..card(mul)] of var int : r_mul = [ r[i] | i in mul],
       array[1..card(mul)] of var int : d_mul = [ del_mul | i in mul],
       array[1..card(mul)] of var int : h_mul = [ 1 | i in mul]
     }
     in 
       diffn(t_mul, r_mul, d_mul, h_mul);

constraint
    let {
      array[1..card(last)] of var 0..1000 : opp = [ t[i] + d[i] | i in last]
    }
    in
      maximum(end, opp);

%constraint
%	forall (i in 1..n) (
%	   end >= t[i] + d[i]
%	);

%solve :: int_search( t ++ r, input_order, indomain_min, complete) minimize end;

solve :: seq_search([
      int_search(t, smallest, indomain_min, complete),
      int_search(r, input_order, indomain_min, complete)

%      seq_search([
%           int_search(t_add, largest, indomain_min, complete),
%      	   int_search(t_mul, input_order, indomain_min, complete)
%      ])

]) minimize end;

output [
   show( end ),
   show( t ),
   show( r )
];
