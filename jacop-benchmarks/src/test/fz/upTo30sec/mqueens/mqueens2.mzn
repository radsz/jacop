include "lex_lesseq.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: n; % size

%------------------------------------------------------------------------------%
% Variables

array[1..n,1..n] of var bool: filled;
array[1..n,1..n] of var 0..1: f = 
     array2d(1..n,1..n,[bool2int(filled[i,j]) | i,j in 1..n]);
array[1..n] of var 0..n: q;
var 0..n: objective;

%------------------------------------------------------------------------------%
% Predicates for symmetry breaking

predicate rot_sqr_sym(array[int,int] of var int: x) = 
	let {
		int: n = card(index_set_1of2(x)),
        int: n2 = card(index_set_2of2(x)),
        int: l = n * n,
        array[1..l] of var int: y = [x[i,j] | i in index_set_1of2(x),
                                              j in index_set_2of2(x) ],
        array[1..4,1..l] of 1..l: p = array2d(1..4,1..l, 
             [ if k == 1 then i*n + j - n else 
               if k == 2 then (n - j)*n + i else 
               if k == 3 then (n - i)*n + (n - j)+1 else
                              i*n + (n - j) - n + 1 endif endif endif
             | k in 1..4, i,j in 1..n ])
  } in assert(n == n2, "rot_sqr_sym: rotation symmetry applied to" ++
              " non square matrix", 
    var_perm_sym(y,p));

predicate var_perm_sym(array[int] of var int: x, array[int,int] of int: p) =
   let { int: l = min(index_set_1of2(p)),
         int: u = max(index_set_1of2(p)),
         array[1..length(x)] of var int: y = [ x[i] | i in index_set(x)] } in
   forall (i in l..u, j in l..u where i != j) (
      var_perm_sym_pairwise(y, %% forces index 1..length(x) 
                            [ p[i,k] | k in index_set_2of2(p)], 
                            [ p[j,k] | k in index_set_2of2(p)]) );

predicate var_perm_sym_pairwise(array[int] of var int: x, 
          array[int] of int: p1, array[int] of int: p2) =
   let { array[1..length(x)] of 1..length(x): invp1 = 
              [ j | i,j in 1..length(x) where p1[j] = i ] } in
   lex_lesseq(x, [ x[p2[invp1[i]]] | i in 1..length(x) ]);

%------------------------------------------------------------------------------%
% Constraints

constraint forall(i, j in 1..n)(
	filled[i,j] = not (
		exists(j1 in 1..n where j1 != j)(filled[i,j1])
	\/	exists(i1 in 1..n where i1 != i)(filled[i1,j])
	\/	exists(k in 1..n-1)(
			filled[i+k,j+k] \/ filled[i-k,j+k]
	    \/	filled[i+k,j-k] \/ filled[i-k,j-k]
		)
	)
);

constraint forall(i in 1..n)(
	q[i] = sum(j in 1..n)(j * f[i,j])
);

constraint objective = sum(i in 1..n)(bool2int(q[i] > 0));

constraint rot_sqr_sym(f);  

%------------------------------------------------------------------------------%
% Search

solve 
	:: int_search([f[i, j] | i, j in 1..n], input_order, indomain_max, complete)
	minimize objective;  		

%------------------------------------------------------------------------------%
% Output

output [ 
	"q = ", show(q), ";\n",
	"objective = ", show(objective), ";\n"
]
