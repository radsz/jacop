% Cross-checked regression test, written for the global cardinality review (models that rely on global_cardinality).
% Search annotation made input_order/indomain_min on all decision variables, so
% every solver reaches the same solution.
% De Bruijn sequence B(3,4) as integers, with every digit occurring equally often (GCC).
include "globals.mzn";
int: base = 3; int: n = 4; int: m = pow(base, n);
array[1..m] of var 0..m-1: x;
array[1..m, 1..n] of var 0..base-1: b;
array[0..base-1] of var 0..m: gcc;
constraint alldifferent(x);
constraint forall(i in 1..m)(x[i] = sum(j in 1..n)(b[i,j] * pow(base, n-j)));
constraint forall(i in 2..m, j in 2..n)(b[i-1,j] = b[i,j-1]);
constraint forall(j in 2..n)(b[m,j] = b[1,j-1]);
constraint x[1] = min(x);
constraint global_cardinality([b[i,1] | i in 1..m], array1d(0..base-1, [d | d in 0..base-1]), gcc);
constraint forall(d in 1..base-1)(gcc[d] = gcc[0]);
solve :: seq_search([
    int_search(array1d(x) ++ array1d(b) ++ array1d(gcc), input_order, indomain_min, complete)])
  satisfy;
output ["x = \(x);\n"];
