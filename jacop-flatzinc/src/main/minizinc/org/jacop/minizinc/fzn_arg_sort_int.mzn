include "fzn_inverse.mzn";
include "lex_less.mzn";

% y = x sorted and x[i] = y[z[i] - offset]
predicate jacop_sort_permutation(array[int] of var int: x,
                                 array[int] of var int: y,
                                 array[int] of var int: z,
                                 int: offset);

% the positions z of the elements of x in sorted order are the inverse of the permutation p;
% equal values keep the order of their indices
predicate fzn_arg_sort_int(array[int] of var int: x,
                           array[int] of var int: p) =
    let {
      int: n = length(x);
      array[1..n] of var lb_array(x)..ub_array(x): y;
      array[index_set(x)] of var 1..n: z;
    } in
    jacop_sort_permutation(x, y, z, 1) /\
    fzn_inverse(z, p) /\
    forall (j in 1..n - 1) (lex_less([y[j], p[j]], [y[j + 1], p[j + 1]]));
