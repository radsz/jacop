%-----------------------------------------------------------------------------%
% Constrains 'c' to not be the number of occurrences of 'y' in 'x'.
%-----------------------------------------------------------------------------%

predicate count_neq(array[int] of var int: x, var int: y, var int: c) =
%    c != sum(i in index_set(x)) ( bool2int(x[i] == y) );
     let {
       var int: limit
     }
     in 
       c != limit /\
       among_var(limit, x, [y]);

include "among_var.mzn"

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

