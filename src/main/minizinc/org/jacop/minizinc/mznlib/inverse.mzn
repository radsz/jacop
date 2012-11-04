%-----------------------------------------------------------------------------%
% Constrains two arrays of int variables, 'f' and 'invf', to represent
% inverse functions.  All the values in each array must be within the index
% set of the other array.
%-----------------------------------------------------------------------------%
predicate inverse(array[int] of var int: f,
                  array[int] of var int: invf) =
      jacop_assignment(f, invf, min(index_set(f)), min(index_set(invf)));

predicate jacop_assignment(array[int] of var int: f,
                           array[int] of var int: invf,
			   int: index_f, int: index_invf);

%    forall(i in index_set(f), j in index_set(invf)) (
%           f[i] in index_set(invf) /\
%        invf[j] in index_set(f   ) /\
%        (j == f[i] <-> i == invf[j])
%    );

