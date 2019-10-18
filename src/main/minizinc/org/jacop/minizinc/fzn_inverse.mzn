predicate jacop_assignment(array[int] of var int: f,
                           array[int] of var int: invf,
			   int: index_f, int: index_invf);

predicate fzn_inverse(array[int] of var int: f,
                  array[int] of var int: invf) =
    jacop_assignment(f, invf, min(index_set(f)), min(index_set(invf)));
