/** @group globals.channeling
  Constrains two arrays of int variables, \a f and \a invf, to represent
  inverse functions.  All the values in each array must be within the index
  set of the other array.
*/
predicate inverse(array[int] of var int: f,
                  array[int] of var int: invf) =
    jacop_assignment(f, invf, min(index_set(f)), min(index_set(invf)));

    % forall(i in index_set(f), j in index_set(invf)) (
    %        f[i] in index_set(invf) /\
    %     invf[j] in index_set(f   ) /\
    %     (j == f[i] <-> i == invf[j])
    % );

predicate jacop_assignment(array[int] of var int: f,
                           array[int] of var int: invf,
			   int: index_f, int: index_invf);

% predicate jacop_assignment_reif(array[int] of var int: f,
%                            array[int] of var int: invf,
% 			   int: index_f, int: index_invf, var bool: b) =
%     abort("Reified inverse/2 is not supported.");


