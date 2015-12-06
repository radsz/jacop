/** @group globals
  Constrains the elements of \a x to define a circuit where \a x[\p i] = \p j means
  that \p j is the successor of \p i.
*/
predicate circuit(array[int] of var int: x) =
  if min(index_set(x)) = 1 then
    jacop_circuit(x)
  else
    jacop_circuit([x[i] - min(index_set(x)) + 1 | i in index_set(x)])
  endif;
  
predicate jacop_circuit(array[int] of var int: x);

% predicate jacop_circuit_reif(array[int] of var int: x, var bool: b) = 
%     abort("Reified circuit/1 is not supported.");
