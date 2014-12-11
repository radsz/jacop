/** @group globals
  Constrains the elements of \a x to define a circuit where \a x[\p i] = \p j means
  that \p j is the successor of \p i.
*/
predicate circuit(array[int] of var int: x) =
    jacop_circuit(x);

predicate jacop_circuit(array[int] of var int: x)
