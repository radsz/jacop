%-----------------------------------------------------------------------------%
% Constrains the array of objects 'x' to form a Hamiltonian circuit in a graph.
%-----------------------------------------------------------------------------%
predicate circuit(array[int] of var int: x) =
    jacop_circuit(x);

predicate jacop_circuit(array[int] of var int: x)
