array[1..5] of var 0..12: x;
constraint forall(i, j in 1..5 where i < j)(abs(x[i] - x[j]) >= 3);
constraint x[1] <= 4 /\ x[2] != 6 /\ x[3] in {1, 2, 7, 8, 9, 12} /\ x[4] >= 5;
solve satisfy;
output ["x = \(x);\n"];
