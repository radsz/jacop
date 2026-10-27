array[1..6] of var 0..7: x;
constraint forall(i in 1..6)(sum(j in 1..6)(bool2int(x[i] <= x[j] /\ x[j] < x[i] + 3)) <= 2);
constraint x[1] <= 2 /\ x[2] != 4 /\ x[3] in {0, 3, 6, 7} /\ x[5] >= 3;
solve satisfy;
output ["x = \(x);\n"];
