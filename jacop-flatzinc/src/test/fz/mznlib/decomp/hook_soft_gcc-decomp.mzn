% The definitions of the two violation measures: value based sum |count - soft|, variable based
% the fewest variables to change, max(shortage, excess), defined when sum(soft) <= length(x).
array[1..4] of var 0..3: x;
array[1..2] of var 0..4: hard;
array[1..2] of var {0, 2, 3}: soft;
array[1..2] of var 0..8: cost;
array[1..2] of int: values = [2, 1];
constraint forall(k in 1..2)(hard[k] = sum(i in 1..4)(bool2int(x[i] = values[k])));
constraint cost[1] = sum(k in 1..2)(abs(hard[k] - soft[k]));
constraint sum(soft) <= 4
  /\ cost[2] = max(sum(k in 1..2)(max(0, soft[k] - hard[k])), sum(k in 1..2)(max(0, hard[k] - soft[k])));
constraint cost[2] >= 1 /\ x[1] != 3;
solve satisfy;
