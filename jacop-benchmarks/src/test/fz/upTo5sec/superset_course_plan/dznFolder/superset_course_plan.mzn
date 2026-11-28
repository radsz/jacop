% Plan courses over semesters; before taking a course all prerequisites must already be done.
int: nc = 14;
int: nsem = 6;
array[1..nc] of set of 1..nc: pre = [
  {}, {}, {1}, {1,2}, {2}, {3}, {3,4}, {5}, {6,7}, {8},
  {4,5}, {9}, {10,11}, {12,13}];
array[1..nc] of int: credits = [3,3,4,4,3,4,5,3,4,3,4,5,4,6];
int: maxload = 12;
array[1..nsem] of var set of 1..nc: take;
array[0..nsem] of var set of 1..nc: done;
constraint done[0] = {};
constraint forall(s in 1..nsem)(done[s] = done[s-1] union take[s]);
constraint forall(s in 1..nsem)(take[s] intersect done[s-1] = {});
constraint forall(s in 1..nsem, c in 1..nc)(c in take[s] -> done[s-1] superset pre[c]);
constraint forall(s in 1..nsem)(sum(c in 1..nc)(bool2int(c in take[s]) * credits[c]) <= maxload);
constraint done[nsem] superset 1..nc;
solve :: seq_search([set_search(take, input_order, indomain_min, complete)]) satisfy;
output ["take = \(take);\n"];
