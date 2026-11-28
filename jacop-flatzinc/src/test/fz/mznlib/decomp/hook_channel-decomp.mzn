% channel(x, b): x in index_set(b) and x = i <-> b[i].
predicate channel(var int: x, array[int] of var bool: b) =
  x in index_set(b) /\ forall(i in index_set(b))(b[i] <-> x = i);
var 2..6: x;
array[1..5] of var bool: b;
var {1, 3, 5}: y;
array[1..5] of var bool: c;
var 1..3: z;
array[1..4] of var bool: d;
var 0..6: w;
array[1..4] of var bool: e;
constraint channel(x, b);
constraint channel(y, c);
constraint channel(z, d);
constraint channel(w, e);
solve satisfy;
