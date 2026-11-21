% channel(x, b) means x = i <-> b[i], also when dom(x) is not index_set(b): a shifted domain,
% a domain with holes, a domain smaller and a domain larger than the index set.
include "channel.mzn";
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
