% Laminar family: every two sets are either disjoint or one is a superset of the other.
int: n = 5;
int: m = 10;
array[1..n] of int: size = [7,4,3,2,2];
array[1..m] of int: w = [3,1,4,1,5,9,2,6,5,3];
array[1..n] of var set of 1..m: s;
constraint forall(i in 1..n)(card(s[i]) = size[i]);
constraint forall(i, j in 1..n where i < j)(
  s[i] superset s[j] \/ s[j] superset s[i] \/ s[i] intersect s[j] = {});
constraint forall(i in 1..n-1 where size[i] = size[i+1])(s[i] <= s[i+1]);
array[1..n] of var bool: top;
constraint forall(j in 1..n)(top[j] <-> forall(i in 1..n where i != j)(not (s[i] superset s[j] /\ size[i] > size[j])));
var int: obj = sum(i in 1..n, e in 1..m)(bool2int(e in s[i]) * w[e]) + 5 * sum(j in 1..n)(bool2int(top[j]));
solve maximize obj;
output ["s = \(s);\ntop = \(top);\nobj = \(obj);\n"];
