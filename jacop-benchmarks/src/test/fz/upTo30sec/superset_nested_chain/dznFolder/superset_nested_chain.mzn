% A descending chain of sets s[1] superset s[2] superset ... with weight and size limits.
int: n = 6;
int: m = 16;
array[1..m] of int: w = [5,3,8,2,7,4,6,1,9,3,5,2,6,4,7,8];
array[1..m] of int: profit = [4,6,3,8,5,2,7,9,1,6,3,8,4,5,2,6];
array[1..n] of var set of 1..m: s;
constraint forall(i in 1..n-1)(s[i] superset s[i+1]);
constraint forall(i in 1..n)(sum(e in 1..m)(bool2int(e in s[i]) * w[e]) <= 8 * (n + 1 - i));
constraint forall(i in 1..n-1)(card(s[i]) >= card(s[i+1]) + 1);
var int: obj = sum(i in 1..n, e in 1..m)(bool2int(e in s[i]) * profit[e]);
solve maximize obj;
output ["s = \(s);\nobj = \(obj);\n"];
