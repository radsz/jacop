include "channel.mzn";
var 1..5: x; var 0..6: y;
array[1..5] of var bool: b;
array[0..6] of var bool: c;
constraint channel(x, b);
constraint channel(y, c, 0..6);
constraint y != x;
constraint bool2int(b[2]) + bool2int(c[3]) + bool2int(c[0]) <= 1;
solve satisfy;
