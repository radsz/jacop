include "channel.mzn";
var 2..6: x; var 1..4: y;
array[2..6] of var bool: b;
array[1..4] of var bool: c;
constraint channel(x, b, 2..6);
constraint channel(y, c);
constraint x >= 2 * y - 1;
solve satisfy;
