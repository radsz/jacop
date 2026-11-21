% atanh goes through JaCoP's redefinition of float_atanh; x = i/4 is not known at compile time.
var 1..3: i;
var float: x = int2float(i) / 4.0;
var float: f;
constraint f = atanh(x);
solve satisfy;
output ["i=\(i) f=\(f)\n"];
