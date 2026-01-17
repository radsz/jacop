%
% Model for an adder built of transistors
%

var bool: a;
var bool: b;
var bool: c;
var bool: nca;
var bool: summa;
var bool: carry;

array[0..5] of var bool: t;
array[0..3] of var bool: q;

predicate ntran(var bool: b, var bool: x, var bool: y) =
	  b  -> x = y
;

predicate ptran(var bool: b, var bool: x, var bool: y) =
	  not b  -> x = y
;

constraint  % summa part
		ptran(nca, t[0], true) /\
		ptran(c, true, t[4]) /\
		ptran(b, t[0], t[4]) /\
		ptran(a, t[0], t[1]) /\
		ptran(nca, t[4], t[1]) /\
		ptran(t[1], true, summa) /\
		ntran(a, t[1], t[2]) /\
		ntran(nca, t[1], t[5]) /\
		ntran(t[1], summa, false) /\
		ntran(b, t[2], t[5]) /\
		ntran(nca, t[2], false) /\
		ntran(c, t[5], false)
;

constraint   % carry part
		ptran(a, q[0], true) /\
		ptran(b, q[0], true) /\
		ptran(a, q[1], true) /\
		ptran(c, q[0], nca) /\
		ptran(b, q[1], nca) /\
		ptran(nca, true, carry) /\
		ntran(c, nca, q[2]) /\
		ntran(b, nca, q[3]) /\
		ntran(nca, carry, false) /\
		ntran(a, q[2], false) /\
		ntran(b, q[2], false) /\
		ntran(a, q[3], false)
;

solve :: bool_search( [a] ++ [b] ++ [c] ++ [summa] ++ [carry], input_order, indomain_min, complete) satisfy;
%solve satisfy;

output [
   show( a ),
   show( b ),
   show( c ),
   show( summa ),
   show( carry )
];
