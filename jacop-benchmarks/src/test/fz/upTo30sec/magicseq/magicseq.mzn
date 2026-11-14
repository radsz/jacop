% magicseq.mzn
% vim: ft=zinc ts=4 sw=4 et tw=0
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Mon Oct 29 13:19:57 EST 2007
%
% A magic sequence of non-negative integers [X0, X1, X2, ..., Xn] has the
% property that forall (i in 1..n) (Xi = card({Xj | j in 1..n, Xj = i})).  That
% is, each Xi is the number of occurrences of i in the sequence.

include "globals.mzn";

int: n;                                       % The length of the sequence.

array [0..n - 1] of var 0..n: x; % The sequence.

constraint forall (i in 0..n - 1) (count(x, i, x[i]));

solve satisfy;

output [show(x)];
