% vim: ft=zinc ts=4 sw=4 et tw=0
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Wed Oct 24 15:35:20 EST 2007
%
% Find a cyclic knights tour of a given length on a chessboard, starting
% in one corner.

include "globals.mzn";

int: n;                                 % The board is n x n in size.
int: m;                                 % The length of the tour.

array [1..m] of var 1..n: r;  % The sequence of moves in the tour
array [1..m] of var 1..n: c;  % (row and column of each move).

    % Each move must be to a different square.
    %
constraint alldifferent([n * r[i] + c[i] | i in 1..m]);

    % Break some symmetries by forcing the first moves.
    %
constraint r[1] = 1;
constraint c[1] = 1;
constraint r[2] = 2;
constraint c[2] = 3;

    % There is only one place for the last move.
    %
constraint r[m] = 3;
constraint c[m] = 2;

    % Set up the possible routes.
    %
constraint
    forall (i in 1..(m - 1)) (
        exists (j in {-2, 2}, k in {-1, 1}) (
            ( r[i + 1] = r[i] + j  /\  c[i + 1] = c[i] + k )
        \/  ( r[i + 1] = r[i] + k  /\  c[i + 1] = c[i] + j )
        )
    );

solve satisfy;

output [
     "r = ", show(r), "\n",
     "c = ", show(c), "\n"
];
