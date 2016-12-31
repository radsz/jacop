%------------------------------------------------------------------------------%
% 2DLevelPacking.mzn
% Jakob Puchinger
% October 29 2007
% vim: ft=zinc ts=4 sw=4 et tw=0
%------------------------------------------------------------------------------%

    % Width of the Bin
int: W;
    % Height of the Bin
int: H;
    % Number of items to be packed
int: N;
    % Widths of the items
array[1..N] of int: ItemWidth;
    % Heights of the items
array[1..N] of int: ItemHeight;

array [1..N, 1..N] of var int: x;
array [1..N, 1..N] of var int: z;

solve minimize sum( k in 1..N ) (z[k, k] );

constraint
        % Each item has to be assigned to a level.
    forall( j in 1..N ) (
        sum( i in 1..j) ( x[i, j] ) = 1
    );

constraint
    forall ( i in 1..N ) (
                % Width of items on level can not exceed W
            sum( j in i..N ) ( ItemWidth[j] * x[i, j] ) <= W * x[i, i]
    );

    % Each level has to be assigned to a bin.
constraint
    forall ( i in 1..N ) (
        sum ( k in 1..i) ( z[k, i] ) = x[i, i]
    );

constraint
    forall ( k in 1..N ) (
            % Height of levels on bin can not exceed H
        sum( i in k..N ) ( ItemHeight[i] * z[k, i] ) <= z[k, k] * H 
);

constraint
    forall ( i in 1..N ) (
            forall( j in 1..N ) ( x[i,j] >= 0 /\ z[i,j] >= 0 ) /\
                % XXX do not need to generate those variables (use default)
            forall( j in 1..i-1 ) ( x[i, j] = 0 /\ z[i, j] = 0) 
        );

output
["Objective = "] ++ [show(sum( k in 1..N ) (z[k, k] ))] ++ ["\n"];
