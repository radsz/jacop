%------------------------------------------------------------------------------%
% 2DPacking_no_colgen.mzn
% Jakob Puchinger
% July 2008
% vim: ft=zinc ts=4 sw=4 et tw=0
%
% Two-dimensional Bin Packing 
%
% n rectangular items with given height and width have to be packed into
% rectangular bins of size W x H
% It is assumed that the items are sorted according to non-increasing height.

    % Upper Bound on the number of Bins used
int: K;
set of int: Bins;
Bins = 1..K;
    % Number of items to be packed
int: N;
set of int: Items;
Items = 1..N;
    % Width of the Bin
int: W;
    % Height of the Bin
int: H;

% Set K
K = N;

    % Widths of the items
array[Items] of int: ItemWidth;
    % Heights of the items
array[Items] of int: ItemHeight;

    % variable indicating if bin k is used
array[Bins] of var 0..1: bin; 
    % variable indicating if item i is in bin k
array[Bins, Items] of var 0..1: item; 

    % The total number of bins has to be minimized
solve 
     minimize sum(k in Bins)(bin[k]); 

    % each item has to be packed
constraint
    forall( j in Items ) (
        sum(k in Bins)(item[k, j])  >= 1
    );

    % subproblem constraints
constraint
    forall(k in Bins)(
        is_feasible_packing(bin[k], [ item[k, j] | j in Items ])
    );

int: N2 = ( N * (N+1) ) div 2;
predicate is_feasible_packing(var 0..1: bin,
        array[1..N] of var 0..1: item) = (
    let{array[1..N2] of var 0..1: x } in (
        forall ( i in Items ) (
                % Width of items on level can not exceed W
            sum( j in i..N ) ( ItemWidth[j] * 
                x[ (i-1)*N - (i*(i-1)) div 2 + j ] )
                <= W * x[(i-1)*N - (i*(i-1)) div 2 + i]
            
        )
        /\    
            % Height of levels on bin can not exceed H
        sum( i in Items ) ( ItemHeight[i] * x[(i-1)*N - (i*(i-1)) div 2 + i] )
            <= bin * H 
        
        /\
            % for all items associate item on bin with item on level.
        forall(j in Items) (
                item[j] = 
                sum( i in 1..j ) ( x[ ((i-1)*N) - ((i*(i-1)) div 2) + j] )
        
        )
    )
);

output [
    "bin  = ", show(bin), "\n",
    "item = ", show(item), "\n"
];

