include "globals.mzn";

int: Q = 1;
int: S = 2;
int: Fstart = 3;
int: Fend = 4;
int: Dstart = 5;

int: width;
int: height;
int: filled;
int: ntiles;
int: size;
array[1..ntiles,1..Dstart] of int: tiles;
array[1..size] of int: dfa;

array[1..width*height] of var filled..ntiles+1: board;

constraint forall (h in 1..height, w in 1..width-1) (
    board[(h-1)*width+w] != ntiles+1);

constraint forall (h in 1..height) (
    board[(h-1)*width+width] = ntiles+1);

constraint
  forall (t in 1..ntiles)(
    let {
      int: q = tiles[t,Q],
      int: s = tiles[t,S],
      set of int: f = tiles[t,Fstart]..tiles[t,Fend],
      array[1..q,1..s] of int: d =
        array2d(1..q,1..s,
                [ dfa[i] | i in tiles[t,Dstart]+1..tiles[t,Dstart]+q*s] )
    }
    in
      regular(board,q,s,d,1,f)
  );

solve :: int_search(board, input_order, indomain_min, complete) satisfy;

output [show(board)];
