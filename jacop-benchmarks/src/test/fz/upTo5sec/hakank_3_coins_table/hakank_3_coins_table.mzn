% Cross-checked regression test, from Hakan Kjellerstrand's 3_coins.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the moves expressed as a table constraint on Booleans.
% 3 coins problem in MiniZinc, with the moves as a Boolean table.
%
% Three coins lie on a table in the order tails, heads ,tails. In precisely three moves
% make them face either all heads or all tails.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@bonetmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 3;
int: num_moves = 3; % first row is the init move
array[1..num_moves+1,1..n] of var bool: x; % false: head, true: tail
array[1..n] of bool: init = [true,false,true];
var 0..n: last_sum;

function bool: bit(int: v, int: i) = (v div pow(2, i - 1)) mod 2 = 1;

% one row per position v of the coins and coin f flipped by the move
array[1..8*n, 1..2*n] of bool: move = array2d(1..8*n, 1..2*n, [
  if k <= n then bit(v, k) else bit(v, k - n) xor (k - n = f) endif
  | v in 0..7, f in 1..n, k in 1..2*n ]);

solve satisfy;

constraint
    forall(i in 1..n) (x[1,i] = init[i])
    /\
    forall(m in 2..num_moves+1) (
       table([x[m-1,i] | i in 1..n] ++ [x[m,i] | i in 1..n], move)
    )
    /\
    last_sum = sum(i in 1..n) (bool2int(x[num_moves+1,i]))
    /\
    (last_sum = 0 \/ last_sum = n)
;

output[
  if j = 1 then "\n" else " " endif ++ show(bool2int(x[m,j]))
  | m in 1..num_moves+1, j in 1..n
] ++ ["\n"];
