%
% Pentominoes model following the integer model described in 
% "Modeling Irregular Shape Placement Problems with Regular Constraints" 
% by Lagerkvist and Pesant.
%
% Model by Mikael Zayenz Lagerkvist
%
% Licensed under the MIT license (https://opensource.org/licenses/MIT)
%
% See https://github.com/zayenz/minizinc-pentominoes-generator for generator
%

include "globals.mzn";

int: size;
int: tiles;
array[int] of string: expressions;

int: marker = tiles+1;
set of int: Tiles = 1..tiles;
set of int: TilesAndMarker = Tiles union {marker};

array[1..size, 1..size] of var Tiles: board;
array[int] of var TilesAndMarker: board_and_markers = [
  if column <= size then board[row, column] else marker endif
  | row in 1..size, column in 1..size+1
];

constraint forall (expression in expressions) (
    regular(board_and_markers, expression)
);

solve :: int_search(board, input_order, indomain_min, complete) satisfy;

output [
   "board = \n", show2d(board), ";\n"
];
