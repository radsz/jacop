% This models a routing problem based on a little example of Mario's day. 
% Mario is an Italian Plumber and his work is mainly to find gold in the plumbing of all the houses of the neighborhood. 
% Mario is moving in the city using his kart that has a specified amount of fuel. Mario starts his day of work from his house 
% and always ends to his friend Luigi's house to have the supper. The problem here is to plan the best path for
% Mario in order to earn the more money with the amount of fuel of his kart ! 
% 
% From a more general point of view, the problem is to find a path in a graph:
% - Path endpoints are given (from Mario's to Luigi's)
% - The sum of weights associated to arcs in the path is restricted (fuel consumption)
% - The sum of weights associated to nodes in the path has to be maximized (gold coins)
% 
% authors: Amaury Ollagnier, Jean-Guillaume Fages
include "subcircuit.mzn";

	%%%%%%%%%%%%%%%
	% PARAMETERS  %
	%%%%%%%%%%%%%%%

int: nbHouses;
int: MarioHouse;
int: LuigiHouse;
int: fuelMax;
int: goldTotalAmount;
% fuel consumption between two houses
array[1..nbHouses,1..nbHouses] of int: conso; 
% gold coins Mario can get in each house
array[1..nbHouses] of int: goldInHouse; 

	%%%%%%%%%%%%%%%
	%  VARIABLES  %
	%%%%%%%%%%%%%%%

% successor variables
array[1..nbHouses] of var 1..nbHouses: succ;
% fuel that is consumed
var 0..fuelMax: fuel;
% earned gold coins
var 0..goldTotalAmount: objective;

	%%%%%%%%%%%%%%%
	% CONSTRAINTS %
	%%%%%%%%%%%%%%%

% Controls the amount of fuel that is consumed
constraint fuel = sum(i in 1..nbHouses) (conso[i,succ[i]]);

% Controls the amount of gold coins that is earned
constraint objective = sum(i in 1..nbHouses) (bool2int(succ[i]!=i)*goldInHouse[i]);

% The solution must form a path from Mario's house to Luigi's
constraint subcircuit(succ);
constraint succ[LuigiHouse] = MarioHouse;

	%%%%%%%%%%%%%%%
	% SEARCH AND  %
	%   OUTPUT    %
	%%%%%%%%%%%%%%%

solve 
	:: seq_search([
		int_search(succ, first_fail, indomain_min, complete),
		int_search([objective], input_order, indomain_max, complete)
	])
	maximize objective;

output [
    "%% Mario earned " ++ show(objective) ++ " gold coins with " ++ show(fuel) ++ "L of fuel\n" 
] ++ [
    "succ = ", show(succ), ";\n",
    "objective = ", show(objective), ";\n"
];

