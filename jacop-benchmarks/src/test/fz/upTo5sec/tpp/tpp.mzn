% Model written for the 2012 MiniZinc competition.
%
% Asymmetric travelling purchaser problem.
%
% A grid-based travelling purchaser problem. The goal is to decide where to buy
% each of a set of products, and in which order to visit the purchase
% locations, so as to minimize the total travel and purchase costs (products
% are available at every city for different prices). Travel costs are
% asymmetric, and cities are laid out on a grid with travel only allowed
% between horizontally and vertically adjacent cities.
%
% Author: Kathryn Francis

include "subcircuit.mzn";

int: numproducts;
int: numcities;
int: maxprice;
int: maxdist;

% travel distances (-1 means no travel allowed)
array[1..numcities,1..numcities] of int: dist; 
% product purchase prices at each city (last city has nothing for sale)
array[1..numcities-1,1..numproducts] of int: price; 

% successor variables
array[1..numcities] of var 1..numcities: succ;
% travel costs
array[1..numcities] of var 0..maxdist: travelCost;
% purchase locations
array[1..numproducts] of var 1..numcities-1: purchaseLoc;
% purchase costs
array[1..numproducts] of var 0..maxprice: purchaseCost;
% total cost (to be minimized)
int: totalCost_min = lb(sum(travelCost) + sum(purchaseCost));
int: totalCost_max = ub(sum(travelCost) + sum(purchaseCost));
var totalCost_min..totalCost_max: objective;

constraint objective = sum(travelCost) + sum(purchaseCost);

% travel cost depends on successor
% travel cost has domain >= 0 so dist for chosen successor cannot be negative
constraint forall (city in 1..numcities) (
  travelCost[city] = dist[city,succ[city]]
);

% purchase price depends on chosen purchase city
constraint forall (product in 1..numproducts) (
  purchaseCost[product] = price[purchaseLoc[product], product]
);

% purchasing a product at a city is only possible if you visit that city
constraint forall (product in 1..numproducts) (
  succ[purchaseLoc[product]] != purchaseLoc[product]
);

% successors must form a subcircuit
constraint subcircuit(succ);

% last city must be visited (we start here)
constraint succ[numcities] != numcities;


solve :: seq_search([
     int_search(succ, input_order, indomain_min, complete),
     int_search(purchaseLoc, input_order, indomain_min, complete) 
   ]) minimize objective;

output 
[
    "succ = \(succ);\n",
    "purchaseLoc = \(purchaseLoc);\n",
    "objective = \(objective);"
];
