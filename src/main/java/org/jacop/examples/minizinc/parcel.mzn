%
% Model for TSP with parcel distribution
%

include "jacop.mzn";

int : n = 10; % number of cities
array[1..n, 1..n] of int : distance = [| 1000, 85, 110, 94, 71, 76, 25, 56, 94, 67
				       | 85, 1000, 26, 70, 62, 60, 63, 62, 70, 49 
				       | 110, 26, 1000, 71, 87, 89, 88, 87, 93, 73 
				       | 94, 70, 71, 1000, 121, 19, 82, 106, 124, 105 
				       | 71, 62, 87, 121, 1000, 104, 53, 24, 8, 13 
				       | 76, 60, 89, 19, 104, 1000, 65, 89, 108, 93 
				       | 25, 63, 88, 82, 53, 65, 1000, 30, 57, 46 
				       | 56, 62, 87, 106, 24, 89, 30, 1000, 23, 20 
				       | 94, 70, 93, 124, 8, 108, 57, 23, 1000, 20 
				       | 67, 49, 73, 105, 13, 93, 46, 20, 20, 1000  
				       |];
array[1..n] of int : load_parcel = [ 0, 1, 5, -6, 4, 3, -5, 2, 1, -3 ];

int: maxLoad = 5;
int: minLoad = -6;

array[1..n] of var 1..n: cities;
array[1..n] of var 1..n: ordered_cities;
array[1..n] of var minLoad..maxLoad: loads;
array[1..n] of var 0..1000: costs;
var int: tour_length;

constraint
	circuit(cities)
	/\
	forall (i in 1..n) (
	   distance[ i, cities[i] ] = costs[i] 
	)	
	/\
	tour_length = sum (i in 1..n) (costs[i] )
;

constraint
	ordered_cities[1] = cities[1]
	/\
	forall (i in 1..n-1) (
	   cities[ ordered_cities[i] ] = ordered_cities[ i + 1 ]
	);

constraint
	forall (i in 1..n) (
	   load_parcel[ordered_cities[i]] = loads[i]
	   /\
	   sum (j in 1..i) (loads[j]) > 0
	   /\
	   sum (j in 1..i) (loads[j]) <= 15
	);

solve :: int_search( cities, input_order, indomain_min, complete) minimize tour_length;

output [
   show( cities ),
   show( tour_length )
];
