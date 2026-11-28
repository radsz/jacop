include "filter.model.mzn";

n = 11;

add = {5, 8, 9, 10, 11};
mul = {1, 2, 3, 4, 6, 7};
last = {8, 9, 11};

del_add = 1;
del_mul = 2;

number_add = 2;
number_mul = 3;

dependencies = [     {6},  % 1
	     	     {6},  % 2
	     	     {7},  % 3
	     	     {8},  % 4
	     	     {9},  % 5
	     	     {10}, % 6
	     	     {11}, % 7
		     {},   % 8
		     {},   % 9
	     	     {11}, % 10
	             {}    % 11
	             ];