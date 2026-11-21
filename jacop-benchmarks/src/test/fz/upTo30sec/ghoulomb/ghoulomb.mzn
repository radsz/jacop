%------------------------------------------------------------------------%
% Ghoulomb
%------------------------------------------------------------------------%
%
% This is based on the classic Golomb ruler problem, with a few twists to make
% it more evil:
%  * Three Golomb rulers are constructed sequentially in the search, but 
%    only the middle one is minimized. This makes the search contain many 
%    redundant parts.  
%  * It uses the cumulative scheduling constraint instead of all_different. 
%    This simulates a modeler that does not know the idiomatic constraint to 
%    use in this instance.
%  * Instead of a resource with capacity 1 and tasks that use capacity 1,
%    the capacity is set to use more than half
%    of the possible maximum capacity (so it is again a disjunctive problem).
%
%------------------------------------------------------------------------%

include "globals.mzn";

%%%%%%%%% Input

int: m1;
int: m2;
int: m3;


%%%%%%%%% Predicates

% Equivalent to all_different(x)
predicate distinct(array[int] of var int: x) =    
    let {
        array[1..length(x)] of var 1..1: d,
        array[1..length(x)] of var 11..11: r,
        var 15..15: c
    } in
        cumulative(x, d, r, c);

% mark is a golomb ruler with difference-variables differences
predicate ghoulomb(array[int] of var int: mark,
	           array[int] of var int: differences) =
    let {
        int: m = length(mark),
	% Difference variables are not defined inside the predicate 
	% due to bug 133.
        %    array[1..(m*(m-1)) div 2] of var 0..m*m: differences =
        %        [ mark[j]-mark[i] | i in 1..m, j in i+1..m ]
	% instead the array is declared outside and passed to the predicate
    } in (
        mark[1] = 0
    /\  forall ( i in 1..m-1) ( mark[i] < mark[i+1] )
    /\  distinct(differences) :: bounds
        % Symmetry breaking
    /\  differences[1] < differences[(m*(m-1)) div 2]
    );


%%%%%%%%% Model

%  Golomb ruler 1
array[1..m1] of var 0..m1*m1: mark1;
array[1..(m1*(m1-1)) div 2] of var 0..m1*m1: differences1 =
            [ mark1[j]-mark1[i] | i in 1..m1, j in i+1..m1 ];
constraint ghoulomb(mark1, differences1);

%  Golomb ruler 2
array[1..m2] of var 0..m2*m2: mark2;
array[1..(m2*(m2-1)) div 2] of var 0..m2*m2: differences2 =
            [ mark2[j]-mark2[i] | i in 1..m2, j in i+1..m2 ];
constraint ghoulomb(mark2, differences2);

%  Golomb ruler 3
array[1..m3] of var 0..m3*m3: mark3;
array[1..(m3*(m3-1)) div 2] of var 0..m3*m3: differences3 =
            [ mark3[j]-mark3[i] | i in 1..m3, j in i+1..m3 ];
constraint ghoulomb(mark3, differences3);

var 0..m2*m2: objective = mark2[m2];

solve :: int_search(mark1 ++ mark2 ++ mark3, input_order, indomain_min, complete)
    minimize objective;

output [
    "mark1 = ", show(mark1), "\n",
    "mark2 = ", show(mark2), "\n",
    "mark3 = ", show(mark3), "\n",
    "objective = ", show(objective), "\n"
];
