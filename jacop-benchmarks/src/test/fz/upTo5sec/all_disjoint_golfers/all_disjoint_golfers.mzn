% Social golfers with a resting golfer: 2 groups of 2 out of 5 golfers in 3 rounds, no pair
% plays together twice. Every solution is printed (all_disjoint over set variables).
include "globals.mzn";

int: n_groups = 2;
int: n_per_group = 2;
int: n_rounds = 3;
int: n_golfers = 5;

set of int: groups = 1..n_groups;
set of int: rounds = 1..n_rounds;
set of int: golfers = 1..n_golfers;

array [rounds, groups] of var set of golfers: x;

constraint forall (r in rounds, g in groups) (card(x[r, g]) = n_per_group);
constraint forall (r in rounds) (all_disjoint (g in groups) (x[r, g]));
constraint forall (a, b in golfers where a < b) (
    sum (r in rounds, g in groups) (bool2int({a, b} subset x[r, g])) <= 1);
% the first group of a round holds the smallest golfer playing in that round
constraint forall (r in rounds) (min(x[r, 1]) < min(x[r, 2]));

solve satisfy;
