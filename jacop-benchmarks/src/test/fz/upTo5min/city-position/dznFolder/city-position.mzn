%
% Determine city positions using distance.
% (like MDS plotting but allows missing values)
%

% enable / disable symmetry constraint
% predicate symmetry_breaking_constraint(bool: c) = c;

% number of cities
int: N;

array[1..N] of string: name;

% size of distance data
int: R;

% distance data
array[1..R] of int: from;
array[1..R] of int: to;
array[1..R] of int: distance;


array[1..N] of var 0..max(distance): x;
array[1..N] of var 0..max(distance): y;

constraint symmetry_breaking_constraint(
  % Hokkaido 
  y[N-2] = max (i in 1..N) (y[i])
  % Chiba
  /\ x[N-1] * 2 > (x[N-2] + x[N])
  % Okinawa
  /\ x[N] = 0 /\ y[N] = 0
);

% http://www.flipcode.com/archives/Fast_Approximate_Distance_Functions.shtml
function var int: approx_distance(var int: x1, var int: y1, var int: x2, var int: y2) = (
    let {
        var int: dx = abs(x1 - x2),
        var int: dy = abs(y1 - y2),
        var int: maxd = max(dx, dy),
        var int: mind = min(dx, dy)
    } in ((1007 * maxd) + (441 * mind))
);

% penalty
int: ub_objective = sum(i in 1..R)(
    let {
        int: max1 = distance[i] * 1024 - (1007 + 441) * max(distance),
        int: max2 = distance[i] * 1024
    } in max( abs(max1), abs(max2) )
);
var 0..ub_objective: objective;

constraint objective = sum(i in 1..R) (
    let {
      var int: d = distance[i] * 1024 - approx_distance(x[from[i]], y[from[i]], x[to[i]], y[to[i]])
    } in abs(d)
);

solve :: seq_search([
           int_search(x, first_fail, indomain_min, complete),
           int_search(y, first_fail, indomain_min, complete)
         ])
         minimize objective;

output [
    % "name = \(name);\n",
    "x = \(x);\n",
    "y = \(y);\n",
    "objective = \(objective);\n",
];

