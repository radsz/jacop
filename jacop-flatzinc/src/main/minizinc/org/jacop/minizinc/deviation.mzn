%-----------------------------------------------------------------------------%
% Defines JaCoP predicates deviation and spread (balancing constraints).
%
% deviation(x, s, d): sum(x) = s and d = sum(i in index_set(x))(abs(n * x[i] - s)),
%   n = length(x): n times the L1 distance of x to its mean s / n (Schaus et al., CP 2007).
% spread(x, s, d): sum(x) = s and d = sum(i in index_set(x))((n * x[i] - s)^2).
% The general forms take a and b: d = sum of abs(a * x[i] - b), or of (a * x[i] - b)^2.
%
% JaCoP also finds these constraints in models that write the sums of abs or squares with
% sum(x) = s, so the predicates are only needed to post them directly.
%-----------------------------------------------------------------------------%
predicate deviation(array[int] of var int: x, int: s, var int: d) =
          jacop_deviation(x, length(x), s, s, d);

predicate deviation(array[int] of var int: x, int: a, int: b, int: s, var int: d) =
          jacop_deviation(x, a, b, s, d);

predicate spread(array[int] of var int: x, int: s, var int: d) =
          jacop_spread(x, length(x), s, s, d);

predicate spread(array[int] of var int: x, int: a, int: b, int: s, var int: d) =
          jacop_spread(x, a, b, s, d);

predicate jacop_deviation(array[int] of var int: x, int: a, int: b, int: s, var int: d);

predicate jacop_spread(array[int] of var int: x, int: a, int: b, int: s, var int: d);
