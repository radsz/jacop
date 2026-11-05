% JaCoP probabilistic constraints (org.jacop.prob). A probability is an integer numerator over a
% denominator den that the model chooses, so the solver compares probabilities exactly.

% The native constraint, with the coefficients of the scenarios flattened row by row and the
% indicator ok[s] of each scenario: ok[s] holds exactly when scenario s does. The indicators give
% the linear relaxation its rows and lazy clause generation literals to learn on; with ok = []
% the constraint has no indicators (no relaxation rows, fewer variables).
predicate jacop_scenario_chance(array[int] of var int: x, array[int] of int: a,
                                array[int] of int: b, array[int] of int: prob, int: den,
                                int: alpha, array[int] of var bool: ok);

/** The chance constraint over scenarios: the scenarios s for which
  sum(i)(a[s, i] * x[i]) <= b[s] holds have a total probability of at least alpha / den, where
  scenario s has probability prob[s] / den. It is Pr(a x <= b) >= alpha / den for a random row
  (a, b) of a finite distribution (the sample average approximation of a chance constraint). */
predicate scenario_chance(array[int] of var int: x, array[int, int] of int: a,
                          array[int] of int: b, array[int] of int: prob, int: den,
                          int: alpha) =
  assert(index_set_1of2(a) = index_set(b) /\ index_set(b) = index_set(prob)
         /\ card(index_set_2of2(a)) = length(x),
         "scenario_chance: a must have one row per scenario and one column per variable") /\
  assert(den > 0 /\ forall(s in index_set(prob))(prob[s] >= 0) /\ sum(prob) <= den,
         "scenario_chance: the probabilities must be numerators from 0 over den summing to at most den") /\
  let { array[index_set(b)] of var bool: ok } in
  jacop_scenario_chance(array1d(x), array1d(a), array1d(b), array1d(prob), den, alpha,
                        array1d(ok));

/** The expectation of a sum with random coefficients, scaled by the common denominator den:
  z = den * E[sum(i)(W[i] * x[i])] = sum(i)(mean_num[i] * x[i]), where mean_num[i] is den times the
  mean of W[i]. By linearity of expectation it is a linear equation. */
predicate jacop_expected_sum(array[int] of var int: x, array[int] of int: mean_num, int: den,
                             var int: z) =
  assert(length(x) = length(mean_num) /\ den > 0,
         "jacop_expected_sum: x and mean_num must have the same length and den must be positive") /\
  let { array[int] of var int: y = array1d(x); array[int] of int: m = array1d(mean_num) } in
  z = sum(i in index_set(y))(m[i] * y[i]);
