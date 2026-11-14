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
                        array1d(ok))
  % the weighted sum again as a linear constraint: the relaxation and the conflict analysis of
  % lazy clause generation use it as a row of the model (10x faster proofs on ccks)
  /\ sum(s in index_set(b))(prob[s] * bool2int(ok[s])) >= alpha;

/** The expectation of a sum with random coefficients, scaled by the common denominator den:
  z = den * E[sum(i)(W[i] * x[i])] = sum(i)(mean_num[i] * x[i]), where mean_num[i] is den times the
  mean of W[i]. By linearity of expectation it is a linear equation. */
predicate jacop_expected_sum(array[int] of var int: x, array[int] of int: mean_num, int: den,
                             var int: z) =
  assert(length(x) = length(mean_num) /\ den > 0,
         "jacop_expected_sum: x and mean_num must have the same length and den must be positive") /\
  let { array[int] of var int: y = array1d(x); array[int] of int: m = array1d(mean_num) } in
  z = sum(i in index_set(y))(m[i] * y[i]);

% The native constraint: item i has the random weight that takes value[(i - 1) * k + j] with
% probability prob[(i - 1) * k + j] / den, for j in 1..k (a probability of 0 pads a row).
predicate jacop_chance_sum(array[int] of var int: x, array[int] of int: value,
                           array[int] of int: prob, int: k, int: den, var int: c, int: alpha);

/** The chance constraint over independent random weights: Pr(sum(i)(W[i] * x[i]) <= c) >= alpha /
  den, where W[i] takes the value value[i, j] with probability prob[i, j] / den and the W[i] are
  independent. The x[i] and the values must be at least 0. Unlike scenario_chance it never lists
  the joint scenarios, whose number is the product of the support sizes. */
predicate chance_sum(array[int] of var int: x, array[int, int] of int: value,
                     array[int, int] of int: prob, int: den, var int: c, int: alpha) =
  assert(index_set_1of2(value) = index_set_1of2(prob)
         /\ index_set_2of2(value) = index_set_2of2(prob)
         /\ card(index_set_1of2(value)) = length(x),
         "chance_sum: value and prob must have one row per variable and the same columns") /\
  assert(den > 0 /\ forall(i in index_set_1of2(prob))(
           forall(j in index_set_2of2(prob))(prob[i, j] >= 0 /\ value[i, j] >= 0)
           /\ sum(j in index_set_2of2(prob))(prob[i, j]) = den),
         "chance_sum: each row of prob must be numerators from 0 over den summing to den, the values at least 0") /\
  assert(forall(i in index_set(x))(lb(x[i]) >= 0), "chance_sum: the variables must be at least 0") /\
  jacop_chance_sum(array1d(x), array1d(value), array1d(prob), card(index_set_2of2(value)), den,
                   c, alpha);

% The native constraint: the arguments of chance_table, with x as a one-dimensional array.
predicate jacop_chance_table(array[int] of var int: x, array[int] of int: scope_len,
                             array[int] of int: scope, array[int] of int: rows,
                             array[int] of int: tuples, array[int] of int: scen_len,
                             array[int] of int: scen_tables, array[int] of int: prob,
                             var int: p);

/** The chance constraint over scenario tables: p = sum(s)(prob[s] * [x satisfies scenario s]).
  Table t has the scope_len[t] variables of x at the positions (from 1) listed next in scope and
  the rows[t] tuples listed next in tuples, row by row. Scenario s holds when x is a tuple of each
  of the scen_len[s] tables listed next in scen_tables (from 1), and has the weight prob[s], a
  probability numerator. Maximising p gives the most probable decision of a one-stage stochastic
  CSP; p >= alpha is the chance constraint. A table shared by scenarios is listed once. */
predicate chance_table(array[int] of var int: x, array[int] of int: scope_len,
                       array[int] of int: scope, array[int] of int: rows,
                       array[int] of int: tuples, array[int] of int: scen_len,
                       array[int] of int: scen_tables, array[int] of int: prob, var int: p) =
  assert(length(scope_len) = length(rows) /\ sum(scope_len) = length(scope)
         /\ sum(t in index_set(rows))(scope_len[t] * rows[t]) = length(tuples)
         /\ length(scen_len) = length(prob) /\ sum(scen_len) = length(scen_tables),
         "chance_table: the lengths of the arrays do not match") /\
  assert(forall(i in index_set(scope))(scope[i] >= 1 /\ scope[i] <= length(x))
         /\ forall(i in index_set(scen_tables))(scen_tables[i] >= 1
                                                /\ scen_tables[i] <= length(rows))
         /\ forall(s in index_set(prob))(prob[s] >= 0),
         "chance_table: a position, a table index or a weight is out of range") /\
  jacop_chance_table(array1d(x), array1d(scope_len), array1d(scope), array1d(rows),
                     array1d(tuples), array1d(scen_len), array1d(scen_tables), array1d(prob), p);

% The native constraint: the arguments of prob_mdd, with x as a one-dimensional array.
predicate jacop_prob_mdd(array[int] of var int: x, array[int] of int: level_var,
                         array[int] of int: level_den, array[int] of int: level_size,
                         array[int] of int: node_edges, array[int] of int: edge_label,
                         array[int] of int: edge_to, int: scale, var int: p);

/** The probability that a layered decision diagram reaches its true sink: p = floor(scale * Pr).
  Level l is a decision level of the variable x[level_var[l]] (a position from 1), or a chance
  level when level_var[l] = 0, whose edges carry probability numerators over level_den[l]. Level l
  has level_size[l] nodes (the first one node, the root); the nodes, level by level, have
  node_edges[n] edges each, and the edges, node by node, a label (a value of the level's variable,
  or a probability numerator) and a target edge_to, the position from 1 of a node of the next level,
  or 0 for the true sink, which only the last level reaches. A missing edge leads to the false
  sink. Each variable labels at most one level. */
predicate prob_mdd(array[int] of var int: x, array[int] of int: level_var,
                   array[int] of int: level_den, array[int] of int: level_size,
                   array[int] of int: node_edges, array[int] of int: edge_label,
                   array[int] of int: edge_to, int: scale, var int: p) =
  assert(length(level_var) = length(level_den) /\ length(level_var) = length(level_size)
         /\ sum(level_size) = length(node_edges) /\ sum(node_edges) = length(edge_label)
         /\ length(edge_label) = length(edge_to),
         "prob_mdd: the lengths of the arrays do not match") /\
  assert(forall(l in index_set(level_var))(level_var[l] >= 0 /\ level_var[l] <= length(x)),
         "prob_mdd: a level variable is out of range") /\
  jacop_prob_mdd(array1d(x), array1d(level_var), array1d(level_den), array1d(level_size),
                 array1d(node_edges), array1d(edge_label), array1d(edge_to), scale, p);
