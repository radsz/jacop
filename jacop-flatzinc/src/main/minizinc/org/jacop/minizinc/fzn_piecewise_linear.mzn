% y = f(x) for the piecewise-linear function through the knots, posted as JaCoP's PiecewiseLinear
predicate jacop_piecewise_linear(var float: x, var float: y,
                                 array [int] of float: x_knot, array [int] of float: y_knot);

predicate fzn_piecewise_linear(var float: x, var float: y,
                               array [int] of float: x_knot, array [int] of float: y_knot) =
  assert(index_set(x_knot) == index_set(y_knot) /\ 0 < card(index_set(x_knot)),
         "fzn_pwl: index sets unequal or empty",
         jacop_piecewise_linear(x, y, x_knot, y_knot));
