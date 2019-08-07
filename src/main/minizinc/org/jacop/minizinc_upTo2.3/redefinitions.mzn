% This file contains redefinitions of standard builtins that can be overridden
% by solvers.

predicate float_sinh(var float: x, var float: y) =
    y = (exp(x)-exp(-x))/2.0;

predicate float_cosh(var float: x, var float: y) =
    y = (exp(x)+exp(-x))/2.0;

predicate float_tanh(var float: x, var float: y) =
    let {
      var float: e2x = exp(2.0*x),
    } in
    y = (e2x - 1.0)/(e2x + 1.0);
