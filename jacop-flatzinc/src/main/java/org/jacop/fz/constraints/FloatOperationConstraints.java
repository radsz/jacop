/*
 * FloatOperationConstraints.java This file is part of JaCoP.
 *
 * <p>JaCoP is a Java Constraint Programming solver.
 *
 * <p>Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 * <p>This program is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Affero General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * <p>This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * <p>Notwithstanding any other provision of this License, the copyright owners of this work
 * supplement the terms of this License with terms prohibiting misrepresentation of the origin of
 * this work and requiring that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license terms is in accordance with
 * Section 7 of GNU Affero General Public License version 3.
 *
 * <p>You should have received a copy of the GNU Affero General Public License along with this
 * program. If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.fz.constraints;

import org.jacop.constraints.And;
import org.jacop.constraints.IfThenElse;
import org.jacop.core.Store;
import org.jacop.floats.constraints.AbsPeqR;
import org.jacop.floats.constraints.AcosPeqR;
import org.jacop.floats.constraints.AsinPeqR;
import org.jacop.floats.constraints.AtanPeqR;
import org.jacop.floats.constraints.CeilPeqX;
import org.jacop.floats.constraints.CosPeqR;
import org.jacop.floats.constraints.ExpPeqR;
import org.jacop.floats.constraints.FloorPeqX;
import org.jacop.floats.constraints.HyperbolicPeqR;
import org.jacop.floats.constraints.LnPeqR;
import org.jacop.floats.constraints.Max;
import org.jacop.floats.constraints.Min;
import org.jacop.floats.constraints.PdivCeqR;
import org.jacop.floats.constraints.PdivQeqR;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PeqQ;
import org.jacop.floats.constraints.PgtC;
import org.jacop.floats.constraints.PgteqC;
import org.jacop.floats.constraints.PiecewiseLinear;
import org.jacop.floats.constraints.PmulCeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PowPeqR;
import org.jacop.floats.constraints.PplusCeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.RoundPeqX;
import org.jacop.floats.constraints.SinPeqR;
import org.jacop.floats.constraints.SqrtPeqR;
import org.jacop.floats.constraints.TanPeqR;
import org.jacop.floats.core.FloatVar;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Generation of set constraints in flatzinc.
 *
 * @author Krzysztof Kuchcinski
 */
class FloatOperationConstraints implements ParserTreeConstants {

  final Support support;
  final Store store;

  public FloatOperationConstraints(Support support) {
    this.support = support;
    this.store = support.store;
  }

  void gen_float_abs(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new AbsPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_acos(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new AcosPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_asin(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new AsinPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_atan(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new AtanPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_cos(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new CosPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_exp(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new ExpPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_ln(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new LnPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_log10(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    FloatVar tmp = new FloatVar(store, -1e150, 1e150);
    support.pose(new LnPeqR(support.getFloatVariable(p1), tmp));
    support.pose(new PdivCeqR(tmp, Math.log(10), support.getFloatVariable(p2)));
  }

  void gen_float_log2(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    FloatVar tmp = new FloatVar(store, -1e150, 1e150);
    support.pose(new LnPeqR(support.getFloatVariable(p1), tmp));
    support.pose(new PdivCeqR(tmp, Math.log(2), support.getFloatVariable(p2)));
  }

  /**
   * Posts f(x) = y for a hyperbolic function f, or x = f(y) for its inverse (asinh, acosh with y
   * &gt;= 0, atanh).
   */
  private void hyperbolic(SimpleNode node, HyperbolicPeqR.Function function, boolean inverse) {
    FloatVar x = support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    FloatVar y = support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    if (inverse) {
      if (function == HyperbolicPeqR.Function.COSH) {
        support.pose(new PgteqC(y, 0.0));
      }
      support.pose(new HyperbolicPeqR(y, function, x));
    } else {
      support.pose(new HyperbolicPeqR(x, function, y));
    }
  }

  void gen_jacop_piecewise_linear(SimpleNode node) {
    FloatVar x = support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    FloatVar y = support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    double[] xKnot = support.getFloatArray((SimpleNode) node.jjtGetChild(2));
    double[] yKnot = support.getFloatArray((SimpleNode) node.jjtGetChild(3));
    support.pose(new PiecewiseLinear(x, y, xKnot, yKnot));
  }

  void gen_float_sinh(SimpleNode node) {
    hyperbolic(node, HyperbolicPeqR.Function.SINH, false);
  }

  void gen_float_cosh(SimpleNode node) {
    hyperbolic(node, HyperbolicPeqR.Function.COSH, false);
  }

  void gen_float_tanh(SimpleNode node) {
    hyperbolic(node, HyperbolicPeqR.Function.TANH, false);
  }

  void gen_float_asinh(SimpleNode node) {
    hyperbolic(node, HyperbolicPeqR.Function.SINH, true);
  }

  void gen_float_acosh(SimpleNode node) {
    hyperbolic(node, HyperbolicPeqR.Function.COSH, true);
  }

  void gen_float_atanh(SimpleNode node) {
    hyperbolic(node, HyperbolicPeqR.Function.TANH, true);
  }

  void gen_float_sqrt(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new SqrtPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_sin(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new SinPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_tan(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new TanPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_float_max(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    FloatVar v1 = support.getFloatVariable(p1);
    FloatVar v2 = support.getFloatVariable(p2);
    FloatVar v3 = support.getFloatVariable(p3);

    support.pose(new Max(new FloatVar[] {v1, v2}, v3));
  }

  void gen_float_min(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    FloatVar v1 = support.getFloatVariable(p1);
    FloatVar v2 = support.getFloatVariable(p2);
    FloatVar v3 = support.getFloatVariable(p3);

    support.pose(new Min(new FloatVar[] {v1, v2}, v3));
  }

  void gen_float_plus(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    if (p1.getType() == 5) { // p1 int
      support.pose(
          new PplusCeqR(
              support.getFloatVariable(p2), support.getFloat(p1), support.getFloatVariable(p3)));
    } else if (p2.getType() == 5) { // p2 int
      support.pose(
          new PplusCeqR(
              support.getFloatVariable(p1), support.getFloat(p2), support.getFloatVariable(p3)));
    } else {
      support.pose(
          new PplusQeqR(
              support.getFloatVariable(p1),
              support.getFloatVariable(p2),
              support.getFloatVariable(p3)));
    }
  }

  void gen_float_times(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    if (p1.getType() == 5) { // p1 float
      support.pose(
          new PmulCeqR(
              support.getFloatVariable(p2), support.getFloat(p1), support.getFloatVariable(p3)));
    } else if (p2.getType() == 5) { // p2 float
      support.pose(
          new PmulCeqR(
              support.getFloatVariable(p1), support.getFloat(p2), support.getFloatVariable(p3)));
    } else {
      support.pose(
          new PmulQeqR(
              support.getFloatVariable(p1),
              support.getFloatVariable(p2),
              support.getFloatVariable(p3)));
    }
  }

  void gen_float_pow(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    FloatVar v1 = support.getFloatVariable(p1);
    FloatVar v2 = support.getFloatVariable(p2);
    FloatVar v3 = support.getFloatVariable(p3);

    // only a point is a constant exponent: a singleton interval is up to the precision wide, and
    // x^min differs from x^y for the other y in it by more than the precision
    if (v2.min() == v2.max()) {
      powConstantExponent(v1, v2.min(), v3);
      return;
    }

    if (v1.min() < 0) {
      System.err.println(
          "%% WARNING: constraint float_pow is not defined for negative numbers as first argument"
              + " and a variable exponent (decomposition x^y = exp(y*ln(x))); "
              + v1
              + " has minimal value negative (will be pruned).");
    }
    v1.domain.inMin(store.level, v1, 0.0);
    if (v1.min() > 0) {
      powByLogarithm(v1, v2, v3);
      return;
    }
    // 0^y is 1 for y = 0, 0 for y > 0 and undefined for y < 0; exp(y*ln(x)) holds for x > 0 only
    v3.domain.inMin(store.level, v3, 0.0);
    FloatVar base = positiveBaseOrOne(v1);
    FloatVar power = new FloatVar(store, 0.0, 1e150);
    powByLogarithm(base, v2, power);
    support.pose(
        new IfThenElse(
            new PgtC(v1, 0),
            new PeqQ(v3, power),
            new IfThenElse(
                new PeqC(v2, 0), new PeqC(v3, 1), new And(new PgtC(v2, 0), new PeqC(v3, 0)))));
  }

  /**
   * Poses x^c = z for a constant exponent c: a native power propagator (PowPeqR) keeps the sign of
   * the base and the hole around zero of an even power; x^-n is 1 / x^n.
   */
  private void powConstantExponent(FloatVar x, double c, FloatVar z) {
    if (c == 0) {
      // x^0 = 1 for every x, 0^0 included
      z.domain.in(store.level, z, 1.0, 1.0);
      return;
    }
    if (c > 0) {
      support.pose(new PowPeqR(x, c, z));
      return;
    }
    // x^-n = 1 / x^n, undefined for x = 0 (z * x^n = 1 has no solution with x^n = 0)
    FloatVar xn = new FloatVar(store, -1e150, 1e150);
    support.pose(new PowPeqR(x, -c, xn));
    support.pose(new PmulQeqR(z, xn, new FloatVar(store, 1.0, 1.0)));
  }

  /** Poses x^y = z as exp(y * ln(x)) = z, which needs x > 0. */
  private void powByLogarithm(FloatVar x, FloatVar y, FloatVar z) {
    FloatVar tmp1 = new FloatVar(store, -1e150, 1e150);
    FloatVar tmp2 = new FloatVar(store, -1e150, 1e150);
    support.pose(new LnPeqR(x, tmp1));
    support.pose(new PmulQeqR(tmp1, y, tmp2));
    support.pose(new ExpPeqR(tmp2, z));
  }

  /** A variable equal to x when x > 0 and to 1 when x = 0 (for x >= 0). */
  private FloatVar positiveBaseOrOne(FloatVar x) {
    FloatVar base = new FloatVar(store, Double.MIN_VALUE, Math.max(1.0, x.max()));
    support.pose(new IfThenElse(new PgtC(x, 0), new PeqQ(x, base), new PeqC(base, 1)));
    return base;
  }

  // not supported any longer
  void gen_float_div(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    support.pose(
        new PdivQeqR(
            support.getFloatVariable(p1),
            support.getFloatVariable(p2),
            support.getFloatVariable(p3)));
  }

  void gen_float_round(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new RoundPeqX(support.getFloatVariable(p1), support.getVariable(p2)));
  }

  void gen_float_floor(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new FloorPeqX(support.getFloatVariable(p1), support.getVariable(p2)));
  }

  void gen_float_ceil(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new CeilPeqX(support.getFloatVariable(p1), support.getVariable(p2)));
  }
}
