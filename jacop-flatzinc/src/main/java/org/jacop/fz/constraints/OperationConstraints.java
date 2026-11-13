/*
 * OperationConstraints.java This file is part of JaCoP.
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

import java.util.Arrays;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.XdivYeqZ;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.XmulYeqC;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.floats.constraints.XeqP;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Generation of linear constraints in flatzinc.
 *
 * @author Krzysztof Kuchcinski
 */
class OperationConstraints implements ParserTreeConstants {

  final Support support;
  final Store store;

  public OperationConstraints(Support support) {
    this.support = support;
    this.store = support.store;
  }

  void gen_int_min(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    IntVar v3 = support.getVariable(p3);

    if (v1.singleton() && v2.singleton()) {
      int min = Math.min(v1.value(), v2.value());
      v3.domain.inValue(store.level, v3, min);
    } else if (v1.singleton() && v1.value() <= v2.min()) {
      int min = v1.value();
      v3.domain.inValue(store.level, v3, min);
    } else if (v2.singleton() && v2.value() <= v1.min()) {
      int min = v2.value();
      v3.domain.inValue(store.level, v3, min);
    } else if (v1.min() >= v2.max()) {
      support.pose(new XeqY(v2, v3));
    } else if (v2.min() >= v1.max()) {
      support.pose(new XeqY(v1, v3));
    } else if (v1 == v2) {
      support.pose(new XeqY(v1, v3));
    } else {
      support.pose(new MinSimple(v1, v2, v3));
    }
  }

  void gen_int_max(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    IntVar v3 = support.getVariable(p3);

    if (v1.singleton() && v2.singleton()) {
      int max = Math.max(v1.value(), v2.value());
      v3.domain.inValue(store.level, v3, max);
    } else if (v1.singleton() && v1.value() >= v2.max()) {
      int max = v1.value();
      v3.domain.inValue(store.level, v3, max);
    } else if (v2.singleton() && v2.value() >= v1.max()) {
      int max = v2.value();
      v3.domain.inValue(store.level, v3, max);
    } else if (v1.min() >= v2.max()) {
      support.pose(new XeqY(v1, v3));
    } else if (v2.min() >= v1.max()) {
      support.pose(new XeqY(v2, v3));
    } else if (v1 == v2) {
      support.pose(new XeqY(v1, v3));
    } else {
      support.pose(new MaxSimple(v1, v2, v3));
    }
  }

  void gen_int_mod(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    IntVar v3 = support.getVariable(p3);

    support.pose(new XmodYeqZ(v1, v2, v3));
  }

  void gen_int_div(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    IntVar v3 = support.getVariable(p3);

    support.pose(new XdivYeqZ(v1, v2, v3));
  }

  void gen_int_abs(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);

    if (support.boundsConsistency) {
      support.pose(new AbsXeqY(v1, v2));
    } else {
      support.pose(new AbsXeqY(v1, v2, true));
    }
  }

  void gen_int_times(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    if (p1.getType() == 0) {
      intTimesConstFirst(support.getInt(p1), p2, p3);
      return;
    }
    if (p2.getType() == 0) {
      intTimesConstSecond(p1, support.getInt(p2), p3);
      return;
    }
    if (p3.getType() == 0) {
      support.pose(
          new XmulYeqC(support.getVariable(p1), support.getVariable(p2), support.getInt(p3)));
      return;
    }
    intTimesAllVars(support.getVariable(p1), support.getVariable(p2), support.getVariable(p3));
  }

  private void intTimesConstFirst(int c, ASTScalarFlatExpr p2, ASTScalarFlatExpr p3) {
    if (c == 1) {
      support.pose(new XeqY(support.getVariable(p2), support.getVariable(p3)));
    } else if (c == 0) {
      IntVar v3 = support.getVariable(p3);
      v3.domain.inValue(store.level, v3, 0);
    } else {
      support.poseXmulCeqZ(support.getVariable(p2), c, support.getVariable(p3));
    }
  }

  private void intTimesConstSecond(ASTScalarFlatExpr p1, int c, ASTScalarFlatExpr p3) {
    if (c == 1) {
      support.pose(new XeqY(support.getVariable(p1), support.getVariable(p3)));
    } else if (c == 0) {
      IntVar v3 = support.getVariable(p3);
      v3.domain.inValue(store.level, v3, 0);
    } else {
      support.poseXmulCeqZ(support.getVariable(p1), c, support.getVariable(p3));
    }
  }

  private void intTimesAllVars(IntVar v1, IntVar v2, IntVar v3) {
    if (v1.min() >= 0
        && v1.max() <= 1
        && v2.min() >= 0
        && v2.max() <= 1
        && v3.min() >= 0
        && v3.max() <= 1) {
      if (v1.equals(v2)) {
        support.pose(new XeqY(v1, v3));
      } else {
        support.pose(new AndBoolSimple(v1, v2, v3));
      }
    } else if ((v1.singleton() && v1.value() == 0) || (v2.singleton() && v2.value() == 0)) {
      v3.domain.inValue(store.level, v3, 0);
    } else if (booleanProductsEnabled()
        && support.options.proof() == null
        && booleanProduct(v1, v2, v3)) {
      return;
    } else {
      if (PRODUCT_DOMAINS) {
        restrictToProducts(v1, v2, v3);
      }
      support.pose(new XmulYeqZ(v1, v2, v3));
    }
  }

  /**
   * Whether a product with a 0/1 factor is written as linear constraints, the system property
   * {@code org.jacop.fz.booleanProducts} (default false).
   */
  static boolean booleanProductsEnabled() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.booleanProducts", "false"));
  }

  /**
   * Posts z = x * b, with b a 0/1 variable and x not one, as
   *
   * <pre>
   *   b -&gt; z = x,   z &lt;= max(x) * b,   z &gt;= min(x) * b
   * </pre>
   *
   * instead of {@link XmulYeqZ}: for b = 0 the inequalities fix z to 0, for b = 1 the implication
   * makes z equal to x, so the solutions are those of the product. The constraints propagate both
   * ways (z != 0 sets b, z outside the domain of x clears it), have short reasons under lazy clause
   * generation, and the two inequalities are the rows of the linear relaxation of the product (F.
   * Glover, Improved linear integer programming formulations of nonlinear integer problems,
   * Management Science 22(4), 1975; G. P. McCormick, Computability of global solutions to
   * factorable nonconvex programs, Mathematical Programming 10, 1976), which sees no row for an
   * XmulYeqZ. It is the presolve rule {@code org.jacop.presolve.BooleanProducts} applied when the
   * constraint is posted, so that it does not need {@code --presolve}.
   *
   * @return false when neither factor alone is a 0/1 variable, or a factor is the result
   */
  private boolean booleanProduct(IntVar v1, IntVar v2, IntVar v3) {
    IntVar b;
    IntVar x;
    if (isZeroOne(v1) && !isZeroOne(v2)) {
      b = v1;
      x = v2;
    } else if (isZeroOne(v2) && !isZeroOne(v1)) {
      b = v2;
      x = v1;
    } else {
      return false;
    }
    if (b.singleton() || x == v3 || b == v3) {
      return false;
    }
    if (support.options.debug()) {
      System.out.println("% boolean product " + v3.id() + " = " + x.id() + " * " + b.id());
    }
    support.pose(new Implies(b, new XeqY(x, v3)));
    support.pose(
        new LinearInt(new IntVar[] {v3, b}, new int[] {1, -x.max()}, "<=", 0).setDegreeWeight(0));
    support.pose(
        new LinearInt(new IntVar[] {v3, b}, new int[] {1, -x.min()}, ">=", 0).setDegreeWeight(0));
    return true;
  }

  private static boolean isZeroOne(IntVar v) {
    return v.min() >= 0 && v.max() <= 1;
  }

  /** Whether int_times restricts its result to the products of the factors' domains. */
  private static final boolean PRODUCT_DOMAINS =
      Boolean.parseBoolean(System.getProperty("org.jacop.fz.productDomains", "true"));

  /** The most pairs of factor values {@link #restrictToProducts} enumerates. */
  private static final int PRODUCT_PAIRS = 1 << 12;

  /**
   * Restricts z in x * y = z to the products of the values of x and y when there are at most {@link
   * #PRODUCT_PAIRS} pairs. XmulYeqZ keeps bounds only, so a product of small domains spans an
   * interval full of values it cannot take; under LCG every bound it reaches is a literal. The
   * Molnar models (determinants of matrices of squares, 2..8) multiply chains of three factors:
   * restricted, the last product of each chain has at most 128 values instead of 262,081, its bound
   * literals 20,380 -> 2,198 in 60 s, and Molnar-3-8 is UNSAT in 29 s instead of 76 s. Each product
   * restricted this way also restricts the products built on it, as the flattener writes a chain
   * factor by factor.
   */
  private void restrictToProducts(IntVar x, IntVar y, IntVar z) {
    if (x == z || y == z || (long) x.getSize() * y.getSize() > PRODUCT_PAIRS) {
      return;
    }
    long[] products = new long[x.getSize() * y.getSize()];
    int count = 0;
    for (ValueEnumeration a = x.dom().valueEnumeration(); a.hasMoreElements(); ) {
      int u = a.nextElement();
      if (x == y) {
        products[count++] = (long) u * u;
        continue;
      }
      for (ValueEnumeration b = y.dom().valueEnumeration(); b.hasMoreElements(); ) {
        products[count++] = (long) u * b.nextElement();
      }
    }
    Arrays.sort(products, 0, count);
    IntervalDomain values = new IntervalDomain();
    for (int k = 0; k < count; k++) {
      long p = products[k];
      if ((k == 0 || p != products[k - 1]) && p >= IntDomain.MIN_INT && p <= IntDomain.MAX_INT) {
        values.unionAdapt((int) p, (int) p);
      }
    }
    z.domain.in(store.level, z, values);
  }

  void gen_int_plus(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    if (p1.getType() == 0) { // p1 int
      support.pose(
          new XplusCeqZ(support.getVariable(p2), support.getInt(p1), support.getVariable(p3)));
    } else if (p2.getType() == 0) { // p2 int
      support.pose(
          new XplusCeqZ(support.getVariable(p1), support.getInt(p2), support.getVariable(p3)));
    } else if (p3.getType() == 0) { // p3 int
      support.pose(
          new XplusYeqC(support.getVariable(p1), support.getVariable(p2), support.getInt(p3)));
    } else {
      support.pose(
          new XplusYeqZ(support.getVariable(p1), support.getVariable(p2), support.getVariable(p3)));
    }
  }

  void gen_int2float(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    support.pose(new XeqP(support.getVariable(p1), support.getFloatVariable(p2)));
  }

  void gen_int_pow(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    IntVar v3 = support.getVariable(p3);

    support.pose(new XexpYeqZ(v1, v2, v3));
  }
}
