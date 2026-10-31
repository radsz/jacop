/*
 * BalanceDetector.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.AbstractBalance;
import org.jacop.constraints.Deviation;
import org.jacop.constraints.Spread;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds balancing objectives over variables with a fixed sum and posts {@link Deviation} or
 * {@link Spread} on them as a redundant constraint. The pattern is a linear sum with unit
 * coefficients of terms |a * x[i] - b| (int_abs) or (a * x[i] - b)<sup>2</sup> (int_times of a
 * variable with itself, or int_pow with exponent 2), the same a and b in every term, where a * x[i]
 * - b is x[i] itself or defined by a two-variable int_lin_eq, and the x[i] are exactly the
 * variables of an int_lin_eq with unit coefficients that fixes their sum, as MiniZinc compiles
 * sum(i in I)(abs(n * x[i] - s)) together with sum(x) = s. The linear sum is an int_lin_eq with one
 * more variable of the opposite sign, the total, or an int_lin_le bounding the terms. All
 * constraints are still posted as usual, so the balancing constraint only adds pruning: the
 * decomposition posts each term on its own and does not see that the x[i] must add up to s.
 *
 * <p>Setting the system property {@code org.jacop.fz.balance} to false turns the detection off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class BalanceDetector implements ParserTreeConstants {

  private final Support support;

  /** A variable defined as p * y + q by a two-variable linear equation. */
  private record Affine(IntVar y, long p, long q) {}

  private final Map<IntVar, List<Affine>> definitions = new IdentityHashMap<>();

  // term -> its argument: term = |argument| or term = argument^2
  private final Map<IntVar, IntVar> absolute = new IdentityHashMap<>();
  private final Map<IntVar, IntVar> square = new IdentityHashMap<>();

  // the sums fixed by an int_lin_eq with unit coefficients, by their set of variables
  private final Map<Set<IntVar>, Long> sums = new HashMap<>();
  private final Set<IntVar> summed = new HashSet<>();

  private final List<ASTConstElem> linears = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public BalanceDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.balance is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.balance"));
  }

  /**
   * It scans the constraint items of the model and posts a Deviation or Spread for each balancing
   * sum it finds.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    Support.forEachConstraint(astTree, this::collect);
    if (absolute.isEmpty() && square.isEmpty()) {
      return;
    }
    for (ASTConstElem node : linears) {
      total(node);
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "int_lin_eq" -> {
        equation(node);
        linears.add(node);
      }
      case "int_lin_le" -> linears.add(node);
      case "int_abs" -> absolute.put(var(node, 1), var(node, 0));
      case "int_times" -> {
        IntVar t = var(node, 0);
        if (t == var(node, 1)) {
          square.put(var(node, 2), t);
        }
      }
      case "int_pow" -> {
        IntVar e = var(node, 1);
        if (e.singleton() && e.value() == 2) {
          square.put(var(node, 2), var(node, 0));
        }
      }
      default -> {
        // not part of a balancing sum
      }
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar var(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  // two-variable definitions and sums with unit coefficients
  private void equation(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    if (a == null || a.length != x.length) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (a.length == 2 && x[0] != x[1]) {
      // a[k] * x[k] + a[o] * x[o] = c with a[k] = +-1: x[k] = a[k] * c - a[k] * a[o] * x[o]
      for (int k = 0; k < 2; k++) {
        int o = 1 - k;
        if (Math.abs(a[k]) == 1 && a[o] != 0) {
          definitions
              .computeIfAbsent(x[k], v -> new ArrayList<>())
              .add(new Affine(x[o], -(long) a[k] * a[o], (long) a[k] * c));
        }
      }
    }
    if (a.length >= 2 && Math.abs(a[0]) == 1) {
      Set<IntVar> set = new HashSet<>();
      for (int k = 0; k < a.length; k++) {
        if (a[k] != a[0] || !set.add(x[k])) {
          return;
        }
      }
      sums.put(set, a[0] * c);
      summed.addAll(set);
    }
  }

  // sum of terms = total + shift, or sum of terms <= bound
  private void total(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] vars = support.getVarArray(child(node, 1));
    if (a == null || a.length < 2 || a.length != vars.length) {
      return;
    }
    int plus = 0;
    for (int k : a) {
      if (k == 1) {
        plus++;
      } else if (k != -1) {
        return;
      }
    }
    int minus = a.length - plus;
    boolean equation = node.getName().equals("int_lin_eq");
    // the terms have the sign e; for an inequality only e = 1 and no total
    int e;
    if (minus <= 1 && (minus == 0 || equation)) {
      e = 1;
    } else if (plus <= 1 && equation) {
      e = -1;
    } else {
      return;
    }
    List<IntVar> terms = new ArrayList<>();
    IntVar other = null;
    for (int k = 0; k < a.length; k++) {
      if (a[k] == e) {
        terms.add(vars[k]);
      } else {
        other = vars[k];
      }
    }
    if (terms.size() < 2) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    boolean squares;
    if (absolute.containsKey(terms.get(0))) {
      squares = false;
    } else if (square.containsKey(terms.get(0))) {
      squares = true;
    } else {
      return;
    }
    Map<IntVar, IntVar> argument = squares ? square : absolute;
    IntVar[] t = new IntVar[terms.size()];
    for (int i = 0; i < t.length; i++) {
      t[i] = argument.get(terms.get(i));
      if (t[i] == null) {
        return;
      }
    }
    // the terms over their defining variables, or over the arguments themselves
    if (!balance(t, true, squares, node, equation, e, c, other)) {
      balance(t, false, squares, node, equation, e, c, other);
    }
  }

  private boolean balance(
      IntVar[] t,
      boolean defined,
      boolean squares,
      ASTConstElem node,
      boolean equation,
      int e,
      long c,
      IntVar other) {
    int n = t.length;
    IntVar[] x = new IntVar[n];
    long a = 0;
    long b = 0;
    Set<IntVar> set = new HashSet<>();
    for (int i = 0; i < n; i++) {
      Affine f = defined ? definition(t[i]) : new Affine(t[i], 1, 0);
      if (f == null) {
        return false;
      }
      // |p * y + q| = | |p| * y - b | with b = -sign(p) * q, and the same for the square
      long ai = Math.abs(f.p());
      long bi = f.p() > 0 ? -f.q() : f.q();
      if (i == 0) {
        a = ai;
        b = bi;
      } else if (ai != a || bi != b) {
        return false;
      }
      x[i] = f.y();
      if (!set.add(x[i])) {
        return false;
      }
    }
    Long s = sums.get(set);
    if (s == null || !fits(a) || !fits(b) || !fits(s)) {
      return false;
    }
    IntVar cost = cost(equation, e, c, other);
    if (cost == null) {
      return false;
    }
    AbstractBalance balance =
        squares
            ? new Spread(x, (int) a, (int) b, (int) (long) s, cost)
            : new Deviation(x, (int) a, (int) b, (int) (long) s, cost);
    // redundant, so degree-based variable selections see the degrees of the model
    balance.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant " + balance + " for " + node.getName());
    }
    support.delayedConstraints.add(balance);
    return true;
  }

  // the definition of t over a variable whose sum is fixed
  private Affine definition(IntVar t) {
    List<Affine> list = definitions.get(t);
    if (list != null) {
      for (Affine f : list) {
        if (f.p() != 0 && summed.contains(f.y())) {
          return f;
        }
      }
    }
    return null;
  }

  private static boolean fits(long v) {
    return v >= IntDomain.MIN_INT && v <= IntDomain.MAX_INT;
  }

  /**
   * The variable equal to the sum of the terms: the total itself or shifted by a constant, or a new
   * variable for a sum fixed or bounded by a constant.
   */
  private IntVar cost(boolean equation, int e, long c, IntVar other) {
    // e * (sum of terms) - e * other = c (or <= c for e = 1), so sum of terms = other + e * c
    long shift = e * c;
    if (other != null) {
      if (shift == 0) {
        return other;
      }
      long min = other.min() + shift;
      long max = other.max() + shift;
      if (!fits(min) || !fits(max)) {
        return null;
      }
      IntVar v = new IntVar(support.store, (int) min, (int) max);
      support.delayedConstraints.add(new XplusCeqZ(other, (int) shift, v).setDegreeWeight(0));
      return v;
    }
    if (shift < 0) {
      return null;
    }
    long max = Math.min(shift, IntDomain.MAX_INT);
    return new IntVar(support.store, equation ? (int) max : 0, (int) max);
  }
}
