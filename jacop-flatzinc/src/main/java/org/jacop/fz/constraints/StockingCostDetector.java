/*
 * StockingCostDetector.java
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
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.StockingCost;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds lot sizing costs and posts {@link StockingCost} on them as a redundant constraint. The
 * capacity comes from an alldifferent (capacity 1) or a global cardinality whose cover holds every
 * value of the variables (capacity the largest upper bound); the cost is an int_lin_eq over exactly
 * those variables, all with coefficients of the same sign, and at least one other variable, such as
 * cost = sum(i) h[i] * (d[i] - x[i]) or an objective that adds other costs to it. An int_lin_le is
 * used when it bounds the cost from above. The due dates are the maxima of the variables, so the
 * stocking cost is the sum of the other terms of the linear constraint plus a constant; it gets a
 * new variable defined by them. All constraints are still posted as usual, so the StockingCost only
 * adds pruning: a lower bound on the cost from the capacity, and the earliest periods its maximum
 * allows.
 *
 * <p>Setting the system property {@code org.jacop.fz.stockingCost} to false turns the detection
 * off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class StockingCostDetector implements ParserTreeConstants {

  private final Support support;

  // the variables of each capacity constraint, as a set, and its capacity
  private final List<Set<IntVar>> groups = new ArrayList<>();
  private final List<Integer> capacities = new ArrayList<>();

  private final List<ASTConstElem> linears = new ArrayList<>();

  // variables of the stocking_cost predicates of the model, which post the constraint already
  private final Set<IntVar> posted = Collections.newSetFromMap(new IdentityHashMap<>());

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public StockingCostDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.stockingCost is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.stockingCost"));
  }

  /**
   * It scans the constraint items of the model and posts a StockingCost for each stocking cost over
   * variables with a capacity.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item);
          }
        }
      }
    }
    if (groups.isEmpty()) {
      return;
    }
    for (ASTConstElem node : linears) {
      cost(node);
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_alldiff", "jacop_alldistinct" -> group(support.getVarArray(child(node, 0)), 1);
      case "jacop_count_values_bounds" -> cardinality(node);
      case "int_lin_eq", "int_lin_le" -> linears.add(node);
      case "jacop_stocking_cost" -> Collections.addAll(posted, support.getVarArray(child(node, 0)));
      default -> {
        // not part of a stocking cost
      }
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private void group(IntVar[] x, int capacity) {
    Set<IntVar> set = Collections.newSetFromMap(new IdentityHashMap<>());
    Collections.addAll(set, x);
    // a repeated variable takes its period twice, which the constraint does not model
    if (set.size() == x.length && x.length > 1) {
      groups.add(set);
      capacities.add(capacity);
    }
  }

  // at most max(ub) orders per period when the cover holds every value of x
  private void cardinality(ASTConstElem node) {
    IntVar[] x = support.getVarArray(child(node, 0));
    int[] cover = support.getIntArray(child(node, 1));
    int[] ub = support.getIntArray(child(node, 3));
    if (cover == null || ub == null || cover.length == 0 || ub.length != cover.length) {
      return;
    }
    IntervalDomain values = new IntervalDomain();
    int capacity = 0;
    for (int i = 0; i < cover.length; i++) {
      values.unionAdapt(cover[i]);
      capacity = Math.max(capacity, ub[i]);
    }
    for (IntVar v : x) {
      if (!values.contains(v.domain)) {
        return;
      }
    }
    if (capacity >= 1) {
      group(x, capacity);
    }
  }

  // sum(k) a[k] * vars[k] = c (or <= c) with the variables of a group and at least one other
  private void cost(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] vars = support.getVarArray(child(node, 1));
    if (a == null || a.length != vars.length || a.length < 3) {
      return;
    }
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    boolean equation = node.getName().equals("int_lin_eq");
    for (int g = 0; g < groups.size(); g++) {
      Set<IntVar> group = groups.get(g);
      List<IntVar> x = new ArrayList<>();
      List<Integer> weights = new ArrayList<>();
      List<IntVar> others = new ArrayList<>();
      List<Integer> otherWeights = new ArrayList<>();
      for (int k = 0; k < a.length; k++) {
        if (group.contains(vars[k])) {
          x.add(vars[k]);
          weights.add(a[k]);
        } else {
          others.add(vars[k]);
          otherWeights.add(a[k]);
        }
      }
      if (x.size() != group.size() || others.isEmpty() || posted.containsAll(x)) {
        continue;
      }
      post(x, weights, others, otherWeights, c, equation, capacities.get(g));
      return;
    }
  }

  /**
   * With h = -tau * a for the variables x and b the weights of the others y: sum(i) h[i] * (d[i] -
   * x[i]) = sum(i) h[i] * d[i] + tau * c - tau * sum(j) b[j] * y[j], or at most that for int_lin_le
   * with tau = 1.
   */
  private void post(
      List<IntVar> xs,
      List<Integer> a,
      List<IntVar> ys,
      List<Integer> b,
      int c,
      boolean equation,
      int capacity) {
    int sign = Integer.signum(a.get(0));
    for (int w : a) {
      if (w == 0 || Integer.signum(w) != sign) {
        return;
      }
    }
    int tau = -sign;
    if (!equation && tau != 1) {
      return;
    }
    int n = xs.size();
    IntVar[] x = xs.toArray(new IntVar[0]);
    int[] h = new int[n];
    int[] due = new int[n];
    long constant = (long) tau * c;
    for (int i = 0; i < n; i++) {
      h[i] = -tau * a.get(i);
      due[i] = x[i].max();
      constant += (long) h[i] * due[i];
    }
    // z = constant - tau * sum(j) b[j] * y[j]
    long low = constant;
    long high = constant;
    for (int j = 0; j < ys.size(); j++) {
      long w = -(long) tau * b.get(j);
      IntVar y = ys.get(j);
      low += Math.min(w * y.min(), w * y.max());
      high += Math.max(w * y.min(), w * y.max());
    }
    low = Math.max(low, 0);
    if (high > IntDomain.MAX_INT
        || low > high
        || constant > IntDomain.MAX_INT
        || constant < IntDomain.MIN_INT) {
      return;
    }
    IntVar z;
    if (ys.size() == 1 && tau * b.get(0) == -1 && constant == 0) {
      z = ys.get(0);
    } else {
      z = new IntVar(support.store, (int) low, (int) high);
      IntVar[] list = new IntVar[ys.size() + 1];
      int[] weights = new int[ys.size() + 1];
      for (int j = 0; j < ys.size(); j++) {
        list[j] = ys.get(j);
        weights[j] = tau * b.get(j);
      }
      list[ys.size()] = z;
      weights[ys.size()] = 1;
      support.delayedConstraints.add(
          new LinearInt(list, weights, "==", (int) constant).setDegreeWeight(0));
    }
    StockingCost sc = new StockingCost(x, due, h, z, capacity);
    // redundant, so degree-based variable selections see the degrees of the model
    sc.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant " + sc);
    }
    support.delayedConstraints.add(sc);
  }
}
