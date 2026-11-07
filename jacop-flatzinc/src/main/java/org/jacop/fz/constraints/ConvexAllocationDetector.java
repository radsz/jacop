/*
 * ConvexAllocationDetector.java
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
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.ConvexAllocation;
import org.jacop.constraints.ConvexCost;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds separable convex costs of variables whose sum is known and posts {@link
 * ConvexAllocation} for them as redundant constraints. A cost term is a variable of a linear
 * constraint (the objective's definition, or a bound on it) with a positive coefficient for the
 * direction of the bound, defined as a convex function of one variable x: |t| (int_abs), t &middot;
 * t (int_times, or int_pow with exponent 2), max(t, u) (int_max) or the square of a maximum, where
 * t and u are x or defined by two-variable int_lin_eq as p &middot; x + q. A group is a set of
 * variables with a known sum: an int_lin_eq with unit coefficients (a fixed sum, or a sum equal to
 * one more variable), or the loads of a jacop_bin_packing, which add up to the sum of the weights.
 * That is what MiniZinc makes of sum(p)((load[p] - target[p])^2), of weighted absolute deviations
 * from per-variable targets, and of the squared dead zones of the generalised balanced academic
 * curriculum (gbac), where the loads come from bin_packing_load.
 *
 * <p>For each linear constraint the terms of every group with two or more costed variables are
 * replaced by a new cost variable C<sub>g</sub> with ConvexAllocation(x, f, total, C<sub>g</sub>),
 * and the linear constraint is posted again over the C<sub>g</sub> and the other terms, as an
 * inequality in the direction of the bound. All constraints are still posted as usual, so this only
 * adds pruning. The linear constraints {@link BalanceDetector} has already covered with Deviation
 * or Spread are skipped.
 *
 * <p>Setting the system property {@code org.jacop.fz.convexAllocation} to false turns the detection
 * off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ConvexAllocationDetector implements ParserTreeConstants {

  private final Support support;

  private final Set<ASTConstElem> skipped;

  /** A variable defined as p * x + q by a two-variable linear equation. */
  private record Affine(IntVar x, long p, long q) {}

  /** A term over one variable: max of affine functions, or its square. */
  private static final class Shape {
    final IntVar x;
    final long[] a;
    final long[] b;
    final boolean squared;

    Shape(IntVar x, long[] a, long[] b, boolean squared) {
      this.x = x;
      this.a = a;
      this.b = b;
      this.squared = squared;
    }
  }

  /** A set of variables with a known sum: a constant, or a variable. */
  private static final class Group {
    final IntVar[] x;
    final IntVar total;
    final long sum;

    Group(IntVar[] x, IntVar total, long sum) {
      this.x = x;
      this.total = total;
      this.sum = sum;
    }
  }

  private final Map<IntVar, List<Affine>> definitions = new IdentityHashMap<>();

  // term -> its definition
  private final Map<IntVar, IntVar> absolute = new IdentityHashMap<>();
  private final Map<IntVar, IntVar> square = new IdentityHashMap<>();
  private final Map<IntVar, IntVar[]> maximum = new IdentityHashMap<>();

  private final List<Group> groups = new ArrayList<>();
  private final Map<IntVar, List<Group>> groupsOf = new IdentityHashMap<>();

  private final List<ASTConstElem> linears = new ArrayList<>();

  private int posted;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   * @param skipped the linear constraints already covered by Deviation or Spread.
   */
  public ConvexAllocationDetector(Support support, Set<ASTConstElem> skipped) {
    this.support = support;
    this.skipped = skipped;
  }

  /**
   * It tells if the detection is on. By default it is on for search without lazy clause generation
   * only: under LCG the stronger bound costs the balanced academic curriculum instances the large
   * improvements its restarts find (2 better, 12 worse of 14 with the search annotation), while
   * without LCG it wins on all of them. The system property org.jacop.fz.convexAllocation set to
   * true or false turns it on or off in both cases.
   *
   * @param lcg true when the model is solved with lazy clause generation.
   * @return true if the detection runs.
   */
  public static boolean enabled(boolean lcg) {
    String p = System.getProperty("org.jacop.fz.convexAllocation");
    if (p == null) {
      return !lcg;
    }
    return Boolean.parseBoolean(p);
  }

  /**
   * It scans the constraint items of the model and posts a ConvexAllocation for each group of
   * convex cost terms it finds in a linear constraint.
   *
   * @param astTree the root of the parsed model.
   * @return the number of ConvexAllocation constraints posted.
   */
  public int detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (groups.isEmpty() || absolute.isEmpty() && square.isEmpty() && maximum.isEmpty()) {
      return 0;
    }
    for (ASTConstElem node : linears) {
      if (!skipped.contains(node)) {
        linear(node);
      }
    }
    return posted;
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "int_lin_eq" -> {
        equation(node);
        linears.add(node);
      }
      case "int_lin_le" -> linears.add(node);
      case "int_abs" -> absolute.put(aVar(node, 1), aVar(node, 0));
      case "int_times" -> {
        IntVar t = aVar(node, 0);
        if (t == aVar(node, 1)) {
          square.put(aVar(node, 2), t);
        }
      }
      case "int_pow" -> {
        IntVar e = aVar(node, 1);
        if (e.singleton() && e.value() == 2) {
          square.put(aVar(node, 2), aVar(node, 0));
        }
      }
      case "int_max" -> maximum.put(aVar(node, 2), new IntVar[] {aVar(node, 0), aVar(node, 1)});
      case "jacop_bin_packing" -> binPacking(node);
      default -> {
        // not part of a convex cost
      }
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar aVar(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void addGroup(IntVar[] x, IntVar total, long sum) {
    Group g = new Group(x, total, sum);
    groups.add(g);
    for (IntVar v : x) {
      groupsOf.computeIfAbsent(v, k -> new ArrayList<>()).add(g);
    }
  }

  // two-variable definitions, and sums with unit coefficients
  private void equation(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    if (a == null || a.length != x.length) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (a.length == 2 && x[0] != x[1]) {
      for (int k = 0; k < 2; k++) {
        int o = 1 - k;
        if (Math.abs(a[k]) == 1 && a[o] != 0) {
          definitions
              .computeIfAbsent(x[k], v -> new ArrayList<>())
              .add(new Affine(x[o], -(long) a[k] * a[o], (long) a[k] * c));
        }
      }
    }
    // e * (x[0] + ... ) - e * total = c, or e * (x[0] + ...) = c
    int plus = 0;
    for (int k : a) {
      if (k == 1) {
        plus++;
      } else if (k != -1) {
        return;
      }
    }
    int minus = a.length - plus;
    int e;
    if (minus <= 1) {
      e = 1;
    } else if (plus <= 1) {
      e = -1;
    } else {
      return;
    }
    List<IntVar> summed = new ArrayList<>();
    IntVar total = null;
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int k = 0; k < a.length; k++) {
      if (!seen.add(x[k])) {
        return;
      }
      if (a[k] == e) {
        summed.add(x[k]);
      } else {
        total = x[k];
      }
    }
    if (total != null && a.length < 3) {
      return;
    }
    // a fixed sum of two variables is almost always the definition of one of them
    if (total == null && summed.size() >= 3 && fits(e * c)) {
      addGroup(summed.toArray(new IntVar[0]), null, e * c);
    } else if (total != null && c == 0) {
      addGroup(summed.toArray(new IntVar[0]), total, 0);
    }
  }

  private static boolean fits(long v) {
    return v >= IntDomain.MIN_INT && v <= IntDomain.MAX_INT;
  }

  // the loads of a bin packing add up to the sum of the weights
  private void binPacking(ASTConstElem node) {
    IntVar[] load = support.getVarArray(child(node, 1));
    int[] w = support.getIntArray(child(node, 2));
    if (load == null || w == null || load.length < 2) {
      return;
    }
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (IntVar v : load) {
      if (!seen.add(v)) {
        return;
      }
    }
    long sum = 0;
    for (int k : w) {
      sum += k;
    }
    if (sum <= IntDomain.MAX_INT) {
      addGroup(load.clone(), null, sum);
    }
  }

  // the definition of t over x, or t itself
  private List<Affine> affines(IntVar t) {
    List<Affine> list = new ArrayList<>();
    list.add(new Affine(t, 1, 0));
    List<Affine> defined = definitions.get(t);
    if (defined != null) {
      list.addAll(defined);
    }
    return list;
  }

  // the max of affine functions of one variable that m is, given as candidate shapes per variable
  private Map<IntVar, long[][]> inner(IntVar m) {
    Map<IntVar, long[][]> result = new IdentityHashMap<>();
    IntVar t = absolute.get(m);
    if (t != null) {
      for (Affine f : affines(t)) {
        result.put(f.x(), new long[][] {{f.p(), -f.p()}, {f.q(), -f.q()}});
      }
      return result;
    }
    IntVar[] mx = maximum.get(m);
    if (mx != null) {
      // a constant side, as in max(x - q, 0), is an affine function of any variable
      if (mx[0].singleton() || mx[1].singleton()) {
        IntVar side = mx[0].singleton() ? mx[1] : mx[0];
        long constant = mx[0].singleton() ? mx[0].value() : mx[1].value();
        for (Map.Entry<IntVar, long[][]> e : innerAffine(side).entrySet()) {
          long[] a = concat(e.getValue()[0], new long[] {0});
          long[] b = concat(e.getValue()[1], new long[] {constant});
          result.put(e.getKey(), new long[][] {a, b});
        }
        return result;
      }
      Map<IntVar, long[][]> left = innerAffine(mx[0]);
      Map<IntVar, long[][]> right = innerAffine(mx[1]);
      for (Map.Entry<IntVar, long[][]> l : left.entrySet()) {
        long[][] r = right.get(l.getKey());
        if (r != null) {
          long[] a = concat(l.getValue()[0], r[0]);
          long[] b = concat(l.getValue()[1], r[1]);
          result.put(l.getKey(), new long[][] {a, b});
        }
      }
      return result;
    }
    return innerAffine(m);
  }

  private Map<IntVar, long[][]> innerAffine(IntVar t) {
    Map<IntVar, long[][]> result = new IdentityHashMap<>();
    for (Affine f : affines(t)) {
      result.put(f.x(), new long[][] {{f.p()}, {f.q()}});
    }
    return result;
  }

  private static long[] concat(long[] a, long[] b) {
    long[] c = Arrays.copyOf(a, a.length + b.length);
    System.arraycopy(b, 0, c, a.length, b.length);
    return c;
  }

  // the shapes of a term over each variable it can be written over (none if it is not a term)
  private Map<IntVar, Shape> shapes(IntVar y) {
    Map<IntVar, Shape> result = new IdentityHashMap<>();
    IntVar t = square.get(y);
    boolean squared = t != null;
    if (!squared) {
      if (!absolute.containsKey(y) && !maximum.containsKey(y)) {
        return result;
      }
      t = y;
    }
    for (Map.Entry<IntVar, long[][]> e : inner(t).entrySet()) {
      result.put(e.getKey(), new Shape(e.getKey(), e.getValue()[0], e.getValue()[1], squared));
    }
    return result;
  }

  // one direction of a linear constraint: sum of w[k] * y[k] <= bound
  private void linear(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] y = support.getVarArray(child(node, 1));
    if (a == null || a.length != y.length || a.length < 2) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    boolean equation = node.getName().equals("int_lin_eq");
    direction(node, a, y, c, 1);
    if (equation) {
      direction(node, a, y, c, -1);
    }
  }

  private void direction(ASTConstElem node, int[] a, IntVar[] y, long c, int d) {
    // the terms with a positive weight, by the variables they are a convex function of
    Map<IntVar, List<Integer>> byVariable = new IdentityHashMap<>();
    List<Map<IntVar, Shape>> shapes = new ArrayList<>();
    for (int k = 0; k < y.length; k++) {
      Map<IntVar, Shape> s = d * (long) a[k] > 0 ? shapes(y[k]) : Map.of();
      shapes.add(s);
      for (IntVar x : s.keySet()) {
        if (groupsOf.containsKey(x)) {
          byVariable.computeIfAbsent(x, v -> new ArrayList<>()).add(k);
        }
      }
    }
    if (byVariable.size() < 2) {
      return;
    }
    // groups by the number of costed variables, largest first, each term in one group only
    List<Group> candidates = new ArrayList<>();
    for (Group g : groups) {
      if (costed(g, byVariable) >= 2) {
        candidates.add(g);
      }
    }
    candidates.sort((g, h) -> Integer.compare(costed(h, byVariable), costed(g, byVariable)));
    boolean[] used = new boolean[y.length];
    List<IntVar> newVars = new ArrayList<>();
    for (Group g : candidates) {
      ConvexAllocation allocation = allocation(g, byVariable, shapes, a, d, used);
      if (allocation != null) {
        newVars.add(allocation.getCost());
        allocation.setDegreeWeight(0);
        if (support.options.debug()) {
          FzConsole.println("% redundant " + allocation + " for " + node.getName());
        }
        support.delayedConstraints.add(allocation);
        posted++;
      }
    }
    if (newVars.isEmpty()) {
      return;
    }
    // the linear constraint again, with each group's terms replaced by its cost
    List<IntVar> vars = new ArrayList<>(newVars);
    List<Integer> weights = new ArrayList<>(Collections.nCopies(newVars.size(), 1));
    for (int k = 0; k < y.length; k++) {
      if (!used[k]) {
        vars.add(y[k]);
        weights.add(d * a[k]);
      }
    }
    long bound = d * c;
    if (bound < IntDomain.MIN_INT || bound > IntDomain.MAX_INT) {
      return;
    }
    LinearInt redundant = new LinearInt(vars, weights, "<=", (int) bound);
    redundant.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant " + redundant + " for " + node.getName());
    }
    support.delayedConstraints.add(redundant);
  }

  private static int costed(Group g, Map<IntVar, List<Integer>> byVariable) {
    int count = 0;
    for (IntVar v : g.x) {
      if (byVariable.containsKey(v)) {
        count++;
      }
    }
    return count;
  }

  // the allocation over a group, with the terms it takes marked used; null if none fits
  private ConvexAllocation allocation(
      Group g,
      Map<IntVar, List<Integer>> byVariable,
      List<Map<IntVar, Shape>> shapes,
      int[] a,
      int d,
      boolean[] used) {
    int n = g.x.length;
    ConvexCost[] f = new ConvexCost[n];
    List<Integer> taken = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      List<Integer> terms = byVariable.get(g.x[i]);
      ConvexCost cost = null;
      if (terms != null) {
        for (int k : terms) {
          if (used[k] || taken.contains(k)) {
            continue;
          }
          Shape s = shapes.get(k).get(g.x[i]);
          long w = d * (long) a[k];
          ConvexCost piece =
              s.squared ? ConvexCost.squaredMax(w, s.a, s.b) : ConvexCost.max(w, s.a, s.b);
          cost = cost == null ? piece : cost.plus(piece);
          taken.add(k);
        }
      }
      f[i] = cost == null ? ConvexCost.linear(0, 0) : cost;
    }
    if (taken.size() < 2) {
      return null;
    }
    // the cost variable takes the place of the terms: it ranges over the sums of their costs
    long least = 0;
    long most = 0;
    try {
      for (int i = 0; i < n; i++) {
        long lo = g.x[i].min();
        long hi = g.x[i].max();
        if (!f[i].isConvexOn(lo, hi)) {
          return null;
        }
        least += f[i].value(f[i].argMin(lo, hi));
        most += Math.max(f[i].value(lo), f[i].value(hi));
      }
    } catch (ArithmeticException _) {
      return null;
    }
    if (!fits(least) || !fits(most)) {
      return null;
    }
    IntVar total = g.total != null ? g.total : new IntVar(support.store, (int) g.sum, (int) g.sum);
    IntVar cost = new IntVar(support.store, (int) least, (int) most);
    ConvexAllocation allocation;
    try {
      allocation = new ConvexAllocation(g.x, f, total, cost);
    } catch (IllegalArgumentException _) {
      // a cost too large for exact arithmetic
      return null;
    }
    for (int k : taken) {
      used[k] = true;
    }
    return allocation;
  }
}
