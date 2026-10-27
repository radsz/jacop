/*
 * CardinalityDetector.java
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.GCC;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds counts written by hand as sums of reified equalities and posts a {@link GCC} on the
 * counted variables as a redundant constraint. A model that writes {@code sum(i)(bool2int(x[i] =
 * v)) = n[v]} for several values v over the same variables x is flattened into an {@code
 * int_eq_reif(x[i], v, b[i])} for each i and v and one linear constraint over the b's for each v.
 * Each such linear constraint {@code a * (b[1] + ... + b[k]) + c * y rel rhs} (the term {@code c *
 * y} is optional), with the same coefficient a on all literals of one value over distinct
 * variables, is a count of v in x. When at least two values are counted over the same set of
 * variables and at least one count is an equation with a variable y, a GCC is posted on the
 * variables, with a counter for each counted value linked to its linear constraints and a free
 * counter for every other value. Counts with fixed bounds only (at most k of each value, as in
 * timetabling) get a GCC only under free search (option -f): under the model's own search the GCC
 * pruned about as much as the sums and cost up to twice the time (bacp, prize-collecting), while
 * under free search it cut the nodes (prize-collecting) and found solutions where the sums found
 * none (skill-allocation). A GCC also needs at least one counted value for every {@link
 * #MIN_VALUES_FACTOR} variables. The system property value {@code all} drops both conditions.
 *
 * <p>All constraints of the model are still posted as usual, so the GCC only adds pruning: it
 * reasons about all counts at once, which the separate sums cannot do (for example in magic
 * sequence models, where the counters are the counted variables themselves).
 *
 * <p>Setting the system property {@code org.jacop.fz.cardinality} to false turns the detection off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CardinalityDetector implements ParserTreeConstants {

  // fewest literals a linear constraint must have to be read as a count
  static final int MIN_COUNT_SIZE = 2;

  // a GCC is posted only if at least one value in MIN_VALUES_FACTOR variables is counted; with
  // few counted values over many variables (battleship ship counts over the cells of a board) it
  // pruned nothing more than the sums and cost about 15% more time
  static final int MIN_VALUES_FACTOR = 4;

  // a GCC gets a counter for every value between the smallest and the largest value of its
  // variables, so it is posted only if there are at most MAX_RANGE_FACTOR * n + MAX_RANGE_SLACK
  static final int MAX_RANGE_FACTOR = 10;
  static final int MAX_RANGE_SLACK = 100;

  private final Support support;

  // GCCs also for counts with fixed bounds only
  private final boolean all =
      "all".equalsIgnoreCase(System.getProperty("org.jacop.fz.cardinality"));

  // b <-> x = v
  private record Literal(IntVar x, int v) {}

  private final Map<IntVar, Literal> literals = new IdentityHashMap<>();

  private final List<ASTConstElem> linears = new ArrayList<>();

  // a * count(x, v) + sum(c[i] * y[i]) rel rhs
  private static final class Count {
    final int v;
    final int a;
    final IntVar[] y;
    final int[] c;
    final String rel;
    final int rhs;

    Count(int v, int a, IntVar[] y, int[] c, String rel, int rhs) {
      this.v = v;
      this.a = a;
      this.y = y;
      this.c = c;
      this.rel = rel;
      this.rhs = rhs;
    }

    // an equation with a counter variable, rather than fixed bounds on the count
    boolean variable() {
      return rel.equals("==") && y.length == 1 && !y[0].singleton();
    }
  }

  // the counts of each set of variables, in the order they are found
  private final Map<Set<IntVar>, Group> groups = new LinkedHashMap<>();

  private static final class Group {
    final IntVar[] x;
    final List<Count> counts = new ArrayList<>();

    Group(IntVar[] x) {
      this.x = x;
    }
  }

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public CardinalityDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.cardinality is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.cardinality"));
  }

  /**
   * It scans the constraint items of the model and posts a GCC for each set of variables whose
   * values are counted for at least two values.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    Support.forEachConstraint(astTree, this::collect);
    if (literals.isEmpty()) {
      return;
    }
    for (ASTConstElem node : linears) {
      linear(node);
    }
    int posted = 0;
    for (Group g : groups.values()) {
      if (post(g)) {
        posted++;
      }
    }
    if (support.options.debug()) {
      FzConsole.println("% cardinality: " + groups.size() + " counted sets, " + posted + " GCCs");
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "int_eq_reif" -> {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        Literal l = null;
        if (p2.getType() == 0 && p1.getType() != 0) {
          l = new Literal(support.getVariable(p1), support.getInt(p2));
        } else if (p1.getType() == 0 && p2.getType() != 0) {
          l = new Literal(support.getVariable(p2), support.getInt(p1));
        }
        if (l != null && !b.singleton() && !l.x.singleton()) {
          literals.putIfAbsent(b, l);
        }
      }
      case "int_lin_eq", "int_lin_le" -> linears.add(node);
      default -> {
        // not part of a count
      }
    }
  }

  private void linear(ASTConstElem node) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] vs = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (a == null || a.length != vs.length) {
      return;
    }
    int rhs = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

    // the value and coefficient shared by most literals
    Map<Long, int[]> frequency = new HashMap<>();
    long best = 0;
    int bestFrequency = 0;
    for (int i = 0; i < vs.length; i++) {
      Literal l = literals.get(vs[i]);
      if (l != null) {
        long key = ((long) l.v << 32) | (a[i] & 0xffffffffL);
        int f = ++frequency.computeIfAbsent(key, k -> new int[1])[0];
        if (f > bestFrequency) {
          bestFrequency = f;
          best = key;
        }
      }
    }
    if (bestFrequency < MIN_COUNT_SIZE) {
      return;
    }
    int value = (int) (best >> 32);
    int weight = (int) best;

    List<IntVar> x = new ArrayList<>();
    Set<IntVar> xs = new HashSet<>();
    List<IntVar> y = new ArrayList<>();
    List<Integer> c = new ArrayList<>();
    for (int i = 0; i < vs.length; i++) {
      Literal l = literals.get(vs[i]);
      if (l != null && l.v == value && a[i] == weight && xs.add(l.x)) {
        x.add(l.x);
      } else {
        y.add(vs[i]);
        c.add(a[i]);
      }
    }
    if (x.size() < MIN_COUNT_SIZE || y.size() > 1) {
      return;
    }
    IntVar[] xa = x.toArray(new IntVar[0]);
    Group g = groups.computeIfAbsent(xs, k -> new Group(xa));
    String rel = node.getName().equals("int_lin_eq") ? "==" : "<=";
    g.counts.add(
        new Count(
            value,
            weight,
            y.toArray(new IntVar[0]),
            c.stream().mapToInt(Integer::intValue).toArray(),
            rel,
            rhs));
  }

  private boolean post(Group g) {
    Map<Integer, List<Count>> byValue = new LinkedHashMap<>();
    for (Count k : g.counts) {
      byValue.computeIfAbsent(k.v, v -> new ArrayList<>()).add(k);
    }
    if (byValue.size() < 2) {
      return false;
    }
    if (!all
        && (MIN_VALUES_FACTOR * byValue.size() < g.x.length
            || !support.options.freeSearch() && g.counts.stream().noneMatch(Count::variable))) {
      return false;
    }

    int min = Integer.MAX_VALUE;
    int max = Integer.MIN_VALUE;
    for (IntVar v : g.x) {
      min = Math.min(min, v.min());
      max = Math.max(max, v.max());
    }
    int n = g.x.length;
    if ((long) max - min + 1 > MAX_RANGE_FACTOR * (long) n + MAX_RANGE_SLACK) {
      return false;
    }
    Set<IntVar> used = new HashSet<>();
    IntVar[] counter = new IntVar[max - min + 1];
    for (int v = min; v <= max; v++) {
      List<Count> counts = byValue.get(v);
      counter[v - min] =
          counts == null ? new IntVar(support.store, 0, n) : counter(counts, n, used);
    }
    GCC gcc = new GCC(g.x, counter, min);
    // redundant, so degree-based variable selections see the degrees of the model
    gcc.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println(
          "% redundant GCC on " + n + " variables, " + byValue.size() + " counted values");
    }
    support.delayedConstraints.add(gcc);
    return true;
  }

  // the counter of one value: the variable y of a count a * count - a * y = 0 when there is one
  // not used yet, otherwise a new variable linked to each linear constraint
  private IntVar counter(List<Count> counts, int n, Set<IntVar> used) {
    IntVar counter = null;
    for (Count k : counts) {
      if (k.rel.equals("==")
          && k.rhs == 0
          && k.y.length == 1
          && k.c[0] == -k.a
          && !used.contains(k.y[0])) {
        counter = k.y[0];
        break;
      }
    }
    if (counter == null) {
      counter = new IntVar(support.store, 0, n);
    } else {
      used.add(counter);
    }
    for (Count k : counts) {
      if (k.y.length == 1 && k.y[0] == counter && k.c[0] == -k.a && k.rhs == 0) {
        continue;
      }
      IntVar[] list = new IntVar[k.y.length + 1];
      int[] w = new int[k.y.length + 1];
      list[0] = counter;
      w[0] = k.a;
      System.arraycopy(k.y, 0, list, 1, k.y.length);
      System.arraycopy(k.c, 0, w, 1, k.c.length);
      // redundant, like the GCC
      support.delayedConstraints.add(new LinearInt(list, w, k.rel, k.rhs).setDegreeWeight(0));
    }
    return counter;
  }
}
