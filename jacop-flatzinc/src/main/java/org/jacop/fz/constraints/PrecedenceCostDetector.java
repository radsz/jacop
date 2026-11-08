/*
 * PrecedenceCostDetector.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.constraints;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.PrecedenceCost;
import org.jacop.constraints.UnaryEarlinessTardiness;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds sums of earliness and tardiness terms over start times with precedences and posts a
 * redundant {@link PrecedenceCost} on them. A term is {@code y = max(0, a)} ({@code int_max} with a
 * constant 0) where {@code a} is {@code s - b} or {@code b - s}, directly or through an {@code
 * int_lin_eq} over a and s with unit coefficients; the cost is an {@code int_lin_eq} (or an {@code
 * int_lin_le} bounding it from above) with positive coefficients on at least two such terms and a
 * coefficient of -1 on one other variable, as MiniZinc writes {@code objective = sum(i) e[i] *
 * max(0, d[i] - s[i]) + t[i] * max(0, s[i] - d[i])}. The precedences are the difference constraints
 * {@code x - y <= c} ({@code int_lin_le}, {@code int_le}, {@code int_lt}) that link the start
 * times, directly or through variables without a cost; one that would close a cycle is left out.
 * The constraint is posted only when there is at least one precedence.
 *
 * <p>It is on with the model's search and off with free search (-f); the system property {@code
 * org.jacop.fz.precedenceCost} set to true or false turns it on or off in both.
 *
 * <p>When some of the starts of such a sum are tasks of unary resources (the cliques of the
 * disjunctive clique detection, and the tasks of a {@code jacop_cumulative} that use more than half
 * of its capacity), with fixed durations, it also posts a redundant {@link UnaryEarlinessTardiness}
 * on those resources, which bounds the sum by the assignment bound of Sourd and Kedad-Sidhoum
 * (2003); precedences are not needed for it. Each task's costs are counted on the resource with the
 * most work among those it is on. The system property {@code org.jacop.fz.unaryEarlinessTardiness}
 * set to false turns this part off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class PrecedenceCostDetector implements ParserTreeConstants {

  // the largest graph the constraint is posted on
  private static final int MAX_TASKS = 5000;

  private final Support support;

  private final Store scratch = new Store();
  private final Map<Integer, IntVar> constants = new HashMap<>();

  // y = max(0, a)
  private final Map<IntVar, IntVar> hinge = new IdentityHashMap<>();
  // a = sign * s + offset, as {s, sign, offset}
  private final Map<IntVar, Object[]> affine = new IdentityHashMap<>();
  // x - y <= c, as from x to y with lag -c
  private final List<IntVar[]> diffVars = new ArrayList<>();
  private final List<Long> diffLags = new ArrayList<>();
  private final List<ASTConstElem> sums = new ArrayList<>();
  // unary resources: starts and fixed durations
  private final List<IntVar[]> unaryStarts = new ArrayList<>();
  private final List<int[]> unaryDurations = new ArrayList<>();

  private final boolean precedenceCost;
  private final boolean unary;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public PrecedenceCostDetector(Support support) {
    this(support, true, true);
  }

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   * @param precedenceCost whether it posts {@link PrecedenceCost}.
   * @param unary whether it posts {@link UnaryEarlinessTardiness}.
   */
  public PrecedenceCostDetector(Support support, boolean precedenceCost, boolean unary) {
    this.support = support;
    this.precedenceCost = precedenceCost;
    this.unary = unary;
  }

  /**
   * It tells if the detection of earliness and tardiness costs on unary resources is on: unless the
   * system property org.jacop.fz.unaryEarlinessTardiness is false.
   *
   * @param freeSearch whether free search (-f) is used.
   * @return false if the system property org.jacop.fz.unaryEarlinessTardiness is false.
   */
  public static boolean unaryEnabled(boolean freeSearch) {
    String p = System.getProperty("org.jacop.fz.unaryEarlinessTardiness");
    return p == null || !"false".equalsIgnoreCase(p);
  }

  /**
   * It tells if the detection is on: by default with the model's search, and with free search only
   * when the system property org.jacop.fz.precedenceCost is true (on rcpsp-wet it paid with the
   * model's search and lost with free search).
   *
   * @param freeSearch whether free search (-f) is used.
   * @return false if the system property org.jacop.fz.precedenceCost is false, or it is not set and
   *     free search is used.
   */
  public static boolean enabled(boolean freeSearch) {
    String p = System.getProperty("org.jacop.fz.precedenceCost");
    return p == null ? !freeSearch : !"false".equalsIgnoreCase(p);
  }

  /**
   * It scans the model and adds a redundant {@link PrecedenceCost} to the delayed constraints for
   * every sum of earliness and tardiness terms over start times with precedences.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (hinge.isEmpty()) {
      return;
    }
    if (unary) {
      for (IntVar[][] r : support.unaryResources) {
        unaryResource(r[0], r[1]);
      }
    }
    for (ASTConstElem node : sums) {
      sum(node);
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "int_max" -> {
        IntVar a = scalar(node, 0);
        IntVar b = scalar(node, 1);
        IntVar y = scalar(node, 2);
        if (isZero(a) && !b.singleton() && !y.singleton()) {
          hinge.put(y, b);
        } else if (isZero(b) && !a.singleton() && !y.singleton()) {
          hinge.put(y, a);
        }
      }
      case "int_lin_eq" -> {
        sums.add(node);
        linear(node, true);
      }
      case "int_lin_le" -> {
        sums.add(node);
        linear(node, false);
      }
      case "jacop_cumulative" -> cumulative(node);
      case "int_le" -> difference(scalar(node, 0), scalar(node, 1), 0);
      case "int_lt" -> difference(scalar(node, 0), scalar(node, 1), -1);
      default -> {
        // not part of an earliness or tardiness cost
      }
    }
  }

  // the tasks of a cumulative that use more than half of its capacity, so no two overlap
  private void cumulative(ASTConstElem node) {
    if (!unary) {
      return;
    }
    IntVar[] s = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] d = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] r = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    IntVar b = scalar(node, 3);
    if (s == null || d == null || r == null || s.length != d.length || s.length != r.length) {
      return;
    }
    List<IntVar> starts = new ArrayList<>();
    List<IntVar> durations = new ArrayList<>();
    for (int i = 0; i < s.length; i++) {
      if (2L * r[i].min() > b.max()) {
        starts.add(s[i]);
        durations.add(d[i]);
      }
    }
    unaryResource(starts.toArray(new IntVar[0]), durations.toArray(new IntVar[0]));
  }

  // a unary resource over the tasks with a fixed positive duration and a start not fixed
  private void unaryResource(IntVar[] s, IntVar[] d) {
    List<IntVar> starts = new ArrayList<>();
    List<Integer> durations = new ArrayList<>();
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (int i = 0; i < s.length; i++) {
      if (d[i].singleton()
          && d[i].value() > 0
          && !s[i].singleton()
          && seen.put(s[i], true) == null) {
        starts.add(s[i]);
        durations.add(d[i].value());
      }
    }
    if (starts.size() >= 2) {
      unaryStarts.add(starts.toArray(new IntVar[0]));
      unaryDurations.add(durations.stream().mapToInt(Integer::intValue).toArray());
    }
  }

  private static boolean isZero(IntVar x) {
    return x.singleton() && x.value() == 0;
  }

  // constants come from a scratch store, so that reading the model adds no variable to it
  private IntVar scalar(SimpleNode node, int i) {
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) node.jjtGetChild(i);
    int type = e.getType();
    if (type == 0 || type == 1) {
      return constant(e.getInt());
    }
    if (type == 2 && support.dictionary.getVariable(e.getIdent()) == null) {
      return constant(support.dictionary.getInt(e.getIdent()));
    }
    return support.getVariable(e);
  }

  private IntVar constant(int c) {
    return constants.computeIfAbsent(c, k -> new IntVar(scratch, k, k));
  }

  // the two variables of an array of length two, or null
  private IntVar[] pair(SimpleNode array) {
    if (array.getId() == JJTARRAYLITERAL) {
      if (array.jjtGetNumChildren() != 2) {
        return null;
      }
      return new IntVar[] {scalar(array, 0), scalar(array, 1)};
    }
    if (array.getId() == JJTSCALARFLATEXPR && ((ASTScalarFlatExpr) array).getType() == 2) {
      IntVar[] x = support.dictionary.getVariableArray(((ASTScalarFlatExpr) array).getIdent());
      return x != null && x.length == 2 ? x : null;
    }
    return null;
  }

  // two-variable linear constraints: a difference x - y <= c, or a = sign * s + offset
  private void linear(ASTConstElem node, boolean equation) {
    int[] k = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    if (k == null || k.length != 2 || Math.abs(k[0]) != 1 || Math.abs(k[1]) != 1) {
      return;
    }
    IntVar[] x = pair((SimpleNode) node.jjtGetChild(1));
    if (x == null || x[0] == x[1] || x[0].singleton() || x[1].singleton()) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (!equation) {
      if (k[0] == -k[1]) {
        // k0 * (x0 - x1) <= c
        difference(k[0] > 0 ? x[0] : x[1], k[0] > 0 ? x[1] : x[0], c);
      }
      return;
    }
    // k0 * x0 + k1 * x1 = c: x1 = (c - k0 * x0) / k1, and x0 the same way
    affine.putIfAbsent(x[1], new Object[] {x[0], (long) -k[0] * k[1], c * k[1]});
    affine.putIfAbsent(x[0], new Object[] {x[1], (long) -k[1] * k[0], c * k[0]});
  }

  private void difference(IntVar x, IntVar y, long c) {
    if (x == y
        || x.singleton()
        || y.singleton()
        || c < IntDomain.MIN_INT
        || c > IntDomain.MAX_INT) {
      return;
    }
    diffVars.add(new IntVar[] {x, y});
    diffLags.add(-c);
  }

  // sum(k) w[k] * y[k] - z = c (or <= c) with at least two terms y = max(0, +-s + b)
  private void sum(ASTConstElem node) {
    int[] w = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] vars = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (w == null || vars == null || w.length != vars.length || w.length < 3) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (node.getName().equals("int_lin_eq") && negated(w, vars)) {
      // z - sum(k) w[k] * y[k] = c, the same as sum(k) w[k] * y[k] - z = -c
      w = Arrays.stream(w).map(v -> -v).toArray();
      c = -c;
    }
    IntVar z = null;
    List<IntVar> starts = new ArrayList<>();
    Map<IntVar, Integer> task = new IdentityHashMap<>();
    List<int[]> terms = new ArrayList<>();
    for (int k = 0; k < w.length; k++) {
      if (vars[k].singleton()) {
        // a term fixed by the model moves to the constant
        c -= (long) w[k] * vars[k].value();
        continue;
      }
      Object[] t = term(vars[k]);
      if (t == null || w[k] <= 0) {
        if (w[k] != -1 || z != null) {
          return;
        }
        z = vars[k];
        continue;
      }
      IntVar s = (IntVar) t[0];
      long sign = (Long) t[1];
      long offset = (Long) t[2];
      if (offset < IntDomain.MIN_INT || offset > IntDomain.MAX_INT) {
        return;
      }
      int i =
          task.computeIfAbsent(
              s,
              v -> {
                starts.add(v);
                return starts.size() - 1;
              });
      // w * max(0, s - b) with b = -offset, or w * max(0, b - s) with b = offset
      terms.add(
          sign > 0 ? new int[] {i, (int) -offset, 0, w[k]} : new int[] {i, (int) offset, w[k], 0});
    }
    if (terms.size() < 2 || (z != null && task.containsKey(z)) || (z == null && c < 0)) {
      return;
    }
    UnaryPlan plan = unary ? unaryPlan(starts, terms) : null;
    List<int[]> precedences =
        precedenceCost
            ? precedences(new ArrayList<>(starts), new IdentityHashMap<>(task))
            : List.of();
    if (plan != null && plan.contains(z)) {
      plan = null;
    }
    if (!precedences.isEmpty()) {
      // the starts with the variables the precedences go through
      List<IntVar> all = new ArrayList<>(starts);
      precedences = precedences(all, task);
      if (z != null && all.contains(z)) {
        precedences = List.of();
      }
      starts.addAll(all.subList(starts.size(), all.size()));
    }
    if (precedences.isEmpty() && plan == null) {
      return;
    }
    // z >= sum - c, as a new variable when c is not 0
    IntVar bound = z;
    if (z == null) {
      // sum(k) w[k] * y[k] = c, or at most c
      if (c > IntDomain.MAX_INT) {
        return;
      }
      bound = new IntVar(support.store, (int) c, (int) c);
    } else if (c != 0) {
      long low = (long) z.min() + c;
      long high = (long) z.max() + c;
      if (low < IntDomain.MIN_INT || high > IntDomain.MAX_INT) {
        return;
      }
      bound = new IntVar(support.store, (int) Math.max(0, low), (int) Math.max(0, high));
      support.delayedConstraints.add(
          new LinearInt(new IntVar[] {bound, z}, new int[] {1, -1}, "==", (int) c)
              .setDegreeWeight(0));
    }
    if (!precedences.isEmpty()) {
      PrecedenceCost pc =
          new PrecedenceCost(
              starts.toArray(new IntVar[0]),
              precedences.toArray(new int[0][]),
              terms.toArray(new int[0][]),
              bound);
      // redundant, so degree-based variable selections see the degrees of the model
      pc.setDegreeWeight(0);
      if (support.options.debug()) {
        FzConsole.println(
            "% precedence cost: "
                + starts.size()
                + " tasks, "
                + precedences.size()
                + " precedences, "
                + terms.size()
                + " terms");
      }
      support.delayedConstraints.add(pc);
    }
    if (plan != null) {
      UnaryEarlinessTardiness et =
          new UnaryEarlinessTardiness(
              plan.starts, plan.durations, plan.machines, plan.owner, plan.terms, bound);
      et.setDegreeWeight(0);
      if (support.options.debug()) {
        FzConsole.println(
            "% unary earliness/tardiness: "
                + plan.starts.length
                + " tasks, "
                + plan.machines.length
                + " machines, "
                + plan.terms.length
                + " terms");
      }
      support.delayedConstraints.add(et);
    }
  }

  /** The tasks, machines, owners and terms of a UnaryEarlinessTardiness. */
  private record UnaryPlan(
      IntVar[] starts, int[] durations, int[][] machines, int[] owner, int[][] terms) {

    boolean contains(IntVar z) {
      for (IntVar s : starts) {
        if (s == z) {
          return true;
        }
      }
      return false;
    }
  }

  /**
   * The unary resources with a task that has a cost, over the cost terms on the starts; null when
   * there is none. The tasks of the resources join the starts of the terms (without a cost if they
   * have none); a task with costs counts them on its resource with the most work.
   */
  private UnaryPlan unaryPlan(List<IntVar> termStarts, List<int[]> terms) {
    if (unaryStarts.isEmpty()) {
      return null;
    }
    boolean[] costly = new boolean[termStarts.size()];
    for (int[] t : terms) {
      costly[t[0]] |= t[2] + t[3] > 0;
    }
    Map<IntVar, Integer> position = new IdentityHashMap<>();
    for (int i = 0; i < termStarts.size(); i++) {
      position.put(termStarts.get(i), i);
    }
    List<Integer> chosen = new ArrayList<>();
    for (int r = 0; r < unaryStarts.size(); r++) {
      for (IntVar s : unaryStarts.get(r)) {
        Integer i = position.get(s);
        if (i != null && costly[i]) {
          chosen.add(r);
          break;
        }
      }
    }
    if (chosen.isEmpty()) {
      return null;
    }
    List<IntVar> starts = new ArrayList<>(termStarts);
    Map<IntVar, Integer> index = new IdentityHashMap<>(position);
    List<Integer> durations = new ArrayList<>();
    for (int i = 0; i < starts.size(); i++) {
      durations.add(0);
    }
    int[][] machines = new int[chosen.size()][];
    long[] work = new long[chosen.size()];
    for (int m = 0; m < chosen.size(); m++) {
      IntVar[] s = unaryStarts.get(chosen.get(m));
      int[] d = unaryDurations.get(chosen.get(m));
      machines[m] = new int[s.length];
      for (int k = 0; k < s.length; k++) {
        Integer i = index.get(s[k]);
        if (i == null) {
          i = starts.size();
          index.put(s[k], i);
          starts.add(s[k]);
          durations.add(d[k]);
        } else if (durations.get(i) != 0 && durations.get(i) != d[k]) {
          // the same start with two durations: not one task
          return null;
        }
        durations.set(i, d[k]);
        machines[m][k] = i;
        work[m] += d[k];
      }
      if (starts.size() > MAX_TASKS) {
        return null;
      }
    }
    int n = starts.size();
    int[] owner = new int[n];
    Arrays.fill(owner, -1);
    for (int m = 0; m < machines.length; m++) {
      for (int i : machines[m]) {
        if (owner[i] < 0 || work[m] > work[owner[i]]) {
          owner[i] = m;
        }
      }
    }
    int[] duration = new int[n];
    for (int i = 0; i < n; i++) {
      // a task on no resource keeps a duration of 1, which only its own window uses
      duration[i] = Math.max(1, durations.get(i));
    }
    return new UnaryPlan(
        starts.toArray(new IntVar[0]), duration, machines, owner, terms.toArray(new int[0][]));
  }

  // whether the terms have negative coefficients and the one other variable 1
  private boolean negated(int[] w, IntVar[] vars) {
    int others = 0;
    for (int k = 0; k < w.length; k++) {
      if (vars[k].singleton()) {
        continue;
      }
      if (term(vars[k]) == null) {
        if (w[k] != 1 || ++others > 1) {
          return false;
        }
      } else if (w[k] >= 0) {
        return false;
      }
    }
    return others <= 1;
  }

  // {s, sign, offset} for y = max(0, sign * s + offset), or null
  private Object[] term(IntVar y) {
    IntVar a = hinge.get(y);
    if (a == null) {
      return null;
    }
    Object[] t = affine.get(a);
    if (t != null && !hinge.containsKey(t[0])) {
      return t;
    }
    return new Object[] {a, 1L, 0L};
  }

  /**
   * The precedences between the starts, and the variables without a cost they go through (added to
   * starts), over the difference constraints reachable from the starts; arcs that close a cycle are
   * left out.
   */
  private List<int[]> precedences(List<IntVar> starts, Map<IntVar, Integer> task) {
    Map<IntVar, List<Integer>> incident = new IdentityHashMap<>();
    for (int a = 0; a < diffVars.size(); a++) {
      incident.computeIfAbsent(diffVars.get(a)[0], v -> new ArrayList<>()).add(a);
      incident.computeIfAbsent(diffVars.get(a)[1], v -> new ArrayList<>()).add(a);
    }
    // the variables connected to the starts
    Deque<IntVar> queue = new ArrayDeque<>(starts);
    List<Integer> arcs = new ArrayList<>();
    boolean[] seen = new boolean[diffVars.size()];
    while (!queue.isEmpty()) {
      IntVar v = queue.poll();
      for (int a : incident.getOrDefault(v, List.of())) {
        if (seen[a]) {
          continue;
        }
        seen[a] = true;
        arcs.add(a);
        for (IntVar u : diffVars.get(a)) {
          if (!task.containsKey(u)) {
            if (starts.size() >= MAX_TASKS) {
              return List.of();
            }
            task.put(u, starts.size());
            starts.add(u);
            queue.add(u);
          }
        }
      }
    }
    // keep the arcs that leave the graph acyclic, by an order of insertion check
    int n = starts.size();
    List<List<Integer>> succ = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      succ.add(new ArrayList<>());
    }
    List<int[]> result = new ArrayList<>();
    for (int a : arcs) {
      int i = task.get(diffVars.get(a)[0]);
      int j = task.get(diffVars.get(a)[1]);
      if (reaches(succ, j, i, n)) {
        continue;
      }
      succ.get(i).add(j);
      long lag = diffLags.get(a);
      result.add(new int[] {i, j, (int) lag});
    }
    return result;
  }

  // whether target can be reached from source
  private static boolean reaches(List<List<Integer>> succ, int source, int target, int n) {
    if (source == target) {
      return true;
    }
    boolean[] visited = new boolean[n];
    Deque<Integer> stack = new ArrayDeque<>();
    stack.push(source);
    visited[source] = true;
    while (!stack.isEmpty()) {
      int u = stack.pop();
      for (int v : succ.get(u)) {
        if (v == target) {
          return true;
        }
        if (!visited[v]) {
          visited[v] = true;
          stack.push(v);
        }
      }
    }
    return false;
  }
}
