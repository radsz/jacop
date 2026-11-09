/*
 * WeightedCompletionDetector.java
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.LateCount;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.WeightedCompletion;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ASTSolveExpr;
import org.jacop.fz.ASTSolveKind;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds weighted sums of completion times over the tasks of a unary resource and posts {@link
 * WeightedCompletion} on them as a redundant constraint (Kovács and Beck, Constraints 2011).
 *
 * <p>The unary resources are the {@code jacop_cumulative} constraints whose tasks pairwise exceed
 * the capacity ({@code disjunctive} in MiniZinc) and the cliques of the disjunctive clique
 * detection. The sums are {@code int_lin_eq} (and {@code int_lin_le}) with at least three terms. A
 * term a * x with a &gt; 0 is mapped to a task with start s and duration d of the resource when the
 * difference constraints of the model ({@code int_lin_le}, {@code int_lin_eq}, {@code int_le},
 * {@code int_lt} over two variables) give x &ge; s + L: x is s itself, its end, or the end of a
 * later task of the same job, as in single machine models and in job shops whose objective weighs
 * the last task of each job. Then sum(mapped) a * x &ge; sum(tasks) w * (s + d) + sum(mapped) a *
 * (L - d), with w the sum of the coefficients mapped to the task, so a new variable z, defined by
 * the other terms of the sum, bounds the weighted completion time of the resource. The sum must
 * contain the objective of the model among those other terms, with the sign that makes branch and
 * bound lower z, and the objective must not be bounded by a task start itself (as a makespan is),
 * so that sums that only define differences of start times are left alone. With at least two
 * weighted tasks on a resource the constraint is posted on all its tasks, unweighted ones with
 * weight 0. All constraints are still posted as usual, so it only adds pruning.
 *
 * <p>A {@code jacop_cumulative} of capacity above 1 that is not unary is a parallel resource: the
 * constraint gets the resource uses and the capacity and bounds the cost by the Eastman, Even and
 * Isaacs bound (identical machines, Management Science 11(2), 1964) with release dates. Setting
 * {@code org.jacop.fz.weightedCompletion.parallel} to false leaves those resources out.
 *
 * <p>Setting the system property {@code org.jacop.fz.weightedCompletion} to false turns the
 * detection off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class WeightedCompletionDetector implements ParserTreeConstants {

  // longest path relaxations per term, a guard against large difference graphs and positive cycles
  private static final int PATH_BUDGET = 200_000;

  // longest path relaxations over all sums
  private static final long TOTAL_BUDGET = 20_000_000L;

  // the largest number of constraints posted
  private static final int MAX_POSTED = 200;

  // detection on cumulatives of capacity above 1: -Dorg.jacop.fz.weightedCompletion.parallel=false
  private static final String OFF = "false";

  private static final String INT_LIN_EQ = "int_lin_eq";

  private static final boolean PARALLEL =
      !OFF.equalsIgnoreCase(System.getProperty("org.jacop.fz.weightedCompletion.parallel"));

  // detection of counts of late tasks: -Dorg.jacop.fz.lateCount=false turns it off
  private static final boolean LATE =
      !OFF.equalsIgnoreCase(System.getProperty("org.jacop.fz.lateCount"));

  private final Support support;

  // the difference graph, reversed: to -> (from, lag) with to >= from + lag
  private final Map<IntVar, List<Arc>> into = new IdentityHashMap<>();

  private record Arc(IntVar from, int lag) {}

  // the difference graph forward: from -> to, for the variables reachable from a task
  private final Map<IntVar, List<IntVar>> outOf = new IdentityHashMap<>();

  private final Set<IntVar> reachable = Collections.newSetFromMap(new IdentityHashMap<>());

  private long work;

  // 0/1 variables of bool2int: the integer to the Boolean
  private final Map<IntVar, IntVar> boolOf = new IdentityHashMap<>();

  // reified thresholds: b holds exactly when x >= c, from int_le_reif on c and x or int_lt_reif on
  // c - 1 and x
  private final Map<IntVar, Threshold> thresholds = new IdentityHashMap<>();

  private record Threshold(IntVar x, int c) {}

  private final List<Resource> resources = new ArrayList<>();

  // the number of constraint arguments each variable occurs in
  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  // the dominance rule of LateCount where it is safe: -Dorg.jacop.fz.lateCount.dominance=false
  private static final boolean DOMINANCE =
      !OFF.equalsIgnoreCase(System.getProperty("org.jacop.fz.lateCount.dominance"));

  // tasks of a resource: start, duration (its minimum is used), use and capacity (1 if unary)
  // a class, not a record: a record compares array components by reference (Sonar S6218)
  private static final class Resource {
    private final IntVar[] starts;
    private final IntVar[] durations;
    private final int[] uses;
    private final int capacity;

    Resource(IntVar[] starts, IntVar[] durations, int[] uses, int capacity) {
      this.starts = starts;
      this.durations = durations;
      this.uses = uses;
      this.capacity = capacity;
    }

    IntVar[] starts() {
      return starts;
    }

    IntVar[] durations() {
      return durations;
    }

    int[] uses() {
      return uses;
    }

    int capacity() {
      return capacity;
    }
  }

  private final List<ASTConstElem> linears = new ArrayList<>();

  // the objective and 1 to minimize it, -1 to maximize it
  private IntVar objective;
  private int direction;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public WeightedCompletionDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.weightedCompletion is false.
   */
  public static boolean enabled() {
    return !OFF.equalsIgnoreCase(System.getProperty("org.jacop.fz.weightedCompletion"));
  }

  /**
   * It scans the constraint items of the model and posts a WeightedCompletion for each weighted sum
   * of completion times over a unary resource.
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
            // bool2int makes one variable of its two (the Boolean and its 0/1 value)
            for (int a = 0;
                !"bool2int".equals(((ASTConstElem) item).getName()) && a < item.jjtGetNumChildren();
                a++) {
              PartialCopyDetector.countVariables(
                  support, (SimpleNode) item.jjtGetChild(a), occurrences);
            }
          }
        }
      }
    }
    for (IntVar[][] unary : support.unaryResources) {
      int[] one = new int[unary[0].length];
      Arrays.fill(one, 1);
      resources.add(new Resource(unary[0], unary[1], one, 1));
    }
    objective(astTree);
    if (objective == null || resources.isEmpty() || linears.isEmpty()) {
      return;
    }
    // the variables that can bound a completion time: reachable from a start of a resource
    ArrayDeque<IntVar> queue = new ArrayDeque<>();
    for (Resource resource : resources) {
      for (IntVar v : resource.starts()) {
        if (reachable.add(v)) {
          queue.add(v);
        }
      }
    }
    while (!queue.isEmpty()) {
      for (IntVar to : outOf.getOrDefault(queue.poll(), List.of())) {
        if (reachable.add(to)) {
          queue.add(to);
        }
      }
    }
    if (LATE && !thresholds.isEmpty()) {
      int posted = 0;
      for (ASTConstElem node : linears) {
        posted += lateSum(node, MAX_POSTED - posted);
        if (posted >= MAX_POSTED) {
          break;
        }
      }
    }
    if (reachable.contains(objective)) {
      // the objective is itself bounded by a task start, as in a makespan, not a weighted sum
      return;
    }
    int posted = 0;
    for (ASTConstElem node : linears) {
      posted += sum(node, MAX_POSTED - posted);
      if (posted >= MAX_POSTED) {
        break;
      }
    }
  }

  // the variable of minimize (direction 1) or maximize (direction -1), null for satisfy
  private void objective(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() != JJTMODELEND || node.jjtGetNumChildren() == 0) {
        continue;
      }
      SimpleNode item = child(node, 0);
      SimpleNode last = child(item, item.jjtGetNumChildren() - 1);
      if (!(last instanceof ASTSolveKind kind) || last.jjtGetNumChildren() == 0) {
        return;
      }
      direction =
          switch (kind.getKind()) {
            case "minimize" -> 1;
            case "maximize" -> -1;
            default -> 0;
          };
      if (direction != 0 && child(kind, 0) instanceof ASTSolveExpr expr) {
        if (expr.getType() == 0) {
          objective = support.dictionary.getVariable(expr.getIdent());
        } else if (expr.getType() == 1) {
          IntVar[] array = support.dictionary.getVariableArray(expr.getIdent());
          objective =
              array != null && expr.getIndex() >= 0 && expr.getIndex() < array.length
                  ? array[expr.getIndex()]
                  : null;
        }
      }
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_cumulative" -> cumulative(node);
      case "int_lin_le" -> linear(node, false);
      case INT_LIN_EQ -> linear(node, true);
      case "int_le" -> arc(variable(node, 0), variable(node, 1), 0);
      case "int_lt" -> arc(variable(node, 0), variable(node, 1), 1);
      case "int_le_reif" -> threshold(node, 0);
      case "int_lt_reif" -> threshold(node, 1);
      case "bool2int" -> boolOf.put(variable(node, 1), variable(node, 0));
      default -> {
        // not part of a weighted completion time
      }
    }
  }

  // c <= x (plus 1 for <) reified by b, with c a constant
  private void threshold(ASTConstElem node, int strict) {
    IntVar c = variable(node, 0);
    IntVar x = variable(node, 1);
    if (c.singleton() && !x.singleton() && (long) c.value() + strict <= IntDomain.MAX_INT) {
      thresholds.put(variable(node, 2), new Threshold(x, c.value() + strict));
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar variable(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  // a cumulative whose tasks pairwise exceed the capacity is a unary resource, any other one with a
  // capacity above 1 a parallel resource (Eastman, Even and Isaacs)
  private void cumulative(ASTConstElem node) {
    IntVar[] s = support.getVarArray(child(node, 0));
    IntVar[] d = support.getVarArray(child(node, 1));
    IntVar[] r = support.getVarArray(child(node, 2));
    int capacity = variable(node, 3).max();
    List<IntVar> starts = new ArrayList<>();
    List<IntVar> durations = new ArrayList<>();
    List<Integer> uses = new ArrayList<>();
    int least = Integer.MAX_VALUE;
    int count = 0;
    for (int i = 0; i < s.length; i++) {
      if (r[i].min() > 0 && d[i].min() > 0) {
        starts.add(s[i]);
        durations.add(d[i]);
        uses.add(r[i].min());
        count++;
        least = Math.min(least, r[i].min());
      }
    }
    // the two smallest uses exceed the capacity, so every pair does
    if (count < 2) {
      return;
    }
    int second = Integer.MAX_VALUE;
    boolean seen = false;
    for (int i = 0; i < s.length; i++) {
      if (r[i].min() > 0 && d[i].min() > 0) {
        if (!seen && r[i].min() == least) {
          seen = true;
        } else {
          second = Math.min(second, r[i].min());
        }
      }
    }
    IntVar[] taskStarts = starts.toArray(new IntVar[0]);
    IntVar[] taskDurations = durations.toArray(new IntVar[0]);
    if ((long) least + second > capacity) {
      int[] one = new int[count];
      Arrays.fill(one, 1);
      resources.add(new Resource(taskStarts, taskDurations, one, 1));
    } else if (PARALLEL && capacity > 1) {
      long energy = 0;
      for (int i = 0; i < count; i++) {
        energy = Math.max(energy, (long) uses.get(i) * taskDurations[i].min());
      }
      if (energy <= IntDomain.MAX_INT) {
        resources.add(
            new Resource(
                taskStarts,
                taskDurations,
                uses.stream().mapToInt(Integer::intValue).toArray(),
                capacity));
      }
    }
  }

  private void linear(ASTConstElem node, boolean equation) {
    int[] a = support.getIntArray(child(node, 0));
    if (a == null) {
      return;
    }
    if (a.length >= 3) {
      linears.add(node);
      return;
    }
    if (a.length != 2 || a[0] != -a[1] || a[0] == 0) {
      return;
    }
    IntVar[] x = support.getVarArray(child(node, 1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int k = Math.abs(a[0]);
    // k * (x0 - x1) <= c, so x1 >= x0 - floor(c / k); with a negative a[0] the roles swap
    IntVar from = x[a[0] > 0 ? 0 : 1];
    IntVar to = x[a[0] > 0 ? 1 : 0];
    arc(from, to, -Math.floorDiv(c, k));
    if (equation && c % k == 0) {
      arc(to, from, c / k);
    }
  }

  // an arc of the difference graph: head >= tail + lag
  private void arc(IntVar tail, IntVar head, int lag) {
    if (tail != head) {
      into.computeIfAbsent(head, k -> new ArrayList<>()).add(new Arc(tail, lag));
      outOf.computeIfAbsent(tail, k -> new ArrayList<>()).add(head);
    }
  }

  /**
   * It returns, for every variable v with a path of difference constraints to x, the largest L with
   * x &ge; v + L that the paths give (x itself with 0).
   */
  private Map<IntVar, Long> longestTo(IntVar x) {
    Map<IntVar, Long> dist = new IdentityHashMap<>();
    dist.put(x, 0L);
    ArrayDeque<IntVar> queue = new ArrayDeque<>();
    queue.add(x);
    int steps = 0;
    while (!queue.isEmpty() && steps < PATH_BUDGET && work < TOTAL_BUDGET) {
      IntVar v = queue.poll();
      long dv = dist.get(v);
      for (Arc arc : into.getOrDefault(v, List.of())) {
        steps++;
        work++;
        long candidate = dv + arc.lag;
        Long old = dist.get(arc.from);
        if (old == null || candidate > old) {
          dist.put(arc.from, candidate);
          queue.add(arc.from);
        }
      }
    }
    // with the budget spent the distances are still valid lower bounds of the longest paths
    return dist;
  }

  /**
   * It posts the constraint for each resource that the sum weighs.
   *
   * @return the number of constraints posted.
   */
  private int sum(ASTConstElem node, int room) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    if (a.length != x.length) {
      return 0;
    }
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    boolean equation = node.getName().equals(INT_LIN_EQ);

    // at least two terms of one sign that a task can bound
    int positive = 0;
    int negative = 0;
    for (int k = 0; k < x.length; k++) {
      if (!x[k].singleton() && reachable.contains(x[k])) {
        positive += a[k] > 0 ? 1 : 0;
        negative += a[k] < 0 ? 1 : 0;
      }
    }
    if (positive < 2 && (negative < 2 || !equation)) {
      return 0;
    }
    List<Map<IntVar, Long>> paths = new ArrayList<>();
    for (IntVar v : x) {
      paths.add(v.singleton() || !reachable.contains(v) ? Map.of() : longestTo(v));
    }

    int count = 0;
    for (int sign : equation ? new int[] {1, -1} : new int[] {1}) {
      for (Resource resource : resources) {
        if (count < room && post(a, x, c, sign, paths, resource)) {
          count++;
        }
      }
    }
    return count;
  }

  /**
   * It maps the terms sign * a[k] * x[k] &gt; 0 to tasks of the resource and posts the constraint
   * when at least two tasks get a weight and a term is left for the cost.
   */
  private boolean post(
      int[] a, IntVar[] x, int c, int sign, List<Map<IntVar, Long>> paths, Resource resource) {
    IntVar[] starts = resource.starts();
    IntVar[] durations = resource.durations();
    int n = starts.length;
    long[] weight = new long[n];
    long offset = 0;
    boolean[] mapped = new boolean[x.length];
    int weighted = 0;
    for (int k = 0; k < x.length; k++) {
      long coefficient = (long) sign * a[k];
      if (coefficient <= 0) {
        continue;
      }
      Map<IntVar, Long> dist = paths.get(k);
      // the task whose start gives the largest static bound on x[k]
      int best = -1;
      long bestBound = Long.MIN_VALUE;
      long bestLag = 0;
      for (int t = 0; t < n; t++) {
        Long lag = dist.get(starts[t]);
        if (lag != null && starts[t].min() + lag > bestBound) {
          best = t;
          bestBound = starts[t].min() + lag;
          bestLag = lag;
        }
      }
      if (best < 0) {
        continue;
      }
      mapped[k] = true;
      if (weight[best] == 0) {
        weighted++;
      }
      weight[best] += coefficient;
      offset += coefficient * (bestLag - durations[best].min());
    }
    if (weighted < 2) {
      return false;
    }

    // z = sign * (c - sum(others) a * x) - offset >= sum(mapped) sign * a * x - offset
    List<IntVar> others = new ArrayList<>();
    List<Integer> otherWeights = new ArrayList<>();
    long constant = (long) sign * c - offset;
    long low = constant;
    long high = constant;
    for (int k = 0; k < x.length; k++) {
      if (mapped[k]) {
        continue;
      }
      long b = -(long) sign * a[k];
      if (x[k].singleton()) {
        constant += b * x[k].value();
        low += b * x[k].value();
        high += b * x[k].value();
        continue;
      }
      others.add(x[k]);
      otherWeights.add(sign * a[k]);
      low += Math.min(b * x[k].min(), b * x[k].max());
      high += Math.max(b * x[k].min(), b * x[k].max());
    }
    // the objective is among the other terms, so its bound in branch and bound bounds z from above
    boolean bounded = false;
    for (int k = 0; k < x.length; k++) {
      if (!mapped[k] && x[k] == objective && (long) sign * a[k] * direction < 0) {
        bounded = true;
      }
    }
    if (!bounded) {
      return false;
    }
    int[] w = new int[n];
    int[] d = new int[n];
    for (int t = 0; t < n; t++) {
      if (weight[t] > IntDomain.MAX_INT) {
        return false;
      }
      w[t] = (int) weight[t];
      d[t] = durations[t].min();
    }
    if (high > IntDomain.MAX_INT
        || low < IntDomain.MIN_INT
        || low > high
        || constant > IntDomain.MAX_INT
        || constant < IntDomain.MIN_INT) {
      return false;
    }
    IntVar z = new IntVar(support.store, (int) low, (int) high);
    // sum(others) sign * a * x + z = sign * c - offset
    IntVar[] list = new IntVar[others.size() + 1];
    int[] coefficients = new int[others.size() + 1];
    for (int j = 0; j < others.size(); j++) {
      list[j] = others.get(j);
      coefficients[j] = otherWeights.get(j);
    }
    list[others.size()] = z;
    coefficients[others.size()] = 1;
    support.delayedConstraints.add(
        new LinearInt(list, coefficients, "==", (int) constant).setDegreeWeight(0));
    WeightedCompletion wc =
        resource.capacity() == 1
            ? new WeightedCompletion(starts, d, w, z)
            : new WeightedCompletion(starts, d, resource.uses(), w, resource.capacity(), z);
    // redundant, so degree-based variable selections see the degrees of the model
    wc.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant " + wc);
    }
    support.delayedConstraints.add(wc);
    return true;
  }

  /**
   * It posts {@link LateCount} for each unary resource whose tasks the sum counts late: a term a *
   * y with a &gt; 0 where y is a 0/1 variable (through bool2int) of a Boolean b that holds exactly
   * when x &ge; c, and x &ge; s + L for the start s of a task by the difference constraints. Then s
   * &ge; c - L implies b, so the task is late for the due date c - L + d - 1 (d its least duration)
   * only if b holds, and a * y counts it at least once.
   *
   * @return the number of constraints posted.
   */
  private int lateSum(ASTConstElem node, int room) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    if (a.length != x.length) {
      return 0;
    }
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    boolean equation = node.getName().equals(INT_LIN_EQ);
    Threshold[] threshold = new Threshold[x.length];
    List<Map<IntVar, Long>> paths = new ArrayList<>();
    int candidates = 0;
    for (int k = 0; k < x.length; k++) {
      IntVar y = x[k];
      Threshold t = y.min() >= 0 && y.max() <= 1 ? thresholds.get(boolOf.getOrDefault(y, y)) : null;
      threshold[k] = t;
      paths.add(t == null ? Map.of() : longestTo(t.x()));
      candidates += t == null ? 0 : 1;
    }
    if (candidates < 2) {
      return 0;
    }
    int count = 0;
    for (int sign : equation ? new int[] {1, -1} : new int[] {1}) {
      for (Resource resource : resources) {
        if (count < room
            && resource.capacity() == 1
            && postLate(a, x, c, sign, threshold, paths, resource)) {
          count++;
        }
      }
    }
    return count;
  }

  /**
   * It tells whether the dominance rule of LateCount keeps an optimal solution: every task of the
   * resource is counted, with one weight, by a Boolean that holds exactly when its start passes a
   * threshold; each start occurs only in the resource and in that test, each Boolean (with its 0/1
   * variable of bool2int) only there and in the sum; the durations are fixed, the domains of the
   * starts are intervals and each start can go up to max(r) + sum(p) - p, so the late tasks fit
   * after the on time ones.
   */
  private boolean dominanceSafe(
      Resource resource,
      int[] a,
      IntVar[] x,
      int sign,
      Threshold[] threshold,
      int[] term,
      int[] d) {
    IntVar[] starts = resource.starts();
    int n = starts.length;
    long maxRelease = Long.MIN_VALUE;
    long total = 0;
    for (int t = 0; t < n; t++) {
      if (!resource.durations()[t].singleton() || resource.uses()[t] != 1) {
        return false;
      }
      maxRelease = Math.max(maxRelease, starts[t].min());
      total += d[t];
    }
    int weight = sign * a[term[0]];
    for (int t = 0; t < n; t++) {
      IntVar s = starts[t];
      int k = term[t];
      IntVar y = x[k];
      IntVar b = boolOf.getOrDefault(y, y);
      if (sign * a[k] != weight
          || threshold[k].x() != s
          || occurrences.getOrDefault(s, 0) != 2
          || b == y && occurrences.getOrDefault(y, 0) != 2
          || b != y && (occurrences.getOrDefault(y, 0) != 1 || occurrences.getOrDefault(b, 0) != 1)
          || s.domain.getSize() != (long) s.max() - s.min() + 1
          || s.max() < maxRelease + total - d[t]) {
        return false;
      }
    }
    for (int t = 0; t < n; t++) {
      for (int u = t + 1; u < n; u++) {
        if (starts[t] == starts[u]) {
          return false;
        }
      }
    }
    return true;
  }

  private boolean postLate(
      int[] a,
      IntVar[] x,
      int c,
      int sign,
      Threshold[] threshold,
      List<Map<IntVar, Long>> paths,
      Resource resource) {
    IntVar[] starts = resource.starts();
    int n = starts.length;
    int[] d = new int[n];
    int[] due = new int[n];
    Arrays.fill(due, Integer.MAX_VALUE);
    boolean[] taken = new boolean[n];
    boolean[] mapped = new boolean[x.length];
    int[] term = new int[n];
    int count = 0;
    for (int t = 0; t < n; t++) {
      d[t] = resource.durations()[t].min();
    }
    for (int k = 0; k < x.length; k++) {
      if (threshold[k] == null || (long) sign * a[k] <= 0) {
        continue;
      }
      Map<IntVar, Long> dist = paths.get(k);
      for (int t = 0; t < n; t++) {
        Long lag = dist.get(starts[t]);
        if (lag == null || taken[t]) {
          continue;
        }
        long date = threshold[k].c() - lag + d[t] - 1;
        if (date < IntDomain.MIN_INT || date > IntDomain.MAX_INT) {
          continue;
        }
        taken[t] = true;
        mapped[k] = true;
        term[t] = k;
        due[t] = (int) date;
        count++;
        break;
      }
    }
    if (count < 2) {
      return false;
    }
    // z = sign * (c - sum(others) a * x) >= sum(mapped) sign * a * y >= number of late tasks
    List<IntVar> others = new ArrayList<>();
    List<Integer> otherWeights = new ArrayList<>();
    long constant = (long) sign * c;
    long low = constant;
    long high = constant;
    boolean bounded = false;
    for (int k = 0; k < x.length; k++) {
      if (mapped[k]) {
        continue;
      }
      long b = -(long) sign * a[k];
      if (x[k].singleton()) {
        constant += b * x[k].value();
        low += b * x[k].value();
        high += b * x[k].value();
        continue;
      }
      if (x[k] == objective && (long) sign * a[k] * direction < 0) {
        bounded = true;
      }
      others.add(x[k]);
      otherWeights.add(sign * a[k]);
      low += Math.min(b * x[k].min(), b * x[k].max());
      high += Math.max(b * x[k].min(), b * x[k].max());
    }
    low = Math.max(low, 0);
    if (!bounded
        || high > IntDomain.MAX_INT
        || low > high
        || constant > IntDomain.MAX_INT
        || constant < IntDomain.MIN_INT) {
      return false;
    }
    IntVar z = new IntVar(support.store, (int) low, (int) high);
    IntVar[] list = new IntVar[others.size() + 1];
    int[] coefficients = new int[others.size() + 1];
    for (int j = 0; j < others.size(); j++) {
      list[j] = others.get(j);
      coefficients[j] = otherWeights.get(j);
    }
    list[others.size()] = z;
    coefficients[others.size()] = 1;
    support.delayedConstraints.add(
        new LinearInt(list, coefficients, "==", (int) constant).setDegreeWeight(0));
    boolean dominance =
        DOMINANCE && count == n && dominanceSafe(resource, a, x, sign, threshold, term, d);
    LateCount lc = new LateCount(starts, d, due, z, dominance);
    lc.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant " + lc);
    }
    support.delayedConstraints.add(lc);
    return true;
  }
}
