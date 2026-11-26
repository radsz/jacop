/*
 * PermutedTasksDetector.java
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
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds a chain of tasks whose resources are a permutation, and posts the unary resource of the
 * chain over the starts of the resources. The pattern is the job of an open shop written in the
 * order of its operations: operation j of a job starts at {@code s[j]}, runs on machine {@code
 * m[j]} for {@code d[j] = p[m[j]]} (a functional table or a constant element), the operations
 * follow each other ({@code s[j] + d[j] <= s[j+1]}), the machines are all different and use every
 * machine of their union, and {@code s[j] = t[m[j]]} channels each operation to the start {@code
 * t[k]} of the job on machine k. The tasks {@code (t[k], p[k])} are then the tasks {@code (s[j],
 * d[j])} renamed, so they never overlap: a unary resource over {@code t} with the fixed durations
 * {@code p}, and every {@code t[k]} lies between the start of the first operation and {@code t[k] +
 * p[k] <= s[n-1] + d[n-1]}. Only the chain sees the order of the operations and only the noOverlap
 * of the machines the {@code t}; the element constraints between them propagate nothing until a
 * machine is chosen, so the job alone gave no bound on its machine starts.
 *
 * <p>These are the redundant constraints of a dual model joined by channelling (Cheng, Lee and Wu,
 * "Increasing constraint propagation by redundant modeling: an experience report", Constraints
 * 4(2), 1999), here the job view of the open shop as in Malapert, Cambazard, Guéret, Jussien,
 * Langevin and Rousseau, "An optimal constraint programming approach to the open-shop problem",
 * INFORMS Journal on Computing 24(2), 2012, which posts a disjunctive constraint on every job and
 * every machine. On XCSP 2025 SchedulingOS-gp-10-01 (Guéret-Prins 10 x 10) it proves the optimum
 * 1093 in seconds; without it JaCoP reached 1189 in 240 s.
 *
 * <p>The system property {@code org.jacop.fz.permutedTasks=false} turns it off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class PermutedTasksDetector implements ParserTreeConstants {

  private static final Set<String> GATE_KINDS =
      Set.of("jacop_alldiff", "all_different_int", "fzn_all_different_int");

  // y = array[index - first]; a plain class, since a record would compare its array by identity
  private static final class Element {
    final IntVar[] array;
    final int first;
    final IntVar value;

    Element(IntVar[] array, int first, IntVar value) {
      this.array = array;
      this.first = first;
      this.value = value;
    }
  }

  // y = f(x) for the values of a functional table or a constant element
  private record Function(IntVar y, Map<Integer, Integer> map) {}

  // start + duration <= next, or start + length <= next when duration is null
  private record Precedence(IntVar duration, int length, IntVar next) {}

  // the lists of more variables or values than this are left out
  private static final int MAX_TASKS = 1000;

  private final Support support;

  private final List<IntVar[]> permutations = new ArrayList<>();

  private final Map<IntVar, List<Element>> elements = new IdentityHashMap<>();

  private final Map<IntVar, List<Function>> functions = new IdentityHashMap<>();

  private final Map<IntVar, List<Precedence>> precedences = new IdentityHashMap<>();

  private int posted;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public PermutedTasksDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.permutedTasks is false.
   */
  public static boolean enabled() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.permutedTasks", "true"));
  }

  /**
   * It scans the constraint items of the model and posts the unary resource of every chain of tasks
   * over permuted resources.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    // the permutations are all-different constraints: a model without them is not read
    if (!support.hasConstraint(astTree, GATE_KINDS)) {
      return;
    }
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
    for (IntVar[] m : permutations) {
      chain(m);
    }
    if ((support.options.debug() || support.options.searchStatistics()) && posted > 0) {
      FzConsole.println("%%%mzn-stat: permutedTasks=" + posted + "\n%%%mzn-stat-end");
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar aVar(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_alldiff", "all_different_int", "fzn_all_different_int" -> {
        IntVar[] m = support.getVarArray(child(node, 0));
        if (m.length > 1 && m.length <= MAX_TASKS) {
          permutations.add(m);
        }
      }
      case "jacop_array_var_int_element_nonshifted" -> {
        int first = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));
        element(aVar(node, 0), support.getVarArray(child(node, 1)), aVar(node, 2), first);
      }
      case "array_var_int_element" ->
          element(aVar(node, 0), support.getVarArray(child(node, 1)), aVar(node, 2), 1);
      case "array_int_element" -> {
        int[] c = support.getIntArray(child(node, 1));
        if (c != null && c.length <= MAX_TASKS) {
          Map<Integer, Integer> map = new HashMap<>();
          for (int k = 0; k < c.length; k++) {
            map.put(k + 1, c[k]);
          }
          function(aVar(node, 0), aVar(node, 2), map);
        }
      }
      case "jacop_table_int" -> table(node);
      case "int_lin_le" -> precedence(node);
      default -> {
        // not a part of the pattern
      }
    }
  }

  private void element(IntVar index, IntVar[] array, IntVar value, int first) {
    if (array.length <= MAX_TASKS && !index.singleton()) {
      elements
          .computeIfAbsent(index, k -> new ArrayList<>(1))
          .add(new Element(array, first, value));
    }
  }

  private void function(IntVar x, IntVar y, Map<Integer, Integer> map) {
    if (x != y && !x.singleton()) {
      functions.computeIfAbsent(x, k -> new ArrayList<>(1)).add(new Function(y, map));
    }
  }

  // a table over (x, y) in which every x has one y
  private void table(ASTConstElem node) {
    IntVar[] v = support.getVarArray(child(node, 0));
    if (v.length != 2) {
      return;
    }
    int[] t = support.getIntArray(child(node, 1));
    if (t == null || t.length % 2 != 0 || t.length > 2 * MAX_TASKS) {
      return;
    }
    Map<Integer, Integer> map = new HashMap<>();
    for (int k = 0; k < t.length; k += 2) {
      Integer old = map.put(t[k], t[k + 1]);
      if (old != null && old != t[k + 1]) {
        return;
      }
    }
    function(v[0], v[1], map);
  }

  // s + d - t <= 0, in any order of the terms, or s - t <= -c for a constant duration c
  private void precedence(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    if (a == null || a.length < 2 || a.length > 3) {
      return;
    }
    IntVar[] x = support.getVarArray(child(node, 1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (a.length == 2) {
      if (a[0] == 1 && a[1] == -1 && c <= 0) {
        precedences
            .computeIfAbsent(x[0], k -> new ArrayList<>(1))
            .add(new Precedence(null, -c, x[1]));
      }
      return;
    }
    if (c != 0) {
      return;
    }
    int next = -1;
    for (int k = 0; k < 3; k++) {
      if (a[k] == -1 && next < 0) {
        next = k;
      } else if (a[k] != 1) {
        return;
      }
    }
    if (next < 0) {
      return;
    }
    int p = next == 0 ? 1 : 0;
    int q = 3 - next - p;
    // either of the two others may be the start
    precedences
        .computeIfAbsent(x[p], k -> new ArrayList<>(1))
        .add(new Precedence(x[q], 0, x[next]));
    precedences
        .computeIfAbsent(x[q], k -> new ArrayList<>(1))
        .add(new Precedence(x[p], 0, x[next]));
  }

  // the chain of the tasks on the permuted resources m, when there is one
  private void chain(IntVar[] m) {
    int n = m.length;
    IntDomain union = new IntervalDomain();
    for (IntVar v : m) {
      union.unionAdapt(v.dom());
    }
    if (union.getSize() != n) {
      return;
    }
    // the start of each task: one element over a shared array of starts
    IntVar[] starts = null;
    int first = 0;
    IntVar[] s = new IntVar[n];
    Map<IntVar, Integer> taskOf = new IdentityHashMap<>();
    for (int j = 0; j < n; j++) {
      List<Element> es = elements.get(m[j]);
      if (es == null) {
        return;
      }
      Element found = null;
      for (Element e : es) {
        if (starts == null || (e.first == first && Arrays.equals(e.array, starts))) {
          found = e;
          break;
        }
      }
      if (found == null || taskOf.put(found.value, j) != null) {
        return;
      }
      starts = found.array;
      first = found.first;
      s[j] = found.value;
    }
    // the resources index the starts
    int[] machines = new int[n];
    int k = 0;
    for (ValueEnumeration it = union.valueEnumeration(); it.hasMoreElements(); ) {
      int u = it.nextElement();
      long i = (long) u - first;
      if (i < 0 || i >= starts.length) {
        return;
      }
      machines[k++] = u;
    }
    // the successor of each task and the duration it waits for
    int[] succ = new int[n];
    Arrays.fill(succ, -1);
    IntVar[] d = new IntVar[n];
    int[] length = new int[n];
    boolean[] hasPred = new boolean[n];
    for (int j = 0; j < n; j++) {
      List<Precedence> ps = precedences.get(s[j]);
      if (ps == null) {
        continue;
      }
      for (Precedence p : ps) {
        Integer next = taskOf.get(p.next);
        if (next != null && next != j && !hasPred[next] && succ[j] < 0) {
          succ[j] = next;
          d[j] = p.duration;
          length[j] = p.length;
          hasPred[next] = true;
        }
      }
    }
    int head = -1;
    for (int j = 0; j < n; j++) {
      if (!hasPred[j]) {
        if (head >= 0) {
          return;
        }
        head = j;
      }
    }
    if (head < 0) {
      return;
    }
    int[] order = new int[n];
    int last = head;
    order[0] = head;
    for (int i = 1; i < n; i++) {
      last = succ[last];
      if (last < 0) {
        return;
      }
      order[i] = last;
    }
    if (succ[last] >= 0) {
      return;
    }
    // the duration of every task, the same function of its resource
    Map<Integer, Integer> p = null;
    for (int j = 0; j < n; j++) {
      Map<Integer, Integer> f =
          j != last && d[j] == null ? constant(m[j], length[j]) : duration(m[j], d[j]);
      if (f == null) {
        return;
      }
      if (j == last) {
        d[j] = durationVar(m[j], f);
      }
      for (int u : machines) {
        Integer v = f.get(u);
        if (v == null || v < 0 || (p != null && !v.equals(p.get(u)))) {
          return;
        }
      }
      if (p == null) {
        p = f;
      }
    }
    post(starts, first, machines, p, s[head], s[last], d[last]);
  }

  // the function of the resource m that gives the duration d; d is null for the last task
  private Map<Integer, Integer> duration(IntVar m, IntVar d) {
    List<Function> fs = functions.get(m);
    if (fs == null) {
      return d != null && d.singleton() ? constant(m, d.value()) : null;
    }
    Function found = null;
    for (Function f : fs) {
      if (d == null || f.y == d) {
        if (found != null && d == null) {
          // two durations of the last task, none of them known to be its own
          return null;
        }
        found = f;
      }
    }
    if (found == null && d != null && d.singleton()) {
      return constant(m, d.value());
    }
    return found == null ? null : found.map;
  }

  private static Map<Integer, Integer> constant(IntVar m, int c) {
    Map<Integer, Integer> map = new HashMap<>();
    for (ValueEnumeration it = m.dom().valueEnumeration(); it.hasMoreElements(); ) {
      map.put(it.nextElement(), c);
    }
    return map;
  }

  private IntVar durationVar(IntVar m, Map<Integer, Integer> f) {
    for (Function g : functions.get(m)) {
      if (g.map == f) {
        return g.y;
      }
    }
    throw new IllegalStateException("no duration of " + m);
  }

  // the unary resource over the starts of the machines and the window of the chain
  private void post(
      IntVar[] starts,
      int first,
      int[] machines,
      Map<Integer, Integer> p,
      IntVar head,
      IntVar last,
      IntVar lastDuration) {
    int n = machines.length;
    IntVar[] t = new IntVar[n];
    IntVar[] durations = new IntVar[n];
    IntVar[] use = new IntVar[n];
    IntVar one = new IntVar(support.store, 1, 1);
    Map<Integer, IntVar> constants = new HashMap<>();
    for (int i = 0; i < n; i++) {
      t[i] = starts[machines[i] - first];
      int length = p.get(machines[i]);
      durations[i] = constants.computeIfAbsent(length, v -> new IntVar(support.store, v, v));
      use[i] = one;
    }
    List<Constraint> added = new ArrayList<>();
    added.add(new CumulativeUnary(t, durations, use, one, true));
    for (int i = 0; i < n; i++) {
      // head <= t and t + p <= last + d: the window of the chain
      added.add(new LinearInt(new IntVar[] {head, t[i]}, new int[] {1, -1}, "<=", 0));
      added.add(
          new LinearInt(
              new IntVar[] {t[i], last, lastDuration},
              new int[] {1, -1, -1},
              "<=",
              -p.get(machines[i])));
    }
    for (Constraint c : added) {
      c.setDegreeWeight(0);
      support.delayedConstraints.add(c);
    }
    support.unaryResources.add(new IntVar[][] {t, durations});
    posted++;
    if (support.options.debug()) {
      FzConsole.println("% permuted tasks: unary resource on " + n + " resource starts");
    }
  }
}
