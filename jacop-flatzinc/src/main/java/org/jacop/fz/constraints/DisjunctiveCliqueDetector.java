/*
 * DisjunctiveCliqueDetector.java
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
import org.jacop.constraints.Constraint;
import org.jacop.constraints.InterDistance;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.UnaryTransition;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.presolve.DisjunctiveCliques;
import org.jacop.presolve.InferredCumulatives;

/**
 * It finds sets of tasks that can never overlap and posts a {@link CumulativeUnary} on each of them
 * as a redundant constraint, following Sidorov, Marijnissen and Demirović, "Unite and Lead: Finding
 * Disjunctive Cliques for Scheduling Problems", CP 2025. The search for the sets is done by {@link
 * DisjunctiveCliques}; this class reads the facts from the FlatZinc model:
 *
 * <ul>
 *   <li>pairs of tasks of one {@code jacop_cumulative} whose resource uses exceed its capacity,
 *   <li>disjunctions {@code s1 + d1 <= s2 \/ s2 + d2 <= s1}, which MiniZinc flattens into a two
 *       literal {@code bool_clause} (or {@code array_bool_or}, or {@code bool_not}) over literals
 *       defined by {@code int_lin_le_imp} or {@code int_lin_le_reif} (also {@code int_le} and
 *       {@code int_lt}), as in job shop models and the redundant constraints of RCPSP models,
 *   <li>difference constraints {@code s1 + c <= s2} ({@code int_lin_le}, {@code int_lin_eq}, {@code
 *       int_le}, {@code int_lt}) between start times.
 * </ul>
 *
 * <p>The tasks of a disjunction are the start variables with the distances of the disjunction as
 * durations. A cumulative whose tasks are all pairwise disjoint is already a unary resource, so its
 * pairs need no clique. All constraints of the model are still posted as usual, so the unary
 * resources only add pruning; they have degree weight 0, so they do not change the static degrees
 * that variable selections such as most_constrained read.
 *
 * <p>In flexible job shops a disjunction holds only when two tasks run on the same machine: a three
 * literal {@code bool_clause} {@code s1 + d1 <= s2 \/ s2 + d2 <= s1 \/ m1 != m2}, where the last
 * literal is defined by {@code int_ne_imp}, {@code int_ne_reif}, {@code int_lin_ne_imp} or {@code
 * int_lin_ne_reif}. When the tasks of such disjunctions share one machine variable each, for every
 * machine {@code v} the tasks that are pairwise conditionally disjoint (or disjoint anyway) get a
 * {@link CumulativeUnary} with optional tasks, task {@code t} present when {@code m_t = v}, as the
 * unary resource with optional activities studied by P. Vilím, R. Barták and O. Čepek, "Extension
 * of O(n log n) filtering algorithms for the unary resource constraint to optional activities",
 * Constraints 10(4), 2005, 403-425. {@code org.jacop.fz.optionalUnary=false} turns this off.
 *
 * <p>Setting the system property {@code org.jacop.fz.disjunctiveCliques} to false turns the
 * detection off.
 *
 * <p>With the system property {@code org.jacop.fz.inferredCumulatives} not set to false (on by
 * default) it also posts the redundant cumulatives that {@link InferredCumulatives} infers by
 * lifting covers of the cumulatives with fixed capacities and the disjoint pairs (Sidorov, "On
 * Inferring Cumulative Constraints", CP 2026). {@code org.jacop.fz.inferredCumulatives.covers}
 * (100) and {@code org.jacop.fz.inferredCumulatives.out} (5) are the paper's N_cover and N_out;
 * {@code org.jacop.fz.inferredCumulatives.disjoint} (true) also lifts over the pairs of tasks that
 * the precedences and disjunctions keep apart, which the paper does not. {@code
 * org.jacop.fz.inferredCumulatives.useful} (true) posts only those whose capacity bound {@code
 * sum(d_i * pi_i) / pi_0} exceeds that of every input cumulative and clique found.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class DisjunctiveCliqueDetector implements ParserTreeConstants {

  private final Support support;

  private final DisjunctiveCliques cliques = new DisjunctiveCliques();

  // b -> to >= from + lag, for the literals of linear constraints over two variables
  private record Implied(IntVar from, IntVar to, int lag) {}

  private final Map<IntVar, List<Implied>> implied = new IdentityHashMap<>();

  private final List<IntVar[]> clauses = new ArrayList<>();

  // b -> x != y, for the literals of disequalities between two variables
  private final Map<IntVar, IntVar[]> differs = new IdentityHashMap<>();

  // three literal clauses, candidates for disjunctions that hold when two assignments are equal
  private final List<IntVar[]> clauses3 = new ArrayList<>();

  // a task of a conditional disjunction: a start and its length
  private record Job(IntVar start, int length) {}

  // a disjunction between two tasks that holds when their assignment variables are equal
  private record Optional(Job a, Job b, IntVar x, IntVar y) {}

  private final List<Optional> optionals = new ArrayList<>();

  // the cumulatives with a fixed capacity: tasks, least uses and capacity
  private static final String FALSE = "false";

  // a cumulative with a fixed capacity, as rows over the task indices; compared by identity
  private static final class Row {
    final int[] tasks;
    final int[] use;
    final int capacity;

    Row(int[] tasks, int[] use, int capacity) {
      this.tasks = tasks;
      this.use = use;
      this.capacity = capacity;
    }
  }

  private final List<Row> rows = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public DisjunctiveCliqueDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.disjunctiveCliques is false.
   */
  public static boolean enabled() {
    return !FALSE.equalsIgnoreCase(System.getProperty("org.jacop.fz.disjunctiveCliques"));
  }

  /**
   * It tells if the inference of redundant cumulatives is on.
   *
   * @return false if the system property org.jacop.fz.inferredCumulatives is false.
   */
  public static boolean inferredEnabled() {
    return !FALSE.equalsIgnoreCase(System.getProperty("org.jacop.fz.inferredCumulatives"));
  }

  /**
   * It scans the constraint items of the model and posts a unary resource for each clique of
   * disjoint tasks.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    long start = System.nanoTime();
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
    for (IntVar[] c : clauses) {
      disjunction(c[0], c[1]);
    }
    for (IntVar[] c : clauses3) {
      for (int k = 0; k < 3; k++) {
        IntVar[] xy = differs.get(c[k]);
        if (xy != null) {
          optionalDisjunction(c[(k + 1) % 3], c[(k + 2) % 3], xy[0], xy[1]);
        }
      }
    }
    List<int[]> found = cliques.cliques();
    if (support.options.debug()) {
      FzConsole.println(
          "% disjunctive cliques: "
              + cliques.size()
              + " tasks, "
              + found.size()
              + " cliques, "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
    if (enabled()) {
      post(found);
      if (!FALSE.equalsIgnoreCase(System.getProperty("org.jacop.fz.optionalUnary"))) {
        postOptional();
      }
    }
    if (inferredEnabled()) {
      infer(found);
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_cumulative" -> cumulative(node);
      case "int_lin_le" -> linear(node, null, false);
      case "int_lin_eq" -> linear(node, null, true);
      case "int_lin_le_imp", "int_lin_le_reif" -> linear(node, aVar(node, 3), false);
      case "int_le" -> difference(aVar(node, 0), aVar(node, 1), 0, null);
      case "int_lt" -> difference(aVar(node, 0), aVar(node, 1), 1, null);
      case "int_le_imp", "int_le_reif" ->
          difference(aVar(node, 0), aVar(node, 1), 0, aVar(node, 2));
      case "int_lt_imp", "int_lt_reif" ->
          difference(aVar(node, 0), aVar(node, 1), 1, aVar(node, 2));
      case "bool_clause" -> {
        IntVar[] pos = support.getVarArray(child(node, 0));
        if (pos.length == 2 && support.getVarArray(child(node, 1)).length == 0) {
          clauses.add(pos);
        } else if (pos.length == 3 && support.getVarArray(child(node, 1)).length == 0) {
          clauses3.add(pos);
        }
      }
      case "int_ne_imp", "int_ne_reif" ->
          differs.put(aVar(node, 2), new IntVar[] {aVar(node, 0), aVar(node, 1)});
      case "int_lin_ne_imp", "int_lin_ne_reif" -> {
        int[] a = support.getIntArray(child(node, 0));
        // -a[1] in long: [MIN_VALUE, MIN_VALUE] weighs x + y, not x - y
        if (a != null
            && a.length == 2
            && a[0] == -(long) a[1]
            && a[0] != 0
            && support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) == 0) {
          IntVar[] x = support.getVarArray(child(node, 1));
          differs.put(aVar(node, 3), new IntVar[] {x[0], x[1]});
        }
      }
      case "array_bool_or" -> {
        IntVar[] pos = support.getVarArray(child(node, 0));
        if (pos.length == 2 && aVar(node, 1).singleton(1)) {
          clauses.add(pos);
        }
      }
      case "bool_not" -> clauses.add(new IntVar[] {aVar(node, 0), aVar(node, 1)});
      default -> {
        // not a fact about disjoint tasks
      }
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar aVar(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void cumulative(ASTConstElem node) {
    IntVar[] s = support.getVarArray(child(node, 0));
    IntVar[] d = support.getVarArray(child(node, 1));
    IntVar[] r = support.getVarArray(child(node, 2));
    int capacity = aVar(node, 3).max();
    int[] tasks = new int[s.length];
    int[] use = new int[s.length];
    int n = 0;
    for (int i = 0; i < s.length; i++) {
      int t = r[i].min() > 0 ? cliques.task(s[i], d[i]) : -1;
      if (t >= 0) {
        tasks[n] = t;
        use[n++] = r[i].min();
      }
    }
    if (n > 1 && aVar(node, 3).singleton()) {
      rows.add(new Row(Arrays.copyOf(tasks, n), Arrays.copyOf(use, n), capacity));
    }
    boolean unary = n > 1;
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if ((long) use[i] + use[j] > capacity) {
          cliques.conflict(tasks[i], tasks[j]);
        } else {
          unary = false;
        }
      }
    }
    if (unary) {
      cliques.unary(Arrays.copyOf(tasks, n));
    }
  }

  // a*x + b*y <= c (or = c) with b = -a: a difference constraint between x and y; -a[1] in long,
  // since [MIN_VALUE, MIN_VALUE] weighs x + y
  private void linear(ASTConstElem node, IntVar literal, boolean equation) {
    int[] a = support.getIntArray(child(node, 0));
    if (a == null || a.length != 2 || a[0] != -(long) a[1] || a[0] == 0) {
      return;
    }
    IntVar[] x = support.getVarArray(child(node, 1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int k = Math.abs(a[0]);
    // k * (x0 - x1) <= c, so x1 >= x0 - floor(c / k); with a negative a[0] the roles swap
    IntVar from = a[0] > 0 ? x[0] : x[1];
    IntVar to = a[0] > 0 ? x[1] : x[0];
    difference(from, to, -Math.floorDiv(c, k), literal);
    if (equation && c % k == 0) {
      difference(to, from, c / k, literal);
    }
  }

  // to >= from + lag, unconditionally (literal null) or when the literal is true
  private void difference(IntVar from, IntVar to, int lag, IntVar literal) {
    if (literal == null) {
      cliques.precedence(from, to, lag);
    } else {
      implied.computeIfAbsent(literal, k -> new ArrayList<>()).add(new Implied(from, to, lag));
    }
  }

  // b1 \/ b2 where b1 orders two starts one way and b2 the other way
  private void disjunction(IntVar b1, IntVar b2) {
    List<Implied> first = implied.get(b1);
    List<Implied> second = implied.get(b2);
    if (first == null || second == null) {
      return;
    }
    for (Implied p : first) {
      for (Implied q : second) {
        if (p.from == q.to && p.to == q.from && p.lag > 0 && q.lag > 0) {
          cliques.task(p.from, p.lag);
          cliques.task(q.from, q.lag);
          cliques.disjunction(p.from, p.lag, q.from, q.lag);
        }
      }
    }
  }

  // b1 \/ b2 \/ x != y where b1 orders two starts one way and b2 the other way
  private void optionalDisjunction(IntVar b1, IntVar b2, IntVar x, IntVar y) {
    List<Implied> first = implied.get(b1);
    List<Implied> second = implied.get(b2);
    if (first == null || second == null || x == y || x.singleton() || y.singleton()) {
      return;
    }
    for (Implied p : first) {
      for (Implied q : second) {
        if (p.from == q.to && p.to == q.from && p.lag > 0 && q.lag > 0) {
          // the tasks are known to the cliques, which order them by the precedences
          cliques.task(p.from, p.lag);
          cliques.task(q.from, q.lag);
          optionals.add(new Optional(new Job(p.from, p.lag), new Job(q.from, q.lag), x, y));
        }
      }
    }
  }

  /**
   * Posts a unary resource with optional tasks for each value of the assignment variables of
   * disjunctions that hold when two tasks are assigned to the same machine, {@code s1 + d1 <= s2 \/
   * s2 + d2 <= s1 \/ m1 != m2}, as in flexible job shop models: the tasks that may take value v
   * form a resource on which task i is present when {@code m_i = v}. A task's assignment variable
   * is the one its disjunctions share; a group holds only tasks every pair of which has such a
   * disjunction.
   */
  private void postOptional() {
    if (optionals.isEmpty()) {
      return;
    }
    // the assignment variable of a task: the one common to all its conditional disjunctions
    Map<Job, IntVar> assignment = new HashMap<>();
    Map<Job, List<Optional>> byJob = new HashMap<>();
    for (Optional o : optionals) {
      byJob.computeIfAbsent(o.a, k -> new ArrayList<>()).add(o);
      byJob.computeIfAbsent(o.b, k -> new ArrayList<>()).add(o);
    }
    for (Map.Entry<Job, List<Optional>> e : byJob.entrySet()) {
      IntVar common = null;
      boolean ok = true;
      List<IntVar> candidates = new ArrayList<>();
      Optional f = e.getValue().get(0);
      candidates.add(f.x);
      candidates.add(f.y);
      for (Optional o : e.getValue()) {
        candidates.removeIf(v -> v != o.x && v != o.y);
      }
      if (candidates.size() == 1) {
        common = candidates.get(0);
      } else {
        ok = false;
      }
      if (ok) {
        assignment.put(e.getKey(), common);
      }
    }
    // the pairs whose disjunction holds when their assignments are equal
    Map<Job, Map<Job, Boolean>> pairs = new HashMap<>();
    for (Optional o : optionals) {
      IntVar xa = assignment.get(o.a);
      IntVar xb = assignment.get(o.b);
      if (xa == null || xb == null || xa == xb) {
        continue;
      }
      if (xa == o.x && xb == o.y || xa == o.y && xb == o.x) {
        pairs.computeIfAbsent(o.a, k -> new HashMap<>()).put(o.b, true);
        pairs.computeIfAbsent(o.b, k -> new HashMap<>()).put(o.a, true);
      }
    }
    List<Job> jobs = new ArrayList<>(pairs.keySet());
    // a deterministic order: by start variable index and length
    jobs.sort(
        (u, v) ->
            u.start.index() != v.start.index()
                ? Integer.compare(u.start.index(), v.start.index())
                : Integer.compare(u.length, v.length));
    java.util.TreeSet<Integer> values = new java.util.TreeSet<>();
    for (Job j : jobs) {
      for (org.jacop.core.ValueEnumeration en = assignment.get(j).dom().valueEnumeration();
          en.hasMoreElements(); ) {
        values.add(en.nextElement());
      }
    }
    IntVar one = new IntVar(support.store, 1, 1);
    Map<Integer, IntVar> lengths = new HashMap<>();
    Map<IntVar, Map<Integer, IntVar>> present = new IdentityHashMap<>();
    int posted = 0;
    for (int v : values) {
      List<Job> left = new ArrayList<>();
      for (Job j : jobs) {
        if (assignment.get(j).domain.contains(v)) {
          left.add(j);
        }
      }
      while (left.size() > 2) {
        List<Job> group = new ArrayList<>();
        List<Job> rest = new ArrayList<>();
        for (Job j : left) {
          boolean fits = true;
          for (Job g : group) {
            if (!pairs.get(g).containsKey(j) && !disjoint(g, j)) {
              fits = false;
              break;
            }
          }
          if (fits) {
            group.add(j);
          } else {
            rest.add(j);
          }
        }
        left = rest;
        if (group.size() < 3) {
          continue;
        }
        IntVar[] st = new IntVar[group.size()];
        IntVar[] du = new IntVar[group.size()];
        IntVar[] re = new IntVar[group.size()];
        for (int k = 0; k < st.length; k++) {
          Job j = group.get(k);
          st[k] = j.start;
          du[k] = lengths.computeIfAbsent(j.length, l -> new IntVar(support.store, l, l));
          IntVar x = assignment.get(j);
          re[k] =
              present
                  .computeIfAbsent(x, k2 -> new HashMap<>())
                  .computeIfAbsent(
                      v,
                      val -> {
                        org.jacop.core.BooleanVar b = new org.jacop.core.BooleanVar(support.store);
                        support.pose(
                            new org.jacop.constraints.Reified(
                                new org.jacop.constraints.XeqC(x, val), b));
                        return b;
                      });
        }
        Constraint unary = new CumulativeUnary(st, du, re, one, true);
        unary.setDegreeWeight(0);
        support.delayedConstraints.add(unary);
        posted++;
        if (support.options.debug()) {
          FzConsole.println(
              "% redundant unary resource with optional tasks on "
                  + st.length
                  + " tasks for assignment value "
                  + v);
        }
      }
    }
    optionalResources = posted;
  }

  private int optionalResources;

  // whether the precedences or the unconditional disjunctions keep two tasks apart
  private boolean disjoint(Job a, Job b) {
    long[][] rows = cliques.disjoint();
    if (rows == null) {
      return false;
    }
    int i = cliques.task(a.start, a.length);
    int j = cliques.task(b.start, b.length);
    return i >= 0 && j >= 0 && i < rows.length && (rows[i][j >>> 6] & (1L << (j & 63))) != 0;
  }

  private void post(List<int[]> found) {
    if (found.isEmpty()) {
      return;
    }
    IntVar one = new IntVar(support.store, 1, 1);
    Map<Integer, IntVar> constants = new HashMap<>();
    for (int[] clique : found) {
      IntVar[] s = new IntVar[clique.length];
      IntVar[] d = new IntVar[clique.length];
      IntVar[] r = new IntVar[clique.length];
      for (int k = 0; k < clique.length; k++) {
        int t = clique[k];
        s[k] = cliques.start(t);
        IntVar dv = cliques.durationVar(t);
        d[k] =
            dv != null
                ? dv
                : constants.computeIfAbsent(
                    cliques.minDuration(t), v -> new IntVar(support.store, v, v));
        r[k] = one;
      }
      int[][] tt = cliques.transitions(clique);
      boolean setups = Arrays.stream(tt).flatMapToInt(Arrays::stream).anyMatch(t -> t > 0);
      // with setup times in the disjunctions the unary resource counts them; tasks of one fixed
      // length without setups are an inter-distance, whose propagator is bounds consistent
      int length = equalLength(d);
      Constraint unary;
      if (setups) {
        unary = new UnaryTransition(s, d, tt);
      } else if (length > 1 && !FALSE.equals(GlobalConstraints.interDistanceMode())) {
        unary = new InterDistance(s, length);
      } else {
        unary = new CumulativeUnary(s, d, r, one, true);
      }
      // redundant, so degree-based variable selections see the degrees of the model
      unary.setDegreeWeight(0);
      if (support.options.debug()) {
        FzConsole.println(
            "% redundant "
                + (unary instanceof InterDistance ? "inter-distance" : "unary resource")
                + " on "
                + clique.length
                + " tasks"
                + (setups ? " with transition times" : ""));
      }
      support.delayedConstraints.add(unary);
      support.unaryResources.add(new IntVar[][] {s, d});
    }
  }

  // posts the cumulatives inferred by lifting covers of the resources (Sidorov, CP 2026)
  private void infer(List<int[]> found) {
    long start = System.nanoTime();
    int n = cliques.size();
    if (rows.isEmpty() || n < 2 || n > InferredCumulatives.DEFAULT_MAX_TASKS) {
      return;
    }
    int[] duration = new int[n];
    for (int t = 0; t < n; t++) {
      duration[t] = cliques.minDuration(t);
    }
    InferredCumulatives inference = new InferredCumulatives(duration);
    for (Row row : rows) {
      inference.resource(row.tasks, row.use, row.capacity);
    }
    if (!FALSE.equals(System.getProperty("org.jacop.fz.inferredCumulatives.disjoint"))) {
      inference.disjoint(cliques.disjoint());
    }
    int covers = Integer.getInteger("org.jacop.fz.inferredCumulatives.covers", 100);
    int out = Integer.getInteger("org.jacop.fz.inferredCumulatives.out", 5);
    // a unary resource inside a clique posted above adds nothing
    List<long[]> posted = new ArrayList<>();
    if (enabled()) {
      for (int[] clique : found) {
        long[] set = new long[(n + 63) >>> 6];
        for (int t : clique) {
          set[t >>> 6] |= 1L << t;
        }
        posted.add(set);
      }
    }
    // only inequalities whose capacity bound exceeds that of every input cumulative and clique
    // found: the others mostly add propagation, which slowed LCG (rcpsp-max psp_d_244 needed 3x
    // the conflicts); .useful=false posts them all
    double inputBound =
        !FALSE.equals(System.getProperty("org.jacop.fz.inferredCumulatives.useful"))
            ? inputBound(duration, found)
            : Double.NEGATIVE_INFINITY;
    List<InferredCumulatives.Inferred> inferred =
        inference.infer(
            covers,
            out,
            inf ->
                (!inf.unary() || !within(inf.tasks(), posted)) && inf.bound() > inputBound + 1e-9);
    if (support.options.debug()) {
      FzConsole.println(
          "% inferred cumulatives: "
              + rows.size()
              + " resources, "
              + n
              + " tasks, "
              + inference.covers()
              + " covers, "
              + inference.lifted()
              + " lifted, "
              + inference.dominated()
              + " dominated, "
              + inferred.size()
              + " posted, "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
    Map<Integer, IntVar> constants = new HashMap<>();
    for (InferredCumulatives.Inferred inf : inferred) {
      int[] tasks = inf.tasks();
      IntVar[] s = new IntVar[tasks.length];
      IntVar[] d = new IntVar[tasks.length];
      IntVar[] r = new IntVar[tasks.length];
      for (int k = 0; k < tasks.length; k++) {
        int t = tasks[k];
        s[k] = cliques.start(t);
        IntVar dv = cliques.durationVar(t);
        d[k] = dv != null ? dv : constant(constants, cliques.minDuration(t));
        r[k] = constant(constants, inf.use()[k]);
      }
      IntVar limit = constant(constants, inf.capacity());
      Constraint c =
          inf.unary()
              ? new CumulativeUnary(s, d, r, limit, true)
              : GlobalConstraints.configureCumulative(new Cumulative(s, d, r, limit));
      // redundant, so degree-based variable selections see the degrees of the model
      c.setDegreeWeight(0);
      if (support.options.debug()) {
        FzConsole.println(
            "% inferred cumulative of "
                + tasks.length
                + " tasks, capacity "
                + inf.capacity()
                + ", uses "
                + Arrays.toString(inf.use())
                + ", capacity bound "
                + String.format("%.1f", inf.bound()));
      }
      support.implied(() -> support.delayedConstraints.add(c));
      if (inf.unary()) {
        support.unaryResources.add(new IntVar[][] {s, d});
      }
    }
  }

  /** The largest capacity bound of an input cumulative or of a clique found. */
  private double inputBound(int[] duration, List<int[]> found) {
    double best = 0;
    for (Row row : rows) {
      double energy = 0;
      for (int k = 0; k < row.tasks.length; k++) {
        energy += (double) duration[row.tasks[k]] * Math.min(row.use[k], row.capacity);
      }
      best = Math.max(best, energy / row.capacity);
    }
    for (int[] clique : found) {
      double sum = 0;
      for (int t : clique) {
        sum += duration[t];
      }
      best = Math.max(best, sum);
    }
    return best;
  }

  private IntVar constant(Map<Integer, IntVar> constants, int v) {
    return constants.computeIfAbsent(v, k -> new IntVar(support.store, k, k));
  }

  private static boolean within(int[] tasks, List<long[]> sets) {
    for (long[] set : sets) {
      boolean all = true;
      for (int t : tasks) {
        if ((set[t >>> 6] & (1L << t)) == 0) {
          all = false;
          break;
        }
      }
      if (all) {
        return true;
      }
    }
    return false;
  }

  /** The common fixed length of the tasks, or 0 if they differ or one is not fixed. */
  private static int equalLength(IntVar[] d) {
    for (IntVar v : d) {
      if (!v.singleton() || v.value() != d[0].value()) {
        return 0;
      }
    }
    return d[0].value();
  }
}
