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
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.UnaryTransition;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.presolve.DisjunctiveCliques;

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
 * <p>Setting the system property {@code org.jacop.fz.disjunctiveCliques} to false turns the
 * detection off.
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
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.disjunctiveCliques"));
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
    post(found);
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_cumulative" -> cumulative(node);
      case "int_lin_le" -> linear(node, null, false);
      case "int_lin_eq" -> linear(node, null, true);
      case "int_lin_le_imp", "int_lin_le_reif" -> linear(node, var(node, 3), false);
      case "int_le" -> difference(var(node, 0), var(node, 1), 0, null);
      case "int_lt" -> difference(var(node, 0), var(node, 1), 1, null);
      case "int_le_imp", "int_le_reif" -> difference(var(node, 0), var(node, 1), 0, var(node, 2));
      case "int_lt_imp", "int_lt_reif" -> difference(var(node, 0), var(node, 1), 1, var(node, 2));
      case "bool_clause" -> {
        IntVar[] pos = support.getVarArray(child(node, 0));
        if (pos.length == 2 && support.getVarArray(child(node, 1)).length == 0) {
          clauses.add(pos);
        }
      }
      case "array_bool_or" -> {
        IntVar[] pos = support.getVarArray(child(node, 0));
        if (pos.length == 2 && var(node, 1).singleton(1)) {
          clauses.add(pos);
        }
      }
      case "bool_not" -> clauses.add(new IntVar[] {var(node, 0), var(node, 1)});
      default -> {
        // not a fact about disjoint tasks
      }
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar var(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void cumulative(ASTConstElem node) {
    IntVar[] s = support.getVarArray(child(node, 0));
    IntVar[] d = support.getVarArray(child(node, 1));
    IntVar[] r = support.getVarArray(child(node, 2));
    int capacity = var(node, 3).max();
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

  // a*x + b*y <= c (or = c) with b = -a: a difference constraint between x and y
  private void linear(ASTConstElem node, IntVar literal, boolean equation) {
    int[] a = support.getIntArray(child(node, 0));
    if (a == null || a.length != 2 || a[0] != -a[1] || a[0] == 0) {
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
      // with setup times in the disjunctions the unary resource counts them
      Constraint unary =
          setups ? new UnaryTransition(s, d, tt) : new CumulativeUnary(s, d, r, one, true);
      // redundant, so degree-based variable selections see the degrees of the model
      unary.setDegreeWeight(0);
      if (support.options.debug()) {
        FzConsole.println(
            "% redundant unary resource on "
                + clique.length
                + " tasks"
                + (setups ? " with transition times" : ""));
      }
      support.delayedConstraints.add(unary);
    }
  }
}
