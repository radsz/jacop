/*
 * Components.java
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

package org.jacop.fz;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XeqC;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;

/**
 * Independent components of a model (SCIP's {@code cons_components}): the variables that are not
 * fixed, split by the constraints that are not satisfied into groups that share no constraint.
 *
 * <p>A component that the objective does not depend on needs one solution, whatever the other
 * components take. Search over the whole model may still come back into it, for example when a
 * search order that interleaves components fails in another one, or when branch and bound tightens
 * the objective. {@link #solveSide} finds one solution of each such component before search, each
 * in a search of its own with a time budget, and fixes its variables to it. A component without a
 * solution makes the model infeasible. For a satisfaction problem the largest component is left to
 * the search, and the others are solved this way.
 *
 * <p>This keeps one solution of a satisfaction problem and every optimum, but not every solution,
 * so it is only for searches that want one solution or an optimum. Clauses kept outside the store,
 * for the SAT solver of --lcg, link their variables like constraints and are imposed in the store
 * while their component is solved.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class Components {

  /** What {@link #solveSide} did. */
  record Outcome(int components, int solved, int fixed, int timedOut, long millis) {}

  private Components() {}

  /**
   * Solves and fixes the components the objective does not depend on.
   *
   * @param store the store, at a fixpoint at the level of the search.
   * @param clauses clauses kept outside the store, each {positive, negative}; may be empty.
   * @param objective the objective variable, or null for a satisfaction problem.
   * @param order variables to branch on first, in this order, for example those of the search
   *     annotations.
   * @param budgetMillis the time all the component searches may take together.
   * @return what was done.
   * @throws org.jacop.core.FailException if a component has no solution.
   */
  static Outcome solveSide(
      Store store, List<IntVar[][]> clauses, IntVar objective, List<Var> order, long budgetMillis) {
    long start = System.currentTimeMillis();
    Map<Var, Var> parent = new IdentityHashMap<>();
    for (Constraint c : store.getConstraints()) {
      if (c instanceof SatisfiedPresent s && s.satisfied()) {
        continue;
      }
      join(parent, c.arguments());
    }
    for (IntVar[][] clause : clauses) {
      List<Var> vars = new ArrayList<>();
      vars.addAll(List.of(clause[0]));
      vars.addAll(List.of(clause[1]));
      join(parent, vars);
    }
    // the components in the order of the store's variables, so that the result is deterministic
    Map<Var, List<Var>> components = new LinkedHashMap<>();
    for (int i = 0; i < store.size(); i++) {
      Var v = store.vars[i];
      if (parent.containsKey(v)) {
        components.computeIfAbsent(find(parent, v), k -> new ArrayList<>()).add(v);
      }
    }
    for (Var v : store.variablesHashMap.values()) {
      if (v.index() < 0 && parent.containsKey(v)) {
        components.computeIfAbsent(find(parent, v), k -> new ArrayList<>()).add(v);
      }
    }
    int n = components.size();
    if (n < 2) {
      return new Outcome(n, 0, 0, 0, System.currentTimeMillis() - start);
    }
    Var kept;
    if (objective != null) {
      kept =
          objective.singleton() || !parent.containsKey(objective) ? null : find(parent, objective);
      if (kept == null) {
        return new Outcome(n, 0, 0, 0, System.currentTimeMillis() - start);
      }
    } else {
      kept = null;
      int largest = -1;
      for (Map.Entry<Var, List<Var>> e : components.entrySet()) {
        if (e.getValue().size() > largest) {
          largest = e.getValue().size();
          kept = e.getKey();
        }
      }
    }
    int solved = 0;
    int fixed = 0;
    int timedOut = 0;
    for (Map.Entry<Var, List<Var>> e : components.entrySet()) {
      if (e.getKey() == kept) {
        continue;
      }
      List<IntVar> vars = variables(e.getValue(), order);
      long left = budgetMillis - (System.currentTimeMillis() - start);
      if (vars == null || vars.isEmpty() || left <= 0) {
        continue;
      }
      int[] values = solve(store, vars, clauses, left);
      if (values == null) {
        timedOut++;
        continue;
      }
      for (int i = 0; i < values.length; i++) {
        store.impose(new XeqC(vars.get(i), values[i]));
      }
      if (!store.consistency()) {
        throw Store.failException;
      }
      solved++;
      fixed += values.length;
    }
    return new Outcome(n, solved, fixed, timedOut, System.currentTimeMillis() - start);
  }

  /**
   * The variables of a component to branch on: those of {@code order} first, then the others; null
   * if the component has a variable that is not an integer variable.
   */
  private static List<IntVar> variables(List<Var> component, List<Var> order) {
    Set<Var> members = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Var v : component) {
      if (!(v instanceof IntVar)) {
        return null;
      }
      members.add(v);
    }
    Set<Var> added = Collections.newSetFromMap(new IdentityHashMap<>());
    List<IntVar> vars = new ArrayList<>();
    for (Var v : order) {
      if (members.contains(v) && !v.singleton() && added.add(v)) {
        vars.add((IntVar) v);
      }
    }
    for (Var v : component) {
      if (!v.singleton() && added.add(v)) {
        vars.add((IntVar) v);
      }
    }
    return vars;
  }

  /**
   * One solution of a component, or null if the search ran out of time.
   *
   * @throws org.jacop.core.FailException if the component has no solution.
   */
  private static int[] solve(Store store, List<IntVar> vars, List<IntVar[][]> clauses, long ms) {
    List<Constraint> posted = new ArrayList<>();
    Set<Var> in = Collections.newSetFromMap(new IdentityHashMap<>());
    in.addAll(vars);
    for (IntVar[][] clause : clauses) {
      if (touches(clause, in)) {
        Constraint c = new BoolClause(clause[0], clause[1]);
        store.impose(c);
        posted.add(c);
      }
    }
    IntVar[] array = vars.toArray(new IntVar[0]);
    DepthFirstSearch<IntVar> label = new DepthFirstSearch<>();
    label.setPrintInfo(false);
    label.setAssignSolution(false);
    label.getSolutionListener().recordSolutions(true);
    label.setTimeOutMilliseconds(ms);
    boolean found;
    try {
      found = label.labeling(store, new SimpleSelect<>(array, null, new IndomainMin<>()));
    } finally {
      for (Constraint c : posted) {
        c.removeConstraint();
      }
    }
    if (!found) {
      if (label.timeOutOccured) {
        return null;
      }
      throw Store.failException;
    }
    Domain[] solution = label.getSolution();
    int[] values = new int[array.length];
    for (int i = 0; i < values.length; i++) {
      values[i] = ((IntDomain) solution[i]).value();
    }
    return values;
  }

  private static boolean touches(IntVar[][] clause, Set<Var> in) {
    for (IntVar[] side : clause) {
      for (IntVar v : side) {
        if (in.contains(v)) {
          return true;
        }
      }
    }
    return false;
  }

  private static void join(Map<Var, Var> parent, Iterable<? extends Var> vars) {
    Var first = null;
    for (Var v : vars) {
      if (v.singleton()) {
        continue;
      }
      parent.putIfAbsent(v, v);
      if (first == null) {
        first = v;
      } else {
        Var a = find(parent, first);
        Var b = find(parent, v);
        if (a != b) {
          parent.put(a, b);
        }
      }
    }
  }

  private static Var find(Map<Var, Var> parent, Var x) {
    Var r = x;
    while (parent.get(r) != r) {
      r = parent.get(r);
    }
    while (parent.get(x) != r) {
      Var next = parent.get(x);
      parent.put(x, r);
      x = next;
    }
    return r;
  }
}
