/*
 * Tabling.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Automatic tabulation (Akgün et al., CP 2018; Dekker et al., Constraints 2017): a small group of
 * constraints over a few variables is replaced by one table holding the solutions of the group. The
 * table propagates to domain consistency over the whole group, where the constraints of the group
 * propagate one at a time.
 *
 * <p>Two heuristics form the groups, on constraints whose variables are all integer variables and
 * that have at most {@link Limits#variables()} unfixed variables:
 *
 * <ol>
 *   <li>a constraint whose unfixed variables are a subset of those of another constraint joins it
 *       (Savile Row's identical scopes);
 *   <li>the constraints of a variable that occurs in at most {@link Limits#degree()} constraints
 *       join, so an intermediate variable of a decomposition, for example {@code t} in {@code t = x
 *       - y, z = abs(t)}, brings its definition and its use together.
 * </ol>
 *
 * A group grows only while it has at most {@link Limits#variables()} unfixed variables. Each group
 * of two or more constraints is solved on a scratch store, with a search over its unfixed variables
 * limited to {@link Limits#nodes()} nodes and {@link Limits#tuples()} solutions; a group within the
 * limits is replaced by the table of its solutions over all its unfixed variables. The table is
 * therefore equivalent to the group, so every solution, and the number of solutions, is kept. A
 * group whose table holds every tuple of its domains is entailed and is dropped without a table;
 * one without a solution makes the problem infeasible.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class Tabling {

  /**
   * Limits of the tabulation.
   *
   * @param variables most unfixed variables of a group, the arity of its table.
   * @param degree most constraints of a variable whose constraints are joined.
   * @param tuples most tuples of a table.
   * @param nodes most search nodes to tabulate one group.
   * @param budget most search nodes over all groups.
   */
  record Limits(int variables, int degree, int tuples, long nodes, long budget) {

    /** The limits of Savile Row: 10 variables and 10,000 tuples. */
    static final Limits DEFAULT = new Limits(10, 3, 10_000, 100_000, 2_000_000);
  }

  /**
   * A group of constraints and the table that replaces it.
   *
   * @param constraints the constraints of the group.
   * @param scope the unfixed variables of the group, the columns of the table.
   * @param tuples the solutions of the group over the scope, or null if the group is entailed.
   */
  record Group(List<Constraint> constraints, IntVar[] scope, int[][] tuples) {}

  private final Limits limits;
  private final Map<Var, Integer> position;
  private final List<Constraint> constraints;

  // per constraint: its unfixed variables as sorted positions, or null if it cannot be in a group
  private final int[][] scope;
  private final int[] parent;
  // per root of the union-find: the unfixed variables of the group as sorted positions
  private final int[][] groupScope;
  private final List<Var> variables;
  private long nodes;
  private boolean infeasible;

  private Tabling(List<Constraint> constraints, List<Var> variables, Limits limits) {
    this.limits = limits;
    this.constraints = constraints;
    this.variables = variables;
    this.position = new IdentityHashMap<>();
    for (int i = 0; i < variables.size(); i++) {
      position.put(variables.get(i), i);
    }
    int n = constraints.size();
    scope = new int[n][];
    parent = new int[n];
    groupScope = new int[n][];
    for (int i = 0; i < n; i++) {
      parent[i] = i;
      scope[i] = unfixedScope(constraints.get(i));
      groupScope[i] = scope[i];
    }
  }

  /**
   * Finds the groups of constraints to replace by tables.
   *
   * @param constraints the constraints, in a deterministic order.
   * @param variables the variables of the store, in a deterministic order; every variable of the
   *     constraints is among them.
   * @param limits the limits.
   * @return the tabling, with its groups.
   */
  static Tabling of(List<Constraint> constraints, List<Var> variables, Limits limits) {
    return new Tabling(constraints, variables, limits);
  }

  /**
   * Forms the groups and tabulates them.
   *
   * @return the groups replaced by tables or dropped as entailed, in the order of their first
   *     constraint; empty if the problem is infeasible.
   */
  List<Group> groups() {
    List<List<Integer>> occurrences = occurrences();
    joinSubsets(occurrences);
    joinThroughVariables(occurrences);

    Map<Integer, List<Integer>> members = new LinkedHashMap<>();
    for (int i = 0; i < constraints.size(); i++) {
      if (scope[i] != null) {
        members.computeIfAbsent(find(i), k -> new ArrayList<>()).add(i);
      }
    }
    List<Group> result = new ArrayList<>();
    for (Map.Entry<Integer, List<Integer>> e : members.entrySet()) {
      if (e.getValue().size() < 2 || nodes >= limits.budget()) {
        continue;
      }
      Group g = tabulate(e.getValue(), groupScope[e.getKey()]);
      if (infeasible) {
        return List.of();
      }
      if (g != null) {
        result.add(g);
      }
    }
    return result;
  }

  /**
   * Whether a group has no solution, which makes the problem infeasible.
   *
   * @return true if {@link #groups()} found a group without a solution.
   */
  boolean infeasible() {
    return infeasible;
  }

  /**
   * The search nodes spent tabulating.
   *
   * @return the nodes.
   */
  long nodes() {
    return nodes;
  }

  private int[] unfixedScope(Constraint c) {
    List<Integer> result = new ArrayList<>();
    for (Var v : c.arguments()) {
      if (!(v instanceof IntVar)) {
        return null;
      }
      if (!v.singleton()) {
        result.add(position.get(v));
      }
    }
    if (result.isEmpty() || result.size() > limits.variables()) {
      return null;
    }
    return result.stream().mapToInt(Integer::intValue).sorted().toArray();
  }

  /** For each variable position, the constraints with that variable unfixed, in order. */
  private List<List<Integer>> occurrences() {
    List<List<Integer>> occ = new ArrayList<>(variables.size());
    for (int i = 0; i < variables.size(); i++) {
      occ.add(null);
    }
    for (int i = 0; i < constraints.size(); i++) {
      for (Var v : constraints.get(i).arguments()) {
        if (!v.singleton()) {
          int p = position.get(v);
          if (occ.get(p) == null) {
            occ.set(p, new ArrayList<>(2));
          }
          occ.get(p).add(i);
        }
      }
    }
    return occ;
  }

  /** Heuristic 1: a constraint whose unfixed variables are a subset of another's joins it. */
  private void joinSubsets(List<List<Integer>> occ) {
    for (int i = 0; i < constraints.size(); i++) {
      if (scope[i] == null) {
        continue;
      }
      // the other constraint contains every variable of this one, so also the rarest
      List<Integer> candidates = null;
      for (int p : scope[i]) {
        if (candidates == null || occ.get(p).size() < candidates.size()) {
          candidates = occ.get(p);
        }
      }
      for (int j : candidates) {
        if (j != i
            && scope[j] != null
            && (subset(scope[i], scope[j]) || subset(scope[j], scope[i]))) {
          union(i, j);
        }
      }
    }
  }

  /** Heuristic 2: the constraints of a variable that occurs in few constraints join. */
  private void joinThroughVariables(List<List<Integer>> occ) {
    for (List<Integer> cs : occ) {
      if (cs == null || cs.size() < 2 || cs.size() > limits.degree()) {
        continue;
      }
      boolean eligible = true;
      for (int c : cs) {
        eligible &= scope[c] != null;
      }
      if (!eligible) {
        continue;
      }
      int[] joined = groupScope[find(cs.get(0))];
      for (int c : cs) {
        joined = merge(joined, groupScope[find(c)]);
      }
      if (joined.length <= limits.variables()) {
        for (int c : cs) {
          union(cs.get(0), c);
        }
      }
    }
  }

  private int find(int i) {
    while (parent[i] != i) {
      parent[i] = parent[parent[i]];
      i = parent[i];
    }
    return i;
  }

  private void union(int i, int j) {
    int a = find(i);
    int b = find(j);
    if (a == b) {
      return;
    }
    int[] joined = merge(groupScope[a], groupScope[b]);
    if (joined.length > limits.variables()) {
      return;
    }
    // the smaller index is the root, so groups are ordered by their first constraint
    int root = Math.min(a, b);
    parent[Math.max(a, b)] = root;
    groupScope[root] = joined;
  }

  private static boolean subset(int[] a, int[] b) {
    if (a.length > b.length) {
      return false;
    }
    int j = 0;
    for (int x : a) {
      while (j < b.length && b[j] < x) {
        j++;
      }
      if (j == b.length || b[j] != x) {
        return false;
      }
    }
    return true;
  }

  private static int[] merge(int[] a, int[] b) {
    int[] result = new int[a.length + b.length];
    int i = 0;
    int j = 0;
    int n = 0;
    while (i < a.length || j < b.length) {
      if (j == b.length || i < a.length && a[i] < b[j]) {
        result[n++] = a[i++];
      } else if (i == a.length || b[j] < a[i]) {
        result[n++] = b[j++];
      } else {
        result[n++] = a[i++];
        j++;
      }
    }
    return Arrays.copyOf(result, n);
  }

  /**
   * Solves a group on a scratch store.
   *
   * @return the group with its table, the group without a table if it is entailed, or null if it
   *     exceeds the limits.
   */
  private Group tabulate(List<Integer> members, int[] positions) {
    Store scratch = new Store();
    Map<Var, Var> copies = new IdentityHashMap<>();
    VarMap map =
        new VarMap() {
          @Override
          public Store target() {
            return scratch;
          }

          @Override
          @SuppressWarnings("unchecked")
          public <V extends Var> V get(V v) {
            return (V) copies.computeIfAbsent(v, x -> x.copyTo(scratch));
          }
        };
    List<Constraint> group = new ArrayList<>(members.size());
    for (int c : members) {
      group.add(constraints.get(c));
    }
    IntVar[] scope = new IntVar[positions.length];
    IntVar[] copy = new IntVar[positions.length];
    for (int i = 0; i < positions.length; i++) {
      scope[i] = (IntVar) variables.get(positions[i]);
      copy[i] = map.get(scope[i]);
    }
    try {
      for (Constraint c : group) {
        scratch.impose(((Copyable<?>) c).copy(map));
      }
    } catch (FailException e) {
      infeasible = true;
      return null;
    }
    Enumeration e = new Enumeration(scratch, copy);
    if (!e.run()) {
      return null;
    }
    if (e.solutions.isEmpty()) {
      infeasible = true;
      return null;
    }
    long all = 1;
    for (IntVar v : scope) {
      // only a count up to the number of solutions matters
      all = all > limits.tuples() ? all : all * v.getSize();
    }
    return new Group(
        List.copyOf(group),
        scope,
        all == e.solutions.size() ? null : e.solutions.toArray(new int[0][]));
  }

  /** A depth-first search for all solutions of a scratch store, within the limits. */
  private final class Enumeration {

    private final Store store;
    private final IntVar[] vars;
    private final List<int[]> solutions = new ArrayList<>();
    private final long start = nodes;

    Enumeration(Store store, IntVar[] vars) {
      this.store = store;
      this.vars = vars;
    }

    /** Returns false if a limit was reached. */
    boolean run() {
      if (!store.consistency()) {
        return true;
      }
      return dive();
    }

    private boolean dive() {
      IntVar next = null;
      for (IntVar v : vars) {
        if (!v.singleton() && (next == null || v.getSize() < next.getSize())) {
          next = v;
        }
      }
      if (next == null) {
        int[] tuple = new int[vars.length];
        for (int i = 0; i < vars.length; i++) {
          tuple[i] = vars[i].value();
        }
        solutions.add(tuple);
        return solutions.size() <= limits.tuples();
      }
      for (int value : next.dom().toIntArray()) {
        if (++nodes - start > limits.nodes() || nodes > limits.budget()) {
          return false;
        }
        int level = store.level;
        store.setLevel(level + 1);
        boolean within = true;
        try {
          next.domain.in(store.level, next, value, value);
          if (store.consistency()) {
            within = dive();
          }
        } catch (FailException f) {
          // no solution with this value
        }
        // propagation may have raised the level further (raiseLevelBeforeConsistency)
        while (store.level > level) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        }
        if (!within) {
          return false;
        }
      }
      return true;
    }
  }
}
