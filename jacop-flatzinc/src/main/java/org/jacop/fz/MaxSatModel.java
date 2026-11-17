/*
 * MaxSatModel.java
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
import java.util.Collection;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.cumulative.EnergyPrecedence;
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;
import org.jacop.search.ls.MaxSatLocalSearch;

/**
 * A model that is weighted partial MaxSAT: clauses over 0/1 variables and a minimised cost that
 * linear equalities define as a constant plus a weighted sum of 0/1 variables. The cost terms
 * become unit soft clauses, and a term variable that is only the relaxation of one clause, as in
 * the MaxSAT encoding {@code (C or b)} with cost {@code w * b}, gives back the soft clause C of
 * weight w. Aliases {@code x = y} and negations {@code x + y = 1} of 0/1 variables share a variable
 * of the local search.
 */
final class MaxSatModel {

  // the 0/1 variables of the model, the local search variable of each, and its sign
  final IntVar[] vars;
  private final int[] lsVar;
  private final boolean[] negated;
  // the relaxation variables taken out: their local search variable is true when their clause is
  // falsified
  private final int[] relaxed;
  private final int[][] relaxedClause;
  private final long constant;
  final List<int[]> hard = new ArrayList<>();
  final List<int[]> soft = new ArrayList<>();
  final List<Long> weights = new ArrayList<>();
  final int lsVars;

  private MaxSatModel(
      IntVar[] vars,
      int[] lsVar,
      boolean[] negated,
      int lsVars,
      List<int[]> hard,
      List<int[]> soft,
      List<Long> weights,
      int[] relaxed,
      int[][] relaxedClause,
      long constant) {
    this.vars = vars;
    this.lsVar = lsVar;
    this.negated = negated;
    this.lsVars = lsVars;
    this.hard.addAll(hard);
    this.soft.addAll(soft);
    this.weights.addAll(weights);
    this.relaxed = relaxed;
    this.relaxedClause = relaxedClause;
    this.constant = constant;
  }

  /** The local search over the clauses. */
  MaxSatLocalSearch search(long softBound, long seed) {
    long[] w = new long[weights.size()];
    for (int k = 0; k < w.length; k++) {
      w[k] = weights.get(k);
    }
    return new MaxSatLocalSearch(lsVars, hard, soft, w, softBound, seed);
  }

  /** The cost of an assignment of the local search whose soft clauses falsify the given weight. */
  long cost(long falsified) {
    return constant + falsified;
  }

  /** The assignment of the local search for the values of {@link #vars}. */
  boolean[] assignment(int[] values) {
    boolean[] a = new boolean[lsVars];
    for (int k = 0; k < vars.length; k++) {
      a[lsVar[k]] = (values[k] == 1) != negated[k];
    }
    fixRelaxed(a);
    return a;
  }

  // a relaxation variable is true when the rest of its clause is false
  private void fixRelaxed(boolean[] a) {
    for (int k = 0; k < relaxed.length; k++) {
      boolean sat = false;
      for (int lit : relaxedClause[k]) {
        if (a[lit >> 1] == ((lit & 1) == 0)) {
          sat = true;
          break;
        }
      }
      a[relaxed[k]] = !sat;
    }
  }

  /** The values of {@link #vars} for an assignment of the local search. */
  int[] values(boolean[] assignment) {
    boolean[] a = assignment.clone();
    fixRelaxed(a);
    int[] values = new int[vars.length];
    for (int k = 0; k < vars.length; k++) {
      values[k] = a[lsVar[k]] != negated[k] ? 1 : 0;
    }
    return values;
  }

  private static boolean binary(IntVar x) {
    return x.min() >= 0 && x.max() <= 1;
  }

  /**
   * Reads the model as MaxSAT.
   *
   * @param store the store
   * @param clauses the clauses of the SAT solver, positive and negative variables
   * @param cost the minimised cost
   * @param ignored constraints the local search leaves out, such as symmetry breaking constraints
   *     that a canonical form of its solutions satisfies
   * @return the model, or null when it is not MaxSAT
   */
  static MaxSatModel detect(
      Store store, List<IntVar[][]> clauses, IntVar cost, Collection<Constraint> ignored) {
    if (clauses.isEmpty()) {
      return null;
    }
    Set<Constraint> constraints = new LinkedHashSet<>();
    Set<Var> all = new LinkedHashSet<>();
    for (int i = 0; i < store.size(); i++) {
      if (store.vars[i] != null) {
        all.add(store.vars[i]);
      }
    }
    all.addAll(store.variablesHashMap.values());
    for (Var v : all) {
      constraints.addAll(v.dom().constraints());
      constraints.addAll(store.valueWatchers(v));
    }
    constraints.addAll(store.watchedLiteralConstraints());
    constraints.removeIf(
        c ->
            c instanceof LinearRelaxation
                || c instanceof EnergyPrecedence
                || store.isImplied(c)
                || ignored.contains(c));
    Map<Constraint, LinearForm> forms = new LinkedHashMap<>();
    for (Constraint c : constraints) {
      LinearForm f = LinearForms.of(c);
      if (f == null) {
        // a constraint that is not linear: not MaxSAT
        return null;
      }
      forms.put(c, f);
    }
    // the cost as a constant plus weighted 0/1 variables, through the definitions of the others
    Map<IntVar, Long> terms = new IdentityHashMap<>();
    terms.put(cost, 1L);
    long constant = 0;
    Set<Constraint> used = new HashSet<>();
    Set<IntVar> defined = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
    // the equalities on each variable, for its definition
    Map<IntVar, List<Constraint>> equalities = new IdentityHashMap<>();
    for (Map.Entry<Constraint, LinearForm> e : forms.entrySet()) {
      if (e.getValue().relation() == LinearForm.EQ) {
        for (IntVar z : e.getValue().vars()) {
          List<Constraint> on = equalities.computeIfAbsent(z, k -> new ArrayList<>());
          if (on.isEmpty() || on.get(on.size() - 1) != e.getKey()) {
            on.add(e.getKey());
          }
        }
      }
    }
    java.util.ArrayDeque<IntVar> wide = new java.util.ArrayDeque<>();
    wide.add(cost);
    while (!wide.isEmpty()) {
      IntVar y = wide.poll();
      if (!terms.containsKey(y)) {
        continue;
      }
      Constraint def = null;
      long a = 0;
      for (Constraint c : equalities.getOrDefault(y, List.of())) {
        if (used.contains(c)) {
          continue;
        }
        LinearForm f = forms.get(c);
        long coefficient = 0;
        for (int k = 0; k < f.vars().length; k++) {
          if (f.vars()[k] == y) {
            coefficient += f.weights()[k];
          }
        }
        if (Math.abs(coefficient) == 1) {
          def = c;
          a = coefficient;
          break;
        }
      }
      if (def == null) {
        return null;
      }
      used.add(def);
      defined.add(y);
      LinearForm f = forms.get(def);
      long scale = terms.remove(y) * a;
      for (int k = 0; k < f.vars().length; k++) {
        IntVar z = f.vars()[k];
        if (z == y) {
          continue;
        }
        long w = -scale * f.weights()[k];
        if (z.singleton()) {
          constant += w * z.value();
        } else {
          terms.merge(z, w, Long::sum);
          if (!binary(z)) {
            wide.add(z);
          }
        }
      }
      constant += scale * f.c();
    }
    terms.values().removeIf(w -> w == 0);
    if (terms.isEmpty()) {
      return null;
    }
    for (IntVar t : terms.keySet()) {
      if (!binary(t)) {
        return null;
      }
    }
    // the other linear constraints: aliases and negations of 0/1 variables, or redundant ones on
    // the cost and its definitions, which the store checks
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    List<int[]> links = new ArrayList<>();
    for (Map.Entry<Constraint, LinearForm> e : forms.entrySet()) {
      if (used.contains(e.getKey())) {
        continue;
      }
      LinearForm f = e.getValue();
      if (f.relation() == LinearForm.EQ
          && f.vars().length == 2
          && binary(f.vars()[0])
          && binary(f.vars()[1])
          && Math.abs(f.weights()[0]) == 1
          && Math.abs(f.weights()[1]) == 1) {
        long w0 = f.weights()[0];
        long w1 = f.weights()[1];
        long c = f.c();
        // x - y = 0, or x + y = 1 (also with both signs flipped)
        boolean alias = w0 == -w1 && c == 0;
        boolean negation = w0 == w1 && c == w0;
        if (alias || negation) {
          int i = index(f.vars()[0], index, vars);
          int j = index(f.vars()[1], index, vars);
          links.add(new int[] {i, j, negation ? 1 : 0});
          continue;
        }
      }
      boolean redundant = true;
      for (IntVar z : f.vars()) {
        if (!z.singleton() && z != cost && !defined.contains(z) && !terms.containsKey(z)) {
          redundant = false;
        }
      }
      if (!redundant) {
        return null;
      }
    }
    List<int[]> hard = new ArrayList<>();
    for (IntVar[][] clause : clauses) {
      List<Integer> lits = new ArrayList<>();
      boolean sat = false;
      for (int s = 0; s < 2 && !sat; s++) {
        for (IntVar x : clause[s]) {
          if (!binary(x)) {
            return null;
          }
          if (x.singleton()) {
            sat |= (x.value() == 1) == (s == 0);
            continue;
          }
          lits.add(2 * index(x, index, vars) + s);
        }
      }
      if (sat) {
        continue;
      }
      if (lits.isEmpty()) {
        return null;
      }
      hard.add(lits.stream().mapToInt(Integer::intValue).toArray());
    }
    for (IntVar t : terms.keySet()) {
      index(t, index, vars);
    }
    // two binary clauses (a or b) and (not a or not b) say that b is the negation of a, as the
    // clauses of a negation or an equality that went to the SAT solver
    Set<Long> binaries = new HashSet<>();
    for (int[] c : hard) {
      if (c.length == 2) {
        binaries.add(pair(c[0], c[1]));
      }
    }
    for (int[] c : hard) {
      if (c.length == 2 && c[0] >> 1 != c[1] >> 1 && binaries.contains(pair(c[0] ^ 1, c[1] ^ 1))) {
        // a = not b: the variables are negations when the signs are equal, aliases otherwise
        boolean sameSign = (c[0] & 1) == (c[1] & 1);
        links.add(new int[] {c[0] >> 1, c[1] >> 1, sameSign ? 1 : 0});
      }
    }
    // the variables of the local search: classes of aliases and negations
    int n = vars.size();
    int[] parent = new int[n];
    boolean[] flip = new boolean[n];
    for (int i = 0; i < n; i++) {
      parent[i] = i;
    }
    for (int[] l : links) {
      int ri = find(l[0], parent, flip);
      boolean si = sign(l[0], parent, flip);
      int rj = find(l[1], parent, flip);
      boolean sj = sign(l[1], parent, flip);
      boolean want = l[2] == 1;
      if (ri == rj) {
        if ((si ^ sj) != want) {
          return null;
        }
        continue;
      }
      parent[rj] = ri;
      flip[rj] = si ^ sj ^ want;
    }
    int[] lsVar = new int[n];
    boolean[] negated = new boolean[n];
    int[] rootVar = new int[n];
    java.util.Arrays.fill(rootVar, -1);
    int lsVars = 0;
    for (int i = 0; i < n; i++) {
      int r = find(i, parent, flip);
      negated[i] = sign(i, parent, flip);
      if (rootVar[r] < 0) {
        rootVar[r] = lsVars++;
      }
      lsVar[i] = rootVar[r];
    }
    List<int[]> lsHard = new ArrayList<>();
    for (int[] c : hard) {
      int[] m = new int[c.length];
      for (int k = 0; k < c.length; k++) {
        int i = c[k] >> 1;
        m[k] = 2 * lsVar[i] + ((c[k] & 1) ^ (negated[i] ? 1 : 0));
      }
      lsHard.add(m);
    }
    // the cost added when each variable of the local search is true
    long[] costTrue = new long[lsVars];
    for (Map.Entry<IntVar, Long> e : terms.entrySet()) {
      int i = index.get(e.getKey());
      long w = e.getValue();
      if (negated[i]) {
        constant += w;
        costTrue[lsVar[i]] -= w;
      } else {
        costTrue[lsVar[i]] += w;
      }
    }
    // occurrences of each literal in the hard clauses, for the relaxations
    int[] occurrences = new int[2 * lsVars];
    int[] where = new int[2 * lsVars];
    for (int h = 0; h < lsHard.size(); h++) {
      for (int lit : lsHard.get(h)) {
        occurrences[lit]++;
        where[lit] = h;
      }
    }
    List<int[]> soft = new ArrayList<>();
    List<Long> weights = new ArrayList<>();
    boolean[] dropped = new boolean[lsHard.size()];
    List<Integer> relaxed = new ArrayList<>();
    List<int[]> relaxedClause = new ArrayList<>();
    for (int v = 0; v < lsVars; v++) {
      long w = costTrue[v];
      if (w == 0) {
        continue;
      }
      // the literal that costs w: v true for w > 0, v false for w < 0 (then cost = w + |w| * not v)
      int costly = w > 0 ? 2 * v : 2 * v + 1;
      if (w < 0) {
        constant += w;
        w = -w;
      }
      if (costly == 2 * v
          && occurrences[costly] == 1
          && occurrences[costly ^ 1] == 0
          && !dropped[where[costly]]
          && lsHard.get(where[costly]).length > 1) {
        // the relaxation of one clause: the rest of the clause is the soft clause
        int h = where[costly];
        dropped[h] = true;
        int[] c = lsHard.get(h);
        int[] rest = new int[c.length - 1];
        int k = 0;
        for (int lit : c) {
          if (lit != costly) {
            rest[k++] = lit;
          }
        }
        soft.add(rest);
        weights.add(w);
        // the relaxation is true when the rest is false
        relaxed.add(v);
        relaxedClause.add(rest);
      } else {
        soft.add(new int[] {costly ^ 1});
        weights.add(w);
      }
    }
    List<int[]> keptHard = new ArrayList<>();
    for (int h = 0; h < lsHard.size(); h++) {
      if (!dropped[h]) {
        keptHard.add(lsHard.get(h));
      }
    }
    return new MaxSatModel(
        vars.toArray(new IntVar[0]),
        lsVar,
        negated,
        lsVars,
        keptHard,
        soft,
        weights,
        relaxed.stream().mapToInt(Integer::intValue).toArray(),
        relaxedClause.toArray(new int[0][]),
        constant);
  }

  private static long pair(int a, int b) {
    return a < b ? ((long) a << 32) | b : ((long) b << 32) | a;
  }

  private static int index(IntVar x, Map<IntVar, Integer> index, List<IntVar> vars) {
    Integer i = index.get(x);
    if (i == null) {
      i = vars.size();
      index.put(x, i);
      vars.add(x);
    }
    return i;
  }

  private static int find(int i, int[] parent, boolean[] flip) {
    while (parent[i] != i) {
      i = parent[i];
    }
    return i;
  }

  // whether i is the negation of the root of its class
  private static boolean sign(int i, int[] parent, boolean[] flip) {
    boolean s = false;
    while (parent[i] != i) {
      s ^= flip[i];
      i = parent[i];
    }
    return s;
  }
}
