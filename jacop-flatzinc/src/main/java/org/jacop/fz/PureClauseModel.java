/*
 * PureClauseModel.java
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
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.cdcl.ComplementSymmetry;
import org.jacop.jasat.lcg.ClauseShape;
import org.jacop.lcg.LinearForm;
import org.jacop.satwrapper.SatWrapper;

/**
 * A satisfaction model that is a set of clauses over 0/1 variables and nothing else, given to JaSAT
 * ({@link CdclSolver}) as a CNF, as {@code CdclMain} solves a DIMACS file: with variable
 * elimination, chronological backtracking, vivification and local search, which the solver keeps
 * off while lazy clause generation connects the store's propagators to it.
 *
 * <p>The model qualifies when every constraint posted became a clause collected for the SAT solver
 * ({@link org.jacop.satwrapper.SatTranslation#collectedClauses}), the store holds no propagator
 * other than the given ones (the linear relaxation of the clauses, which only checks a full
 * assignment once the search has one), and each variable of a clause is 0/1. On the 90 CNFs of the
 * SAT Competition 2024/25 screen (osolpro benchmarks/gap-sources/sat) at 240 s, the FlatZinc front
 * end with lazy clause generation decided 21 (17 with -f) and {@code CdclMain} 30. A model whose
 * detectors posted constraints (symmetry breaking, cardinality) stays with lazy clause generation,
 * which uses them.
 *
 * <p>On by default; the system property {@code org.jacop.fz.pureClauses=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class PureClauseModel {

  /**
   * Returns whether pure clause models go to JaSAT, the property {@code org.jacop.fz.pureClauses},
   * read at every run.
   *
   * @return true unless the property is false
   */
  static boolean enabled() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.pureClauses", "true"));
  }

  /**
   * Returns whether a variable is fixed when the clauses have the complement symmetry, the property
   * {@code org.jacop.fz.complementSymmetry}, read at every run.
   *
   * @return true unless the property is false
   */
  static boolean complementSymmetry() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.complementSymmetry", "true"));
  }

  /** The variable (DIMACS number) fixed to 1 by the complement symmetry, 0 when none. */
  int complementFixed;

  /** The linear constraints taken as their clauses, and the lex-leader pairs taken as clauses. */
  int shapedConstraints;

  int lexPairs;

  /** The solver, with the clauses added. */
  final CdclSolver solver = new CdclSolver();

  // DIMACS variable i + 1 is vars[i]
  private final IntVar[] vars;

  private PureClauseModel(IntVar[] vars) {
    this.vars = vars;
  }

  /**
   * Returns the CNF of the store's model, or null when the store holds more than clauses.
   *
   * @param store the store, with every constraint of the model posted
   * @param clauses the collected clauses, each as its positive and its negative variables
   * @param ignored propagators that may stay in the store and are left out
   * @param lex the lex-leader constraints of symmetry breaking, as the pairs {x, y} of vectors each
   *     orders by x at most y, which become clauses when their variables are 0/1
   * @param declared the variables in the order of their declarations, which number the variables of
   *     the CNF first: as the order of a DIMACS file, it sets the solver's first decisions (hgen of
   *     the SAT screen took 0.5 to 19 s under three random numberings, 1.2 s as given)
   * @return the model with its clauses added to the solver, or null
   */
  static PureClauseModel of(
      Store store,
      List<IntVar[][]> clauses,
      Set<Constraint> ignored,
      Map<Constraint, List<IntVar[][]>> lex,
      Supplier<Var[]> declared) {
    List<IntVar[][]> all = new ArrayList<>(clauses);
    Shapes shapes = new Shapes(store, lex, all);
    if (!onlyClauses(store, ignored, shapes) || all.isEmpty()) {
      return null;
    }
    shapes.encodeLex();
    clauses = all;
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    List<IntVar> order = new ArrayList<>();
    for (IntVar[][] clause : clauses) {
      for (IntVar[] side : clause) {
        for (IntVar x : side) {
          if (x.singleton()) {
            continue;
          }
          if (x.min() != 0 || x.max() != 1) {
            return null;
          }
          if (index.putIfAbsent(x, order.size() + 1) == null) {
            order.add(x);
          }
        }
      }
    }
    // the declared variables first, then the others in the order the clauses first name them
    List<IntVar> numbered = new ArrayList<>(order.size());
    for (Var v : declared.get()) {
      if (v instanceof IntVar x && index.get(x) instanceof Integer i && i > 0) {
        numbered.add(x);
        index.put(x, -i);
      }
    }
    for (IntVar x : order) {
      if (index.get(x) > 0) {
        numbered.add(x);
      }
    }
    IntVar[] vars = numbered.toArray(new IntVar[0]);
    for (int i = 0; i < vars.length; i++) {
      index.put(vars[i], i + 1);
    }
    int n = vars.length;
    PureClauseModel model = new PureClauseModel(vars);
    model.shapedConstraints = shapes.shaped;
    model.lexPairs = shapes.lexPairs.size();
    model.solver.ensureVars(n);
    int[] lits = new int[16];
    List<int[]> added = new ArrayList<>(clauses.size());
    boolean empty = false;
    for (IntVar[][] clause : clauses) {
      int size = 0;
      boolean satisfied = false;
      for (int side = 0; side < 2 && !satisfied; side++) {
        for (IntVar x : clause[side]) {
          if (x.singleton()) {
            // a fixed variable either satisfies the clause or leaves it out
            if ((x.value() == 1) == (side == 0)) {
              satisfied = true;
              break;
            }
            continue;
          }
          if (size == lits.length) {
            lits = Arrays.copyOf(lits, 2 * size);
          }
          int variable = index.get(x);
          lits[size++] = side == 0 ? variable : -variable;
        }
      }
      if (satisfied) {
        continue;
      }
      if (size == 0) {
        // a clause false at the root: addClause of no literal fails the formula
        model.solver.addClause(new int[0], 0);
        empty = true;
        continue;
      }
      model.solver.addClause(lits, size);
      added.add(Arrays.copyOf(lits, size));
    }
    if (!empty && complementSymmetry()) {
      // every clause has its complement: the complement of a model is a model
      int v = ComplementSymmetry.fixedVariable(added, n);
      if (v != 0) {
        model.solver.addClause(new int[] {v}, 1);
        model.complementFixed = v;
      }
    }
    return model;
  }

  // no propagator but the clauses' own and the ignored ones; with shaped not null, a linear
  // constraint over 0/1 variables that is a few clauses over its own variables, and a lex-leader
  // constraint of symmetry breaking over 0/1 variables, count as their clauses, added to shaped
  private static boolean onlyClauses(Store store, Set<Constraint> ignored, Shapes shaped) {
    for (Constraint c : store.unlistedConstraints()) {
      if (!allowed(c, ignored, shaped)) {
        return false;
      }
    }
    // all variables, Boolean ones included (they are not in store.vars), stopping at the first
    // propagator of a model that is not of clauses alone
    for (Var v : store.variablesHashMap.values()) {
      if (!(v instanceof IntVar) && !v.singleton()) {
        return false;
      }
      for (Constraint c : v.dom().constraints()) {
        if (!allowed(c, ignored, shaped)) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Returns whether the store holds clauses alone that have the complement symmetry, which a pure
   * clause model breaks by fixing one variable (see {@link ComplementSymmetry}). Symmetry breaking
   * by lex-leader constraints is then left out: the model would stop being of clauses alone, and
   * the complement symmetry, which is a value symmetry of all variables at once, is not one the
   * automorphisms of the model graph find.
   *
   * @param store the store, with every constraint of the model posted
   * @param clauses the collected clauses, each as its positive and its negative variables
   * @return true when the clauses go to JaSAT with a variable fixed
   */
  static boolean complementSymmetric(Store store, List<IntVar[][]> clauses) {
    if (!enabled()
        || !complementSymmetry()
        || clauses.isEmpty()
        || !onlyClauses(store, Set.of(), null)) {
      return false;
    }
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    List<int[]> added = new ArrayList<>(clauses.size());
    for (IntVar[][] clause : clauses) {
      int[] lits = new int[clause[0].length + clause[1].length];
      int size = 0;
      boolean satisfied = false;
      for (int side = 0; side < 2 && !satisfied; side++) {
        for (IntVar x : clause[side]) {
          if (x.singleton()) {
            satisfied = (x.value() == 1) == (side == 0);
            if (satisfied) {
              break;
            }
            continue;
          }
          if (x.min() != 0 || x.max() != 1) {
            return false;
          }
          int variable = index.computeIfAbsent(x, k -> index.size() + 1);
          lits[size++] = side == 0 ? variable : -variable;
        }
      }
      if (satisfied) {
        continue;
      }
      if (size == 0) {
        return false;
      }
      added.add(Arrays.copyOf(lits, size));
    }
    return ComplementSymmetry.fixedVariable(added, index.size()) != 0;
  }

  private static boolean allowed(Constraint c, Set<Constraint> ignored, Shapes shaped) {
    if (ignored.contains(c) || c instanceof SatWrapper w && w.registeredVars.isEmpty()) {
      return true;
    }
    if (shaped == null) {
      return false;
    }
    if (!shaped.seen.add(c)) {
      return true;
    }
    List<IntVar[][]> pairs = shaped.lex.get(c);
    if (pairs != null) {
      return shaped.lexClauses(pairs);
    }
    List<IntVar[][]> cs = clausesOf(c);
    if (cs == null) {
      return false;
    }
    shaped.out.addAll(cs);
    shaped.shaped++;
    return true;
  }

  // the constraints that count as clauses, and their clauses
  private static final class Shapes {
    final Store store;
    final Map<Constraint, List<IntVar[][]>> lex;
    final List<IntVar[][]> out;
    final Set<Constraint> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    final List<IntVar[][]> lexPairs = new ArrayList<>();
    int shaped;

    Shapes(Store store, Map<Constraint, List<IntVar[][]>> lex, List<IntVar[][]> out) {
      this.store = store;
      this.lex = lex;
      this.out = out;
    }

    // takes the pairs of a lex-leader constraint when their variables are 0/1: their clauses are
    // those of x lexicographically at most y for each pair, with a new
    // 0/1 variable e[i] that the equal prefix x[0..i] = y[0..i] implies: e[i-1] -> x[i] <= y[i]
    // and e[i-1] and x[i] = y[i] -> e[i] (the lex-leader clauses of Aloul, Markov and Sakallah,
    // "Efficient symmetry breaking for Boolean satisfiability", IJCAI 2003); false when a variable
    // is not 0/1
    boolean lexClauses(List<IntVar[][]> pairs) {
      for (IntVar[][] pair : pairs) {
        for (IntVar[] side : pair) {
          for (IntVar v : side) {
            if (v.min() < 0 || v.max() > 1) {
              return false;
            }
          }
        }
        if (pair[0].length != pair[1].length) {
          return false;
        }
      }
      lexPairs.addAll(pairs);
      return true;
    }

    // the clauses of the lex pairs, once the variables of the store are no longer read
    void encodeLex() {
      for (IntVar[][] pair : lexPairs) {
        IntVar[] x = pair[0];
        IntVar[] y = pair[1];
        IntVar prefix = null;
        for (int i = 0; i < x.length; i++) {
          if (x[i] == y[i]) {
            continue;
          }
          out.add(clause(new IntVar[] {y[i]}, prefix, x[i]));
          if (i + 1 < x.length) {
            IntVar equal = new IntVar(store, 0, 1);
            out.add(clause(new IntVar[] {equal}, prefix, x[i], y[i]));
            out.add(clause(new IntVar[] {equal, x[i], y[i]}, prefix));
            prefix = equal;
          }
        }
      }
    }

    // the clause of the positive variables and the negated ones, leaving out a null prefix
    private static IntVar[][] clause(IntVar[] positive, IntVar prefix, IntVar... negative) {
      List<IntVar> neg = new ArrayList<>(negative.length + 1);
      if (prefix != null) {
        neg.add(prefix);
      }
      neg.addAll(Arrays.asList(negative));
      return new IntVar[][] {positive, neg.toArray(new IntVar[0])};
    }
  }

  /**
   * The most clauses per unfixed variable of a linear constraint that the model takes as its
   * clauses, the bound lazy clause generation uses (system property jacop.lcg.clauseShaped, default
   * 2).
   */
  private static final int CLAUSE_SHAPED = Integer.getInteger("jacop.lcg.clauseShaped", 2);

  // the clauses of a linear constraint over 0/1 variables when it is at most CLAUSE_SHAPED clauses
  // per unfixed variable over its own variables ({@link ClauseShape}), as lazy clause generation
  // takes it; null otherwise. A model of such constraints alone, as the PB competition's
  // 3-colouring formulas (3col-left3reg: x + y <= 1 on each edge and colour, exactly one colour per
  // vertex), is a CNF: JaSAT eliminates 6,988 of its 7,089 variables and refutes it in 4 s, where
  // lazy clause generation took 31 s
  private static List<IntVar[][]> clausesOf(Constraint c) {
    if (CLAUSE_SHAPED <= 0) {
      return null;
    }
    LinearForm f = LinearForms.of(c);
    if (f == null || f.relation() == LinearForm.NE) {
      return null;
    }
    IntVar[] xs = f.vars();
    long[] ws = f.weights();
    List<IntVar> vars = new ArrayList<>(xs.length);
    List<Long> weights = new ArrayList<>(xs.length);
    Map<IntVar, Integer> at = new IdentityHashMap<>();
    long rest = f.c();
    for (int i = 0; i < xs.length; i++) {
      if (ws[i] == 0) {
        continue;
      }
      if (xs[i].singleton()) {
        rest -= ws[i] * xs[i].value();
      } else if (xs[i].min() != 0
          || xs[i].max() != 1
          || at.putIfAbsent(xs[i], vars.size()) != null) {
        return null;
      } else {
        vars.add(xs[i]);
        weights.add(ws[i]);
      }
    }
    int n = vars.size();
    if (n == 0) {
      return null;
    }
    List<IntVar[][]> out = new ArrayList<>();
    int cap = CLAUSE_SHAPED * n;
    // sum w x REL rest: the GE side is sum w x >= rest, the LE side sum -w x >= -rest
    for (int side = 0; side < 2; side++) {
      if (side == 0 && f.relation() == LinearForm.LE
          || side == 1 && f.relation() == LinearForm.GE) {
        continue;
      }
      long sign = side == 0 ? 1 : -1;
      long k = sign * rest;
      long[] a = new long[n];
      int[] lits = new int[n];
      for (int i = 0; i < n; i++) {
        long w = sign * weights.get(i);
        // a negative weight: w x = w - w (1 - x), a positive weight on the negated literal
        if (w > 0) {
          a[i] = w;
          lits[i] = i + 1;
        } else {
          a[i] = -w;
          lits[i] = -(i + 1);
          k -= w;
        }
      }
      List<int[]> cs = ClauseShape.clauses(a, lits, k, cap - out.size());
      if (cs == null) {
        return null;
      }
      for (int[] clause : cs) {
        int pos = 0;
        for (int l : clause) {
          pos += l > 0 ? 1 : 0;
        }
        IntVar[] p = new IntVar[pos];
        IntVar[] q = new IntVar[clause.length - pos];
        int i = 0;
        int j = 0;
        for (int l : clause) {
          if (l > 0) {
            p[i++] = vars.get(l - 1);
          } else {
            q[j++] = vars.get(-l - 1);
          }
        }
        out.add(new IntVar[][] {p, q});
      }
    }
    return out;
  }

  /** Returns the number of variables of the clauses. */
  int numVars() {
    return vars.length;
  }

  /**
   * Fixes the variables of the store to the solver's model, and every other unfixed integer
   * variable, which is in no constraint, to its smallest value.
   *
   * @param store the store
   */
  void fixStore(Store store) {
    store.setLevel(store.level + 1);
    for (int i = 0; i < vars.length; i++) {
      int v = solver.modelValue(i + 1) ? 1 : 0;
      vars[i].domain.in(store.level, vars[i], v, v);
    }
    for (Var v : store.variablesHashMap.values()) {
      if (v instanceof IntVar x && !x.singleton()) {
        x.domain.in(store.level, x, x.min(), x.min());
      }
    }
  }
}
