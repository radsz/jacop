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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.cdcl.ComplementSymmetry;
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
   * @param declared the variables in the order of their declarations, which number the variables of
   *     the CNF first: as the order of a DIMACS file, it sets the solver's first decisions (hgen of
   *     the SAT screen took 0.5 to 19 s under three random numberings, 1.2 s as given)
   * @return the model with its clauses added to the solver, or null
   */
  static PureClauseModel of(
      Store store, List<IntVar[][]> clauses, Set<Constraint> ignored, Supplier<Var[]> declared) {
    if (clauses.isEmpty()) {
      return null;
    }
    if (!onlyClauses(store, ignored)) {
      return null;
    }
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

  // no propagator but the clauses' own and the ignored ones
  private static boolean onlyClauses(Store store, Set<Constraint> ignored) {
    for (Constraint c : store.unlistedConstraints()) {
      if (!allowed(c, ignored)) {
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
        if (!allowed(c, ignored)) {
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
    if (!enabled() || !complementSymmetry() || clauses.isEmpty() || !onlyClauses(store, Set.of())) {
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

  private static boolean allowed(Constraint c, Set<Constraint> ignored) {
    return ignored.contains(c) || c instanceof SatWrapper w && w.registeredVars.isEmpty();
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
