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

  int cardinalityRows;

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
    Shapes shapes = Shapes.collect(store, clauses, ignored, lex);
    clauses = shapes.out;
    ignored = shapes.ignored;
    if (clauses.isEmpty()) {
      return null;
    }
    if (!onlyClauses(store, ignored)) {
      return null;
    }
    shapes.encode();
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
    model.cardinalityRows = shapes.cardinalities.size();
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
    return onlyClauses(store, ignored, null);
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
    List<LinearForm> bounds = shaped.splits.bounds.get(c);
    if (bounds != null) {
      return shaped.rows(bounds);
    }
    LinearForm flat = shaped.splits.rows.get(c);
    List<IntVar[][]> cs = flat != null ? clausesOf(flat) : clausesOf(c);
    if (cs == null) {
      return shaped.cardinality(flat != null ? flat : LinearForms.of(c));
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
    // the ignored constraints, with the ones that count as clauses when the model is of clauses
    Set<Constraint> ignored;
    int shaped;
    // the cardinality rows taken as the clauses of their counters, and their auxiliary variables
    final List<CardinalityClauses> cardinalities = new ArrayList<>();
    long auxiliaries;
    // the split linear constraints read back as rows
    SplitSums splits;

    Shapes(Store store, Map<Constraint, List<IntVar[][]>> lex, List<IntVar[][]> out) {
      this.store = store;
      this.lex = lex;
      this.out = out;
    }

    // the clauses with those of the constraints that count as clauses, when the model has no other
    // propagator but the ignored ones
    static Shapes collect(
        Store store,
        List<IntVar[][]> clauses,
        Set<Constraint> ignored,
        Map<Constraint, List<IntVar[][]>> lex) {
      Shapes shapes = new Shapes(store, lex, new ArrayList<>(clauses));
      shapes.ignored = ignored;
      shapes.splits = SplitSums.of(store);
      if (onlyClauses(store, ignored, shapes)) {
        shapes.ignored = Collections.newSetFromMap(new IdentityHashMap<>());
        shapes.ignored.addAll(ignored);
        shapes.ignored.addAll(shapes.seen);
      }
      return shapes;
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
    // a cardinality row that is no few clauses, taken as the clauses of its counter while the
    // auxiliary variables of all counters stay within CardinalityClauses.MAX_AUXILIARIES
    // the rows as clauses or cardinality rows; false when one is neither, or there are none
    boolean rows(List<LinearForm> rows) {
      for (LinearForm f : rows) {
        List<IntVar[][]> cs = clausesOf(f);
        if (cs != null) {
          out.addAll(cs);
        } else if (!cardinality(f)) {
          return false;
        }
      }
      return !rows.isEmpty();
    }

    boolean cardinality(LinearForm f) {
      CardinalityClauses row = CardinalityClauses.of(f);
      if (row == null || auxiliaries + row.auxiliaries() > CardinalityClauses.MAX_AUXILIARIES) {
        return false;
      }
      if (!row.holdsAlways()) {
        auxiliaries += row.auxiliaries();
        cardinalities.add(row);
      }
      return true;
    }

    // the clauses of the lex pairs and of the counters, once the model is of clauses
    void encode() {
      encodeLex();
      for (CardinalityClauses row : cardinalities) {
        row.encode(store, out);
      }
    }

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
  static List<IntVar[][]> clausesOf(Constraint c) {
    return CLAUSE_SHAPED <= 0 ? null : clausesOf(LinearForms.of(c));
  }

  // the clauses of the linear relation f, or null, as clausesOf(Constraint)
  private static List<IntVar[][]> clausesOf(LinearForm f) {
    if (CLAUSE_SHAPED <= 0 || f == null || f.relation() == LinearForm.NE) {
      return null;
    }
    List<IntVar> vars = new ArrayList<>();
    List<Long> weights = new ArrayList<>();
    long[] rest = {f.c()};
    if (!unfixedTerms(f, vars, weights, rest) || vars.isEmpty()) {
      return null;
    }
    List<IntVar[][]> out = new ArrayList<>();
    int cap = CLAUSE_SHAPED * vars.size();
    // sum w x REL rest: the GE side is sum w x >= rest, the LE side sum -w x >= -rest
    for (int side = 0; side < 2; side++) {
      boolean skipped =
          side == 0 && f.relation() == LinearForm.LE || side == 1 && f.relation() == LinearForm.GE;
      List<int[]> cs =
          skipped ? List.of() : sideClauses(weights, side == 0 ? 1 : -1, rest[0], cap - out.size());
      if (cs == null) {
        return null;
      }
      for (int[] clause : cs) {
        out.add(asVars(clause, vars));
      }
    }
    return out;
  }

  // the unfixed variables of f with their weights, and rest less the fixed terms; false when an
  // unfixed variable is not 0/1 or occurs twice
  private static boolean unfixedTerms(
      LinearForm f, List<IntVar> vars, List<Long> weights, long[] rest) {
    IntVar[] xs = f.vars();
    long[] ws = f.weights();
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int i = 0; i < xs.length; i++) {
      if (ws[i] == 0) {
        continue;
      }
      if (xs[i].singleton()) {
        rest[0] -= ws[i] * xs[i].value();
      } else if (xs[i].min() != 0 || xs[i].max() != 1 || !seen.add(xs[i])) {
        return false;
      } else {
        vars.add(xs[i]);
        weights.add(ws[i]);
      }
    }
    return true;
  }

  // the clauses of sum sign w x >= sign rest over the literals 1..n of the variables, at most cap,
  // or null ({@link ClauseShape#clauses})
  private static List<int[]> sideClauses(List<Long> weights, long sign, long rest, int cap) {
    int n = weights.size();
    long k = sign * rest;
    long[] a = new long[n];
    int[] lits = new int[n];
    for (int i = 0; i < n; i++) {
      long w = sign * weights.get(i);
      // a negative weight: w x = w - w (1 - x), a positive weight on the negated literal
      a[i] = Math.abs(w);
      lits[i] = w > 0 ? i + 1 : -(i + 1);
      k -= Math.min(w, 0);
    }
    return ClauseShape.clauses(a, lits, k, cap);
  }

  // a clause of literals 1..n as its positive and its negative variables
  private static IntVar[][] asVars(int[] clause, List<IntVar> vars) {
    List<IntVar> p = new ArrayList<>();
    List<IntVar> q = new ArrayList<>();
    for (int l : clause) {
      if (l > 0) {
        p.add(vars.get(l - 1));
      } else {
        q.add(vars.get(-l - 1));
      }
    }
    return new IntVar[][] {p.toArray(new IntVar[0]), q.toArray(new IntVar[0])};
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
    // the block sums of split rows follow from their blocks
    if (!store.consistency()) {
      throw new IllegalStateException("the store rejects the model of the clauses");
    }
    for (Var v : store.variablesHashMap.values()) {
      if (v instanceof IntVar x && !x.singleton()) {
        x.domain.in(store.level, x, x.min(), x.min());
      }
    }
  }
}
