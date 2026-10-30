/*
 * LinearRelaxation.java
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

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.Stateful;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;

/**
 * The linear relaxation of the linear constraints of a store, solved by a dual simplex during
 * search, as a propagator of lowest priority. Every deduction is an integer combination of the
 * rows: the multipliers of the simplex (its dual values at an optimal basis, or the row of the
 * basis inverse that proves infeasibility) are scaled and rounded to integers, the combination
 * {@code sum lambda_i a_i x} with the matching sides of the rows is computed exactly, and the
 * resulting inequality is propagated by bounds reasoning. A combination of rows holds wherever the
 * rows do, so floating-point errors of the simplex can weaken the deduction but never make it
 * wrong. With an objective, the combination of the dual values bounds the objective and fixes
 * variables by their reduced costs; without one, the relaxation only detects infeasibility.
 *
 * <p>For lazy clause generation each deduction is explained by its inequality ({@link LinearForm}),
 * through the bounds of the other variables, as a linear constraint of the model would be.
 *
 * <p>The simplex is the dense {@link DualSimplex} by default, or the sparse {@link
 * SparseDualSimplex} ({@link Simplex#SPARSE}), which fits large sparse relaxations. With {@link
 * Simplex#LAZY} the sparse simplex starts without rows: each solve adds, in batches, the rows its
 * solution breaks and solves again, and rows that stay inactive for many solves leave the simplex
 * again. The rows the simplex lacks only weaken its deductions; every deduction is still a
 * combination of rows of the model.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LinearRelaxation extends Constraint
    implements Explainable, Stateful, Copyable<LinearRelaxation> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The simplex that solves the relaxation. */
  public enum Simplex {
    /** The dense tableau simplex, {@link DualSimplex}. */
    DENSE,
    /** The sparse revised simplex, {@link SparseDualSimplex}, with every row. */
    SPARSE,
    /** The sparse revised simplex with the rows added and removed lazily. */
    LAZY
  }

  // the scales tried for the multipliers, the largest first
  private static final long[] SCALES = {1L << 24, 1L << 16, 1L << 8, 1};

  // the scale of the rows of the basis inverse the Gomory cuts come from
  private static final long GOMORY_SCALE = 1L << 20;

  private final IntVar[] x;
  // the rows, the cuts last
  private int[][] rowColumns;
  private long[][] rowWeights;
  private long[] rowLo;
  private long[] rowHi;
  private boolean[] hasLo;
  private boolean[] hasHi;
  private final IntVar objective;
  private LpSolver lp;
  private final Simplex simplex;

  // the pivots of simplices dropped for a copy kept before them
  private long droppedPivots;

  // with lazy rows: the row of the relaxation of each row of the simplex, whether each row of the
  // relaxation is in the simplex, and for each row of the simplex the optimal solves in a row in
  // which it was inactive
  private int[] lpRow;
  private boolean[] inLp;
  private int[] inactive;

  // the nonzeros of the rows checked against the solution since the last propagation
  private long scanned;

  // the rows as given, and the sense of the objective, for copies
  private final List<LinearForm> forms = new ArrayList<>();
  private final boolean maximize;

  /** The most simplex pivots per propagation. */
  private int pivotLimit = 500;

  // the relaxation is solved at one call in period; the period doubles after IDLE_RUNS solves that
  // deduce nothing, up to MAX_PERIOD, and halves after one that deduces something
  private static final int IDLE_RUNS = Integer.getInteger("org.jacop.lp.idle", 32);
  private static final int MAX_PERIOD = Integer.getInteger("org.jacop.lp.maxPeriod", 64);
  private int period = 1;
  private int tick;
  private int idle;

  // the largest tableau, rows times columns, that is built, and the tableau entries the pivots of
  // one propagation may update, below the root and at the root
  private static final long MAX_TABLEAU = Long.getLong("org.jacop.lp.maxTableau", 4_000_000L);

  // the most nonzeros of the rows of the sparse simplex
  private static final long MAX_NONZEROS = Long.getLong("org.jacop.lp.maxNonzeros", 4_000_000L);

  // lazy rows: the most rows added per round, the rounds per solve, and the optimal solves a row
  // stays inactive before it leaves the simplex
  private static final int LAZY_BATCH = Integer.getInteger("org.jacop.lp.lazyBatch", 50);
  private static final int LAZY_ROUNDS = Integer.getInteger("org.jacop.lp.lazyRounds", 100);
  private static final int LAZY_AGE = Integer.getInteger("org.jacop.lp.lazyAge", 100);
  private static final long WORK = Long.getLong("org.jacop.lp.work", 20_000_000L);
  private static final long ROOT_WORK = Long.getLong("org.jacop.lp.rootWork", 1_000_000_000L);

  // the most pivots of the first solve, which has the root budget instead of the pivot limit: a
  // root LP that stops at the limit gives neither a bound nor cuts
  private static final int ROOT_PIVOTS = Integer.getInteger("org.jacop.lp.rootPivots", 20_000);

  // the tableau entries earned by each call of consistency, up to WORK; a solve spends the entries
  // its pivots update, a solve that only tightens bounds a PRUNE_DISCOUNT-th of them, and a solve
  // that fails the node fills the credit; while the credit is negative the relaxation is not
  // solved,
  // so a relaxation that finds little costs a bounded share of the search
  private static final long WORK_PER_CALL = Long.getLong("org.jacop.lp.workPerCall", 4096L);
  private static final long PRUNE_DISCOUNT = Long.getLong("org.jacop.lp.pruneDiscount", 16L);
  private long credit = WORK;

  // the solves in a row stopped at the pivot limit; after IDLE_RUNS of them the simplex is taken to
  // be stalling and the relaxation is not solved again
  private int stalled;

  // the deductions of the current branch, for their explanations: variable, form, level
  private final List<IntVar> deducedVar = new ArrayList<>();
  private final List<LinearForm> deducedForm = new ArrayList<>();
  private final List<Integer> deducedLevel = new ArrayList<>();

  // the form propagated when the last failure happened
  private LinearForm failureForm;

  /** Statistics: propagations. */
  public long calls;

  /** Statistics: infeasible relaxations. */
  public long infeasible;

  /** Statistics: failures proved by an exact combination. */
  public long failures;

  /** Statistics: bounds tightened. */
  public long prunings;

  /** Statistics: propagations stopped at the pivot limit. */
  public long limits;

  /** Statistics: the objective bound of the first optimal solve, or NaN. */
  public double rootBound = Double.NaN;

  /** Statistics: the objective bound of the first optimal solve after the cuts, or NaN. */
  public double cutBound = Double.NaN;

  /** Statistics: cuts added. */
  public long cuts;

  /** Statistics: the time of the solves and their propagation, in nanoseconds. */
  public long solveNanos;

  /** Statistics: rows added to the simplex lazily. */
  public long lazyAdded;

  /** Statistics: rows removed from the simplex lazily. */
  public long lazyRemoved;

  // MIR cuts at the root: rounds, cuts per round, and the share of the rows they may add
  private static final boolean CUTS_ENABLED =
      !"false".equals(System.getProperty("org.jacop.lp.cuts"));
  private static final int CUT_ROUNDS = Integer.getInteger("org.jacop.lp.cutRounds", 5);
  private static final int CUTS_PER_ROUND = Integer.getInteger("org.jacop.lp.cutsPerRound", 50);
  private static final int MAX_SOURCES = 100;
  private static final double MAX_PARALLELISM = 0.9;

  // the cuts are made at the first solve only, before any search decision: they use the bounds of
  // that moment, which hold for the whole search
  private boolean cutsTried;

  /**
   * Creates the relaxation of linear forms.
   *
   * @param forms the rows; forms with relation {@code !=} are left out
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   */
  public LinearRelaxation(Collection<LinearForm> forms, IntVar objective, boolean maximize) {
    this(forms, objective, maximize, Simplex.DENSE);
  }

  /**
   * Creates the relaxation of linear forms, solved by the given simplex.
   *
   * @param forms the rows; forms with relation {@code !=} are left out
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param simplex the simplex
   */
  public LinearRelaxation(
      Collection<LinearForm> forms, IntVar objective, boolean maximize, Simplex simplex) {
    numberId = idNumber.incrementAndGet();
    this.simplex = simplex;
    this.objective = objective;
    this.maximize = maximize;
    Map<IntVar, Integer> column = new IdentityHashMap<>();
    List<IntVar> columns = new ArrayList<>();
    List<int[]> rc = new ArrayList<>();
    List<long[]> rw = new ArrayList<>();
    List<long[]> sides = new ArrayList<>();
    if (objective != null) {
      column.put(objective, 0);
      columns.add(objective);
    }
    for (LinearForm f : forms) {
      if (f == null || f.relation() == LinearForm.NE) {
        continue;
      }
      // duplicates merged, zero weights dropped
      Map<Integer, Long> merged = new LinkedHashMap<>();
      boolean overflow = false;
      for (int k = 0; k < f.vars().length; k++) {
        IntVar v = f.vars()[k];
        Integer j = column.get(v);
        if (j == null) {
          j = columns.size();
          column.put(v, j);
          columns.add(v);
        }
        long w = merged.getOrDefault(j, 0L);
        try {
          merged.put(j, Math.addExact(w, f.weights()[k]));
        } catch (ArithmeticException e) {
          overflow = true;
        }
      }
      merged.values().removeIf(w -> w == 0);
      if (overflow || merged.size() < 2) {
        continue;
      }
      this.forms.add(f);
      int[] cs = new int[merged.size()];
      long[] ws = new long[merged.size()];
      int k = 0;
      for (Map.Entry<Integer, Long> e : merged.entrySet()) {
        cs[k] = e.getKey();
        ws[k++] = e.getValue();
      }
      rc.add(cs);
      rw.add(ws);
      sides.add(new long[] {f.relation(), f.c()});
    }
    x = columns.toArray(new IntVar[0]);
    int m = rc.size();
    rowColumns = rc.toArray(new int[0][]);
    rowWeights = rw.toArray(new long[0][]);
    rowLo = new long[m];
    rowHi = new long[m];
    hasLo = new boolean[m];
    hasHi = new boolean[m];
    double[] lo = new double[m];
    double[] hi = new double[m];
    for (int i = 0; i < m; i++) {
      int rel = (int) sides.get(i)[0];
      long c = sides.get(i)[1];
      hasLo[i] = rel != LinearForm.LE;
      hasHi[i] = rel != LinearForm.GE;
      rowLo[i] = c;
      rowHi[i] = c;
      lo[i] = hasLo[i] ? c : Double.NEGATIVE_INFINITY;
      hi[i] = hasHi[i] ? c : Double.POSITIVE_INFINITY;
    }
    double[] cost = new double[x.length];
    if (objective != null) {
      cost[0] = maximize ? -1 : 1;
    }
    lp =
        switch (simplex) {
          case DENSE -> {
            double[][] a = new double[m][x.length];
            for (int i = 0; i < m; i++) {
              for (int k = 0; k < rowColumns[i].length; k++) {
                a[i][rowColumns[i][k]] = rowWeights[i][k];
              }
            }
            yield new DualSimplex(a, lo, hi, cost);
          }
          case SPARSE -> new SparseDualSimplex(sparseRows(m), doubles(m), lo, hi, cost);
          case LAZY -> {
            lpRow = new int[0];
            inLp = new boolean[m];
            inactive = new int[0];
            yield new SparseDualSimplex(new int[0][], new double[0][], lo, hi, cost);
          }
        };
    queueIndex = 4;
    setScope(x);
  }

  /**
   * Creates the relaxation of the linear constraints of a store: the constraints {@link
   * LinearForms#of} reads as linear relations.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @return the relaxation, or null when the store has fewer than two rows or the tableau would
   *     have more than {@code org.jacop.lp.maxTableau} (4,000,000) entries
   */
  public static LinearRelaxation of(Store store, IntVar objective, boolean maximize) {
    return of(store, objective, maximize, List.of(), Set.of(), Simplex.DENSE);
  }

  /**
   * Creates the relaxation of the linear constraints of a store, solved by the given simplex.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param simplex the simplex
   * @return the relaxation, or null when the store has fewer than two rows, or the dense tableau
   *     would have more than {@code org.jacop.lp.maxTableau} (4,000,000) entries, or the rows of a
   *     sparse simplex more than {@code org.jacop.lp.maxNonzeros} (4,000,000) nonzeros
   */
  public static LinearRelaxation of(
      Store store, IntVar objective, boolean maximize, Simplex simplex) {
    return of(store, objective, maximize, List.of(), Set.of(), simplex);
  }

  /**
   * Creates the relaxation of the linear constraints of a store with the dense simplex, with rows
   * that are not store constraints and with variables substituted by their definitions.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param extra rows to add to those of the store's constraints
   * @param substituted variables to replace by their definitions
   * @return the relaxation, or null when it has fewer than two rows or the tableau would have more
   *     than {@code org.jacop.lp.maxTableau} (4,000,000) entries
   */
  public static LinearRelaxation of(
      Store store,
      IntVar objective,
      boolean maximize,
      Collection<LinearForm> extra,
      Set<? extends IntVar> substituted) {
    return of(store, objective, maximize, extra, substituted, Simplex.DENSE);
  }

  /**
   * Creates the relaxation of the linear constraints of a store, with rows that are not store
   * constraints and with variables substituted by their definitions, solved by the given simplex.
   *
   * <p>The extra rows are relations implied by the model that the store holds elsewhere, such as
   * the clauses that lazy clause generation hands to the SAT solver. A substituted variable {@code
   * s} has a definition, an equality row {@code sum a x + w s = c} with {@code w} = 1 or -1 among
   * the rows; the definition is dropped and {@code s} is replaced by {@code w (c - sum a x)} in the
   * other rows. The block sums of a long linear constraint split for lazy clause generation are
   * such variables: substituting them gives the constraint back as one row, so the relaxation has
   * the rows and columns of the unsplit model. A variable without a definition, the objective, and
   * every variable when a substitution overflows a {@code long} are left as they are.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param extra rows to add to those of the store's constraints
   * @param substituted variables to replace by their definitions
   * @param simplex the simplex
   * @return the relaxation, or null when it has fewer than two rows, or the dense tableau would
   *     have more than {@code org.jacop.lp.maxTableau} (4,000,000) entries, or the rows of a sparse
   *     simplex more than {@code org.jacop.lp.maxNonzeros} (4,000,000) nonzeros
   */
  public static LinearRelaxation of(
      Store store,
      IntVar objective,
      boolean maximize,
      Collection<LinearForm> extra,
      Set<? extends IntVar> substituted,
      Simplex simplex) {
    // the constraints of the variables in the store and of the named ones, such as Boolean
    // variables, which have no store index
    Set<Constraint> constraints = new LinkedHashSet<>();
    for (int i = 0; i < store.size(); i++) {
      constraints.addAll(store.vars[i].dom().constraints());
      constraints.addAll(store.valueWatchers(store.vars[i]));
    }
    for (Var v : store.variablesHashMap.values()) {
      constraints.addAll(v.dom().constraints());
      // constraints that watch values, such as long pseudo-Boolean sums, are not in the domains
      constraints.addAll(store.valueWatchers(v));
    }
    constraints.addAll(store.watchedLiteralConstraints());
    List<LinearForm> forms = new ArrayList<>();
    for (Constraint c : constraints) {
      LinearForm f = LinearForms.of(c);
      if (f != null && f.relation() != LinearForm.NE && f.vars().length > 1) {
        forms.add(f);
      }
    }
    for (LinearForm f : extra) {
      if (f != null && f.relation() != LinearForm.NE && f.vars().length > 1) {
        forms.add(f);
      }
    }
    if (!substituted.isEmpty()) {
      forms = substitute(forms, substituted, objective);
    }
    Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
    long rows = 0;
    long nonzeros = 0;
    for (LinearForm f : forms) {
      vars.addAll(Arrays.asList(f.vars()));
      rows++;
      nonzeros += f.vars().length;
      // the dense tableau has a column for each variable and for each row
      if (simplex == Simplex.DENSE
          ? rows * (rows + vars.size() + 1) > MAX_TABLEAU
          : nonzeros > MAX_NONZEROS) {
        return null;
      }
    }
    LinearRelaxation r = new LinearRelaxation(forms, objective, maximize, simplex);
    return r.rows() < 2 ? null : r;
  }

  /**
   * Returns the rows with the variables that have a definition among them replaced by it, and the
   * definitions left out; the rows unchanged when a substitution overflows.
   */
  private static List<LinearForm> substitute(
      List<LinearForm> forms, Set<? extends IntVar> substituted, IntVar objective) {
    Map<IntVar, LinearForm> definition = new IdentityHashMap<>();
    Map<IntVar, Long> weight = new IdentityHashMap<>();
    Set<LinearForm> definitions = Collections.newSetFromMap(new IdentityHashMap<>());
    for (LinearForm f : forms) {
      if (f.relation() != LinearForm.EQ) {
        continue;
      }
      IntVar s = null;
      int count = 0;
      for (int k = 0; k < f.vars().length; k++) {
        IntVar v = f.vars()[k];
        if (substituted.contains(v) && v != objective && !definition.containsKey(v)) {
          if (s == null && Math.abs(f.weights()[k]) == 1) {
            s = v;
          }
          if (v == s) {
            count++;
          }
        }
      }
      if (s != null && count == 1) {
        definition.put(s, f);
        weight.put(s, f.weights()[indexOf(f, s)]);
        definitions.add(f);
      }
    }
    if (definition.isEmpty()) {
      return forms;
    }
    List<LinearForm> result = new ArrayList<>();
    try {
      for (LinearForm f : forms) {
        if (!definitions.contains(f)) {
          result.add(expand(f, definition, weight, 0));
        }
      }
    } catch (ArithmeticException overflow) {
      return forms;
    }
    return result;
  }

  // f with every defined variable replaced by its definition; definitions may use defined
  // variables, up to a small depth
  private static LinearForm expand(
      LinearForm f, Map<IntVar, LinearForm> definition, Map<IntVar, Long> weight, int depth) {
    boolean any = false;
    for (IntVar v : f.vars()) {
      any |= definition.containsKey(v);
    }
    if (!any || depth > 8) {
      return f;
    }
    List<IntVar> vs = new ArrayList<>();
    List<Long> ws = new ArrayList<>();
    long c = f.c();
    for (int k = 0; k < f.vars().length; k++) {
      IntVar v = f.vars()[k];
      long w = f.weights()[k];
      LinearForm d = definition.get(v);
      if (d == null) {
        vs.add(v);
        ws.add(w);
        continue;
      }
      // d: sum a x + ws s = cd, so w s = w ws cd - w ws sum a x (ws is 1 or -1)
      long f0 = Math.multiplyExact(w, weight.get(v));
      c = Math.subtractExact(c, Math.multiplyExact(f0, d.c()));
      for (int j = 0; j < d.vars().length; j++) {
        if (d.vars()[j] != v) {
          vs.add(d.vars()[j]);
          ws.add(Math.negateExact(Math.multiplyExact(f0, d.weights()[j])));
        }
      }
    }
    long[] w = new long[ws.size()];
    for (int k = 0; k < w.length; k++) {
      w[k] = ws.get(k);
    }
    LinearForm e = new LinearForm(vs.toArray(new IntVar[0]), w, c, f.relation());
    return expand(e, definition, weight, depth + 1);
  }

  private static int indexOf(LinearForm f, IntVar v) {
    for (int k = 0; k < f.vars().length; k++) {
      if (f.vars()[k] == v) {
        return k;
      }
    }
    return -1;
  }

  /**
   * Returns the number of rows.
   *
   * @return the rows of the relaxation
   */
  public int rows() {
    return rowColumns.length;
  }

  /**
   * Sets the most simplex pivots per propagation.
   *
   * @param limit the limit
   */
  public void setPivotLimit(int limit) {
    pivotLimit = limit;
  }

  /**
   * Returns the pivots made so far.
   *
   * @return the pivots
   */
  public long pivots() {
    return lp.pivots() + droppedPivots;
  }

  /**
   * Returns the estimated work of a pivot of the simplex, in tableau entries of the dense simplex.
   *
   * @return the work of a pivot
   */
  public long pivotWork() {
    return lp.pivotWork();
  }

  /**
   * Returns the number of columns.
   *
   * @return the columns of the relaxation
   */
  public int columns() {
    return x.length;
  }

  /**
   * Returns the simplex that solves the relaxation.
   *
   * @return the simplex
   */
  public Simplex simplex() {
    return simplex;
  }

  /**
   * Returns the number of rows in the simplex, fewer than {@link #rows()} with lazy rows.
   *
   * @return the rows of the simplex
   */
  public int simplexRows() {
    return lp.rows();
  }

  // the rows of the relaxation, sparse, for the sparse simplex
  private int[][] sparseRows(int m) {
    return Arrays.copyOf(rowColumns, m);
  }

  private double[][] doubles(int m) {
    double[][] w = new double[m][];
    for (int i = 0; i < m; i++) {
      w[i] = new double[rowWeights[i].length];
      for (int k = 0; k < w[i].length; k++) {
        w[i][k] = rowWeights[i][k];
      }
    }
    return w;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {
    // the simplex may skip a node, round its multipliers to nothing, or fix the last variables by
    // its own pruning without being run again; an assignment that breaks a row must still fail
    checkGround();
    credit = Math.min(credit + WORK_PER_CALL, WORK);
    if (++tick < period || credit < 0 || stalled >= IDLE_RUNS) {
      return;
    }
    tick = 0;
    long failed = failures;
    long pruned = prunings;
    long pivots = pivots();
    long work = lp.work();
    boolean first = calls == 0;
    long started = System.nanoTime();
    try {
      solveAndPropagate(store);
    } finally {
      solveNanos += System.nanoTime() - started;
      long cost =
          simplex == Simplex.DENSE
              ? (pivots() - pivots + 1) * lp.pivotWork()
              : Math.max(0, lp.work() - work) + lp.pivotWork() + scanned;
      scanned = 0;
      if (first) {
        // the root solve and its cuts may take up to their own budget; they spend the credit only
        cost = Math.min(cost, WORK);
      }
      // back off while the relaxation finds nothing, come back as soon as it does
      if (failures > failed) {
        idle = 0;
        period = Math.max(1, period / 2);
        credit = WORK;
      } else if (prunings > pruned) {
        idle = 0;
        period = Math.max(1, period / 2);
        credit -= PRUNE_DISCOUNT == 0 ? 0 : cost / PRUNE_DISCOUNT;
      } else {
        credit -= cost;
        if (++idle >= IDLE_RUNS && period < MAX_PERIOD) {
          idle = 0;
          period *= 2;
        }
      }
    }
    checkGround();
  }

  // fails when every variable is fixed and a row does not hold
  private void checkGround() {
    for (IntVar v : x) {
      if (!v.singleton()) {
        return;
      }
    }
    for (int i = 0; i < rows(); i++) {
      int[] cs = rowColumns[i];
      long[] ws = rowWeights[i];
      long sum = 0;
      try {
        for (int k = 0; k < cs.length; k++) {
          sum = Math.addExact(sum, Math.multiplyExact(ws[k], x[cs[k]].value()));
        }
      } catch (ArithmeticException overflow) {
        continue;
      }
      boolean above = hasHi[i] && sum > rowHi[i];
      if (above || hasLo[i] && sum < rowLo[i]) {
        IntVar[] vars = new IntVar[cs.length];
        long[] w = new long[cs.length];
        for (int k = 0; k < cs.length; k++) {
          vars[k] = x[cs[k]];
          w[k] = above ? ws[k] : -ws[k];
        }
        failureForm = new LinearForm(vars, w, above ? rowHi[i] : -rowLo[i], LinearForm.LE);
        failures++;
        throw Store.failException;
      }
    }
  }

  private void solveAndPropagate(Store store) {
    if (rows() == 0) {
      return; // the bounds of the variables alone deduce nothing
    }
    calls++;
    for (int j = 0; j < x.length; j++) {
      lp.setBounds(j, x[j].min(), x[j].max());
    }
    long size = Math.max(1, lp.pivotWork());
    int limit =
        calls == 1
            ? (int) Math.clamp(ROOT_WORK / size, 5, ROOT_PIVOTS)
            : (int) Math.clamp(WORK / size, 5, pivotLimit);
    int status = simplex == Simplex.LAZY ? solveLazily(limit) : lp.solve(limit);
    // the first solve happens in the root propagation, before search makes a decision (also in
    // the free search, which propagates its root a level up, and under lazy clause generation)
    if (status == DualSimplex.OPTIMAL
        && objective != null
        && CUTS_ENABLED
        && !cutsTried
        && calls == 1) {
      cutsTried = true;
      status = cutRounds();
    }
    if (status == DualSimplex.LIMIT) {
      limits++;
      stalled++;
      return;
    }
    stalled = 0;
    double[] y;
    if (status == DualSimplex.INFEASIBLE) {
      infeasible++;
      y = byRow(lp.farkas());
    } else if (objective != null) {
      if (Double.isNaN(rootBound)) {
        rootBound = lp.value(0);
      }
      y = byRow(lp.duals());
    } else {
      return;
    }
    for (long scale : SCALES) {
      long[] lambda = scaled(y, scale);
      if (lambda == null) {
        return;
      }
      LinearForm[] combined = combine(lambda);
      for (LinearForm f : combined) {
        if (f != null) {
          propagate(store, f);
        }
      }
      return;
    }
  }

  // multipliers of the rows of the simplex as multipliers of the rows of the relaxation
  private double[] byRow(double[] y) {
    if (simplex != Simplex.LAZY) {
      return y;
    }
    double[] full = new double[rows()];
    for (int k = 0; k < y.length; k++) {
      full[lpRow[k]] = y[k];
    }
    return full;
  }

  /**
   * Solves with lazy rows: after each optimal solve the rows of the relaxation that its solution
   * breaks, the most broken first, enter the simplex in a batch and it solves again, until it
   * breaks none, it proves infeasibility, or the pivots run out. The rows that stay inactive for
   * {@code LAZY_AGE} optimal solves leave the simplex again.
   *
   * @param limit the most pivots
   * @return the status of the last solve
   */
  private int solveLazily(int limit) {
    long start = lp.pivots();
    int status = LpSolver.OPTIMAL;
    for (int round = 0; round < LAZY_ROUNDS; round++) {
      long left = limit - (lp.pivots() - start);
      if (left <= 0) {
        return LpSolver.LIMIT;
      }
      status = lp.solve((int) left);
      if (status != LpSolver.OPTIMAL) {
        return status;
      }
      if (!addBrokenRows()) {
        ageRows();
        return status;
      }
    }
    return status;
  }

  // adds the rows that the solution of the simplex breaks, at most LAZY_BATCH; false when none
  private boolean addBrokenRows() {
    double[] v = new double[x.length];
    for (int j = 0; j < x.length; j++) {
      v[j] = lp.value(j);
    }
    int m = rows();
    double[] score = new double[m];
    List<Integer> broken = new ArrayList<>();
    for (int i = 0; i < m; i++) {
      if (inLp[i]) {
        continue;
      }
      int[] cs = rowColumns[i];
      long[] ws = rowWeights[i];
      scanned += cs.length;
      double act = 0;
      double norm = 0;
      for (int k = 0; k < cs.length; k++) {
        act += ws[k] * v[cs[k]];
        norm += (double) ws[k] * ws[k];
      }
      double gap = 0;
      if (hasLo[i] && act < rowLo[i] - 1e-6 * (1 + Math.abs(rowLo[i]))) {
        gap = rowLo[i] - act;
      } else if (hasHi[i] && act > rowHi[i] + 1e-6 * (1 + Math.abs(rowHi[i]))) {
        gap = act - rowHi[i];
      }
      if (gap > 0) {
        score[i] = gap / Math.sqrt(norm);
        broken.add(i);
      }
    }
    if (broken.isEmpty()) {
      return false;
    }
    broken.sort(Comparator.comparingDouble((Integer i) -> -score[i]));
    int k = Math.min(LAZY_BATCH, broken.size());
    int[][] cs = new int[k][];
    double[][] ws = new double[k][];
    double[] lo = new double[k];
    double[] hi = new double[k];
    int l = lpRow.length;
    lpRow = Arrays.copyOf(lpRow, l + k);
    inactive = Arrays.copyOf(inactive, l + k);
    for (int q = 0; q < k; q++) {
      int i = broken.get(q);
      cs[q] = rowColumns[i];
      ws[q] = new double[rowWeights[i].length];
      for (int t = 0; t < ws[q].length; t++) {
        ws[q][t] = rowWeights[i][t];
      }
      lo[q] = hasLo[i] ? rowLo[i] : Double.NEGATIVE_INFINITY;
      hi[q] = hasHi[i] ? rowHi[i] : Double.POSITIVE_INFINITY;
      lpRow[l + q] = i;
      inLp[i] = true;
    }
    lp.addRows(cs, ws, lo, hi);
    lazyAdded += k;
    return true;
  }

  // counts the optimal solves in which each row of the simplex is inactive, its slack basic and
  // strictly within its bounds, and removes the rows inactive for LAZY_AGE solves
  private void ageRows() {
    int n = x.length;
    int old = 0;
    for (int k = 0; k < lpRow.length; k++) {
      int i = lpRow[k];
      double s = lp.value(n + k);
      boolean free =
          lp.basicRow(n + k) >= 0
              && (!hasLo[i] || s > rowLo[i] + 1e-6 * (1 + Math.abs(rowLo[i])))
              && (!hasHi[i] || s < rowHi[i] - 1e-6 * (1 + Math.abs(rowHi[i])));
      inactive[k] = free ? inactive[k] + 1 : 0;
      if (inactive[k] >= LAZY_AGE) {
        old++;
      }
    }
    // removals refactorize the basis, so they wait for a batch
    if (old == 0 || old < Math.min(LAZY_BATCH, lpRow.length / 10 + 1)) {
      return;
    }
    int[] gone = new int[old];
    old = 0;
    for (int k = 0; k < lpRow.length; k++) {
      if (inactive[k] >= LAZY_AGE) {
        gone[old++] = k;
      }
    }
    int[] kept = ((SparseDualSimplex) lp).removeRows(gone);
    if (kept == null) {
      return;
    }
    int[] rows2 = new int[kept.length];
    int[] inactive2 = new int[kept.length];
    for (int k = 0; k < kept.length; k++) {
      rows2[k] = lpRow[kept[k]];
      inactive2[k] = inactive[kept[k]];
    }
    for (int i : lpRow) {
      inLp[i] = false;
    }
    for (int i : rows2) {
      inLp[i] = true;
    }
    lazyRemoved += lpRow.length - rows2.length;
    lpRow = rows2;
    inactive = inactive2;
  }

  // y scaled so that its largest entry is about scale, rounded; null when y is zero
  private static long[] scaled(double[] y, long scale) {
    double largest = 0;
    for (double v : y) {
      largest = Math.max(largest, Math.abs(v));
    }
    if (largest == 0 || Double.isNaN(largest) || Double.isInfinite(largest)) {
      return null;
    }
    long[] lambda = new long[y.length];
    for (int i = 0; i < y.length; i++) {
      lambda[i] = Math.round(y[i] / largest * scale);
    }
    return lambda;
  }

  /**
   * The combination {@code sum lambda_i a_i x} of the rows, by column, with its two sides: {@code
   * <= upper} when every row has the side its multiplier needs, and {@code >= lower} likewise.
   */
  private static final class Aggregate {
    private final long[] coef;
    private final long upper;
    private final boolean hasUpper;
    private final long lower;
    private final boolean hasLower;

    Aggregate(long[] coef, long upper, boolean hasUpper, long lower, boolean hasLower) {
      this.coef = coef;
      this.upper = upper;
      this.hasUpper = hasUpper;
      this.lower = lower;
      this.hasLower = hasLower;
    }

    long[] coef() {
      return coef;
    }

    long upper() {
      return upper;
    }

    boolean hasUpper() {
      return hasUpper;
    }

    long lower() {
      return lower;
    }

    boolean hasLower() {
      return hasLower;
    }
  }

  // the combination of the rows by lambda, exact; null on overflow
  private Aggregate aggregate(long[] lambda) {
    long[] coef = new long[x.length];
    long upper = 0; // sum lambda_i a_i x <= upper
    long lower = 0; // sum lambda_i a_i x >= lower
    boolean hasUpper = true;
    boolean hasLower = true;
    try {
      for (int i = 0; i < lambda.length; i++) {
        long l = lambda[i];
        if (l == 0) {
          continue;
        }
        int[] cs = rowColumns[i];
        long[] ws = rowWeights[i];
        for (int k = 0; k < cs.length; k++) {
          coef[cs[k]] = Math.addExact(coef[cs[k]], Math.multiplyExact(l, ws[k]));
        }
        if (l > 0 ? hasHi[i] : hasLo[i]) {
          upper = Math.addExact(upper, Math.multiplyExact(l, l > 0 ? rowHi[i] : rowLo[i]));
        } else {
          hasUpper = false;
        }
        if (l > 0 ? hasLo[i] : hasHi[i]) {
          lower = Math.addExact(lower, Math.multiplyExact(l, l > 0 ? rowLo[i] : rowHi[i]));
        } else {
          hasLower = false;
        }
      }
    } catch (ArithmeticException overflow) {
      return null;
    }
    return new Aggregate(coef, upper, hasUpper, lower, hasLower);
  }

  /**
   * Returns the two inequalities of the combination {@code sum lambda_i a_i x}, each as {@code <=}
   * (one of them may be null when a row lacks the side it needs), or null on overflow.
   */
  private LinearForm[] combine(long[] lambda) {
    Aggregate g = aggregate(lambda);
    if (g == null) {
      return new LinearForm[0];
    }
    long[] coef = g.coef();
    int size = 0;
    for (long c : coef) {
      size += c != 0 ? 1 : 0;
    }
    if (size == 0) {
      return new LinearForm[0];
    }
    IntVar[] vars = new IntVar[size];
    long[] w = new long[size];
    long[] neg = new long[size];
    for (int j = 0, k = 0; j < x.length; j++) {
      if (coef[j] != 0) {
        vars[k] = x[j];
        w[k] = coef[j];
        neg[k++] = -coef[j];
      }
    }
    return new LinearForm[] {
      g.hasUpper() ? new LinearForm(vars, w, g.upper(), LinearForm.LE) : null,
      g.hasLower() ? new LinearForm(vars, neg, -g.lower(), LinearForm.LE) : null
    };
  }

  /**
   * Rounds of MIR cuts at the root, each followed by a re-solve from the same basis. The cuts come
   * from the rows of the tableau of the basic columns with fractional values (Gomory mixed-integer
   * cuts, made exact: the row of the basis inverse is scaled and rounded into an integer
   * combination of the rows, and the MIR is taken of that combination) and from the rows
   * themselves. They use the bounds of the root, so they hold for the whole search, and they are
   * propagated and explained like the other rows.
   *
   * @return the status of the last solve
   */
  private int cutRounds() {
    rootBound = lp.value(0);
    int n = x.length;
    long[] lo = new long[n];
    long[] hi = new long[n];
    for (int j = 0; j < n; j++) {
      lo[j] = x[j].min();
      hi[j] = x[j].max();
    }
    int original = rows();
    Set<List<Long>> seen = new HashSet<>();
    int status = DualSimplex.OPTIMAL;
    double[] value = new double[n];
    for (int round = 0; round < CUT_ROUNDS; round++) {
      for (int j = 0; j < n; j++) {
        value[j] = lp.value(j);
      }
      List<MirCut> found = new ArrayList<>();
      List<Integer> sources = new ArrayList<>();
      for (int j = 0; j < n; j++) {
        double f = value[j] - Math.floor(value[j]);
        if (lp.basicRow(j) >= 0 && f > 0.01 && f < 0.99) {
          sources.add(j);
        }
      }
      sources.sort(
          Comparator.comparingDouble(j -> Math.abs(value[j] - Math.floor(value[j]) - 0.5)));
      for (int j : sources.subList(0, Math.min(MAX_SOURCES, sources.size()))) {
        long[] lambda = scaled(byRow(lp.inverseRow(lp.basicRow(j))), GOMORY_SCALE);
        if (lambda != null) {
          mir(aggregate(lambda), value, lo, hi, found);
        }
      }
      long[] unit = new long[rows()];
      for (int i = 0; i < original; i++) {
        unit[i] = 1;
        mir(aggregate(unit), value, lo, hi, found);
        unit[i] = 0;
      }
      found.sort(Comparator.comparingDouble((MirCut c) -> -c.efficacy));
      List<MirCut> chosen = new ArrayList<>();
      for (MirCut c : found) {
        long m = (long) lp.rows() + chosen.size() + 1;
        if (chosen.size() >= CUTS_PER_ROUND
            || simplex == Simplex.DENSE && m * (m + n) > MAX_TABLEAU) {
          break;
        }
        List<Long> key = new ArrayList<>();
        for (int k = 0; k < c.columns.length; k++) {
          key.add((long) c.columns[k]);
          key.add(c.weights[k]);
        }
        key.add(c.rhs);
        if (!seen.contains(key) && orthogonal(c, chosen)) {
          seen.add(key);
          chosen.add(c);
        }
      }
      if (chosen.isEmpty()) {
        break;
      }
      LpSolver kept = lp.copy();
      int[] keptRows = lpRow;
      long pivots = lp.pivots();
      double before = lp.value(0);
      addCuts(chosen);
      long size = Math.max(1, lp.pivotWork());
      status = lp.solve(Math.clamp(ROOT_WORK / CUT_ROUNDS / size, 5, ROOT_PIVOTS));
      if (status == DualSimplex.OPTIMAL
          && Math.abs(lp.value(0) - before) <= 1e-6 * (1 + Math.abs(before))) {
        // cuts that do not move the bound only make each solve dearer: back to the LP before them
        dropCuts(chosen.size(), kept, keptRows);
        break;
      }
      if (status != DualSimplex.OPTIMAL) {
        if (status == DualSimplex.LIMIT) {
          dropCuts(chosen.size(), kept, keptRows);
          status = DualSimplex.OPTIMAL;
        }
        break;
      }
    }
    if (status == DualSimplex.OPTIMAL) {
      cutBound = lp.value(0);
    }
    return status;
  }

  // whether the cut is far enough from parallel to each of the cuts chosen
  private static boolean orthogonal(MirCut c, List<MirCut> chosen) {
    for (MirCut o : chosen) {
      double dot = 0;
      int p = 0;
      int q = 0;
      while (p < c.columns.length && q < o.columns.length) {
        if (c.columns[p] == o.columns[q]) {
          dot += (double) c.weights[p] * o.weights[q];
          p++;
          q++;
        } else if (c.columns[p] < o.columns[q]) {
          p++;
        } else {
          q++;
        }
      }
      if (Math.abs(dot) > MAX_PARALLELISM * c.norm * o.norm) {
        return false;
      }
    }
    return true;
  }

  private static void mir(Aggregate g, double[] value, long[] lo, long[] hi, List<MirCut> found) {
    if (g == null) {
      return;
    }
    if (g.hasUpper()) {
      MirCut c = MirCut.of(g.coef(), g.upper(), value, lo, hi);
      if (c != null) {
        found.add(c);
      }
    }
    if (g.hasLower()) {
      long[] neg = new long[g.coef().length];
      for (int j = 0; j < neg.length; j++) {
        if (g.coef()[j] == Long.MIN_VALUE || g.lower() == Long.MIN_VALUE) {
          return;
        }
        neg[j] = -g.coef()[j];
      }
      MirCut c = MirCut.of(neg, -g.lower(), value, lo, hi);
      if (c != null) {
        found.add(c);
      }
    }
  }

  // removes the last k rows, the cuts of the last round, and goes back to the simplex before them
  private void dropCuts(int k, LpSolver kept, int[] keptRows) {
    int m = rows() - k;
    rowColumns = Arrays.copyOf(rowColumns, m);
    rowWeights = Arrays.copyOf(rowWeights, m);
    rowLo = Arrays.copyOf(rowLo, m);
    rowHi = Arrays.copyOf(rowHi, m);
    hasLo = Arrays.copyOf(hasLo, m);
    hasHi = Arrays.copyOf(hasHi, m);
    droppedPivots += lp.pivots() - kept.pivots();
    lp = kept;
    if (simplex == Simplex.LAZY) {
      lpRow = keptRows;
      inLp = Arrays.copyOf(inLp, m);
      Arrays.fill(inLp, false);
      for (int i : lpRow) {
        inLp[i] = true;
      }
      inactive = new int[lpRow.length];
    }
    cuts -= k;
  }

  // appends the cuts as rows sum w x <= rhs, to the rows and to the simplex
  private void addCuts(List<MirCut> chosen) {
    int m = rows();
    int k = chosen.size();
    rowColumns = Arrays.copyOf(rowColumns, m + k);
    rowWeights = Arrays.copyOf(rowWeights, m + k);
    rowLo = Arrays.copyOf(rowLo, m + k);
    rowHi = Arrays.copyOf(rowHi, m + k);
    hasLo = Arrays.copyOf(hasLo, m + k);
    hasHi = Arrays.copyOf(hasHi, m + k);
    int[][] cs = new int[k][];
    double[][] ws = new double[k][];
    double[] lo = new double[k];
    double[] hi = new double[k];
    for (int q = 0; q < k; q++) {
      MirCut c = chosen.get(q);
      rowColumns[m + q] = c.columns;
      rowWeights[m + q] = c.weights;
      rowHi[m + q] = c.rhs;
      hasHi[m + q] = true;
      cs[q] = c.columns;
      ws[q] = new double[c.weights.length];
      for (int t = 0; t < c.columns.length; t++) {
        ws[q][t] = c.weights[t];
      }
      lo[q] = Double.NEGATIVE_INFINITY;
      hi[q] = (double) c.rhs;
    }
    if (simplex == Simplex.LAZY) {
      // the cuts go into the simplex at once, as rows its solution breaks
      inLp = Arrays.copyOf(inLp, m + k);
      int l = lpRow.length;
      lpRow = Arrays.copyOf(lpRow, l + k);
      inactive = Arrays.copyOf(inactive, l + k);
      for (int q = 0; q < k; q++) {
        lpRow[l + q] = m + q;
        inLp[m + q] = true;
      }
    }
    lp.addRows(cs, ws, lo, hi);
    cuts += k;
  }

  // bounds propagation of sum w x <= c, exact; nothing on overflow
  private void propagate(Store store, LinearForm f) {
    IntVar[] vars = f.vars();
    long[] w = f.weights();
    long c = f.c();
    long smallest = 0;
    long[] least = new long[vars.length];
    try {
      for (int k = 0; k < vars.length; k++) {
        least[k] = Math.multiplyExact(w[k], w[k] > 0 ? vars[k].min() : vars[k].max());
        smallest = Math.addExact(smallest, least[k]);
      }
    } catch (ArithmeticException overflow) {
      return;
    }
    failureForm = f;
    if (smallest > c) {
      failures++;
      throw Store.failException;
    }
    long room;
    try {
      room = Math.subtractExact(c, smallest);
    } catch (ArithmeticException overflow) {
      return; // the slack is larger than any bound it could tighten
    }
    for (int k = 0; k < vars.length; k++) {
      long wk = w[k];
      // wk * v <= least[k] + room
      long limit;
      try {
        limit = Math.addExact(least[k], room);
      } catch (ArithmeticException overflow) {
        continue;
      }
      IntVar v = vars[k];
      if (wk > 0) {
        long bound = Math.floorDiv(limit, wk);
        if (bound < v.max()) {
          record(store, v, f);
          v.domain.inMax(store.level, v, (int) Math.max(bound, v.min() - 1L));
        }
      } else {
        long bound = Math.ceilDiv(limit, wk);
        if (bound > v.min()) {
          record(store, v, f);
          v.domain.inMin(store.level, v, (int) Math.min(bound, v.max() + 1L));
        }
      }
    }
  }

  private void record(Store store, IntVar v, LinearForm f) {
    prunings++;
    deducedVar.add(v);
    deducedForm.add(f);
    deducedLevel.add(store.level);
  }

  @Override
  public void removeLevel(int level) {
    int k = deducedLevel.size();
    while (k > 0 && deducedLevel.get(k - 1) >= level) {
      k--;
    }
    deducedVar.subList(k, deducedVar.size()).clear();
    deducedForm.subList(k, deducedForm.size()).clear();
    deducedLevel.subList(k, deducedLevel.size()).clear();
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar v = trail.variable(entry);
    int mark = out.size();
    for (int k = deducedVar.size() - 1; k >= 0; k--) {
      if (deducedVar.get(k) == v) {
        if (deducedForm.get(k).explain(trail, entry, out)) {
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return failureForm != null && failureForm.explainFailure(trail, out);
  }

  @Override
  public boolean checksReasons() {
    return true;
  }

  @Override
  public LinearRelaxation copy(VarMap map) {
    List<LinearForm> copies = new ArrayList<>();
    for (LinearForm f : forms) {
      copies.add(new LinearForm(map.get(f.vars()), f.weights(), f.c(), f.relation()));
    }
    LinearRelaxation c =
        new LinearRelaxation(
            copies, objective == null ? null : map.get(objective), maximize, simplex);
    c.pivotLimit = pivotLimit;
    return c;
  }

  @Override
  public String toString() {
    return id() + " : LinearRelaxation(" + x.length + " columns, " + rows() + " rows)";
  }
}
