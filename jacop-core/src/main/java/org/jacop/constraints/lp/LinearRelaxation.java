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
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LinearRelaxation extends Constraint
    implements Explainable, Stateful, Copyable<LinearRelaxation> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

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
  private final DualSimplex lp;

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

  // MIR cuts at the root: rounds, cuts per round, and the share of the rows they may add
  private static final boolean CUTS = !"false".equals(System.getProperty("org.jacop.lp.cuts"));
  private static final int CUT_ROUNDS = Integer.getInteger("org.jacop.lp.cutRounds", 5);
  private static final int CUTS_PER_ROUND = Integer.getInteger("org.jacop.lp.cutsPerRound", 50);
  private static final int MAX_SOURCES = 100;
  private static final double MAX_PARALLELISM = 0.9;

  // the store level the relaxation was imposed at; cuts use the bounds of this level only, so that
  // they hold for the whole search
  private int rootLevel = -1;
  private boolean cutsTried;

  /**
   * Creates the relaxation of linear forms.
   *
   * @param forms the rows; forms with relation {@code !=} are left out
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   */
  public LinearRelaxation(Collection<LinearForm> forms, IntVar objective, boolean maximize) {
    numberId = idNumber.incrementAndGet();
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
    double[][] a = new double[m][x.length];
    for (int i = 0; i < m; i++) {
      int rel = (int) sides.get(i)[0];
      long c = sides.get(i)[1];
      hasLo[i] = rel != LinearForm.LE;
      hasHi[i] = rel != LinearForm.GE;
      rowLo[i] = c;
      rowHi[i] = c;
      lo[i] = hasLo[i] ? c : Double.NEGATIVE_INFINITY;
      hi[i] = hasHi[i] ? c : Double.POSITIVE_INFINITY;
      for (int k = 0; k < rowColumns[i].length; k++) {
        a[i][rowColumns[i][k]] = rowWeights[i][k];
      }
    }
    double[] cost = new double[x.length];
    if (objective != null) {
      cost[0] = maximize ? -1 : 1;
    }
    lp = new DualSimplex(a, lo, hi, cost);
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
    if (store.watchedConstraints != null) {
      store.watchedConstraints.values().forEach(constraints::addAll);
    }
    List<LinearForm> forms = new ArrayList<>();
    Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
    long rows = 0;
    for (Constraint c : constraints) {
      LinearForm f = LinearForms.of(c);
      if (f != null && f.relation() != LinearForm.NE && f.vars().length > 1) {
        forms.add(f);
        vars.addAll(Arrays.asList(f.vars()));
        rows++;
        // the dense tableau has a column for each variable and for each row
        if (rows * (rows + vars.size() + 1) > MAX_TABLEAU) {
          return null;
        }
      }
    }
    LinearRelaxation r = new LinearRelaxation(forms, objective, maximize);
    return r.rows() < 2 ? null : r;
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
    return lp.totalPivots;
  }

  @Override
  public void impose(Store store) {
    rootLevel = store.level;
    super.impose(store);
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
    long pivots = lp.totalPivots;
    boolean first = calls == 0;
    try {
      solveAndPropagate(store);
    } finally {
      long cost = (lp.totalPivots - pivots + 1) * ((long) rows() * (rows() + x.length));
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
    long size = (long) rows() * (rows() + x.length);
    int status =
        lp.solve(
            calls == 1
                ? (int) Math.clamp(ROOT_WORK / size, 5, ROOT_PIVOTS)
                : (int) Math.clamp(WORK / size, 5, pivotLimit));
    if (status == DualSimplex.OPTIMAL
        && objective != null
        && CUTS
        && !cutsTried
        && store.level == rootLevel) {
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
      y = lp.farkas();
    } else if (objective != null) {
      if (Double.isNaN(rootBound)) {
        rootBound = lp.value(0);
      }
      y = lp.duals();
    } else {
      return;
    }
    for (long scale : SCALES) {
      long[] lambda = scaled(y, scale);
      if (lambda == null) {
        return;
      }
      LinearForm[] combined = combine(lambda);
      if (combined == null) {
        continue;
      }
      for (LinearForm f : combined) {
        if (f != null) {
          propagate(store, f);
        }
      }
      return;
    }
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
  private record Aggregate(
      long[] coef, long upper, boolean hasUpper, long lower, boolean hasLower) {}

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
      return null;
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
        long[] lambda = scaled(lp.inverseRow(lp.basicRow(j)), GOMORY_SCALE);
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
        long m = rows() + chosen.size() + 1L;
        if (chosen.size() >= CUTS_PER_ROUND || m * (m + n) > MAX_TABLEAU) {
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
      addCuts(chosen);
      double before = lp.value(0);
      long size = (long) rows() * (rows() + n);
      status = lp.solve((int) Math.clamp(ROOT_WORK / CUT_ROUNDS / size, 5, ROOT_PIVOTS));
      if (status != DualSimplex.OPTIMAL
          || Math.abs(lp.value(0) - before) <= 1e-6 * (1 + Math.abs(before))) {
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
      for (int p = 0, q = 0; p < c.columns.length && q < o.columns.length; ) {
        if (c.columns[p] == o.columns[q]) {
          dot += (double) c.weights[p++] * o.weights[q++];
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
    double[][] a = new double[k][x.length];
    double[] lo = new double[k];
    double[] hi = new double[k];
    for (int q = 0; q < k; q++) {
      MirCut c = chosen.get(q);
      rowColumns[m + q] = c.columns;
      rowWeights[m + q] = c.weights;
      rowHi[m + q] = c.rhs;
      hasHi[m + q] = true;
      for (int t = 0; t < c.columns.length; t++) {
        a[q][c.columns[t]] = c.weights[t];
      }
      lo[q] = Double.NEGATIVE_INFINITY;
      hi[q] = c.rhs;
    }
    lp.addRows(a, lo, hi);
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
        new LinearRelaxation(copies, objective == null ? null : map.get(objective), maximize);
    c.pivotLimit = pivotLimit;
    return c;
  }

  @Override
  public String toString() {
    return id() + " : LinearRelaxation(" + x.length + " columns, " + rows() + " rows)";
  }
}
