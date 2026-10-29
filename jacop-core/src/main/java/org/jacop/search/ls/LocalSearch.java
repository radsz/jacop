/*
 * LocalSearch.java
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

package org.jacop.search.ls;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SplittableRandom;
import java.util.function.Consumer;
import java.util.function.IntSupplier;
import java.util.function.ToIntFunction;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.constraints.AbstractReifiedConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XplusClteqZImplied;
import org.jacop.constraints.cumulative.EnergyPrecedence;
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;

/**
 * Local search over the constraints of a store, in the style of feasibility jump (Luteberget and
 * Sartor, 2023) and CP-SAT's violation local search: every variable has a value, each constraint
 * has a violation and a weight, and a move changes one variable to the value that most lowers the
 * weighted violation. When no move of a violated constraint helps, its weight grows, which moves
 * the search out of the local minimum.
 *
 * <p>Linear constraints (also reified or implied ones, clauses and fixed conjunctions) are
 * evaluated incrementally, with the amount by which they are violated. Any other constraint that
 * can be copied is evaluated by propagating its copy in a scratch store over the assigned values,
 * as violated or not. Constraints over other kinds of variables are not evaluated, so an assignment
 * the local search takes as a solution is always checked by propagation in the store before it is
 * reported.
 *
 * <p>For optimisation, each solution adds the bound {@code cost < best} as a constraint of the
 * local search, which then looks for a better solution.
 *
 * <p>The store is left at the level it was at before {@link #solve()}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LocalSearch {

  /** How a local search ended. */
  public enum Status {
    /** A solution was found and checked in the store; for optimisation it is not proven optimal. */
    SATISFIED,
    /** A limit was reached or the search was stopped before any solution was found. */
    UNKNOWN,
    /** The store has variables other than integer ones that are not fixed. */
    NOT_APPLICABLE
  }

  private static final int LE = LinearForm.LE;
  private static final int GE = LinearForm.GE;
  private static final int EQ = LinearForm.EQ;
  private static final int NE = LinearForm.NE;

  // variables of a large constraint scanned at each step
  private static final int SCAN_LIMIT = 24;
  // domains up to this size are tried value by value
  private static final int SMALL_DOMAIN = 8;
  private static final double WEIGHT_LIMIT = 1e12;

  private final Store store;
  private final IntVar cost;
  private final long timeLimitMillis;
  private final Consumer<LocalSearch> solutionHandler;
  private final IntSupplier sharedBound;
  private final boolean firstSolution;
  private final SplittableRandom random;
  private final IntVar[] order;
  private final IntVar[] hintVars;
  private final int[] hintValues;
  private final long stallSteps;

  // the variables, their root domains and current values
  private IntVar[] vars;
  private IntDomain[] domains;
  private int[] val;
  private final Map<IntVar, Integer> index = new IdentityHashMap<>();

  // the constraints; linear ones have rows, the others a copy in the scratch store
  private int m;
  private double[] weight;
  private long[] viol;
  private int[][] scope;
  private long[][] coef;
  private long[] rhs;
  private int[] rel;
  private int[] enforcer;
  private int[] enforcedValue;
  private long[] lhs;
  private IntVar[][] copies;
  private Store scratch;
  // constraints that measure their own violation
  private Violation[] measures;
  // the index of each variable of the store among the variables of the local search, or -1
  private int[] slot;
  private final Values values = new Values();
  // the variables of the order given come first; a solution fixes them first
  private int orderCount;

  // occurrences of each variable: the constraints and its coefficient in each (0 if not linear)
  private int[][] occ;
  private long[][] occCoef;

  // the violated constraints
  private int[] violated;
  private int[] violatedPos;
  private int violatedCount;

  // the row cost <= bound - 1 for optimisation, or -1
  private int boundRow = -1;
  private int costIndex = -1;

  private long[] tabu;
  private int[] bestAssignment;
  private int[] solution;
  // the values of the integer variables of the store in the best solution, by store index
  private int[] storeSolution;
  private int solutionCost;

  private long steps;
  private long moves;
  private long restarts;
  private long solutions;
  private long rejected;
  private long evaluations;
  private int linearCount;
  private int checkedCount;
  private int unsupportedCount;
  // constraint classes by how they are evaluated, for statistics
  private final Map<String, Integer> classes = new java.util.TreeMap<>();
  private long deadline;
  private volatile boolean stopRequested;

  private LocalSearch(Builder b) {
    store = b.store;
    cost = b.cost;
    timeLimitMillis = b.timeLimitMillis;
    solutionHandler = b.solutionHandler;
    sharedBound = b.sharedBound;
    firstSolution = b.firstSolution || b.cost == null;
    random = new SplittableRandom(b.seed);
    order = b.order;
    hintVars = b.hintVars;
    hintValues = b.hintValues;
    stallSteps = b.stallSteps;
  }

  /**
   * Starts building a local search.
   *
   * @param store the store with the model, at the root of the search.
   * @return the builder.
   */
  public static Builder builder(Store store) {
    return new Builder(store);
  }

  /**
   * Runs the local search until a solution is found (for satisfaction), the time limit, or {@link
   * #stop()}.
   *
   * @return how the search ended.
   */
  public Status solve() {
    deadline = timeLimitMillis > 0 ? System.currentTimeMillis() + timeLimitMillis : Long.MAX_VALUE;
    if (!applicable()) {
      return Status.NOT_APPLICABLE;
    }
    build();
    if (timeUp()) {
      return Status.UNKNOWN;
    }
    initialAssignment();
    search();
    return solution != null ? Status.SATISFIED : Status.UNKNOWN;
  }

  /** Stops the search; it may be called from another thread. */
  public void stop() {
    stopRequested = true;
  }

  /**
   * Returns the values of variables in the best solution found.
   *
   * @param of the variables.
   * @return their values, or null when no solution was found.
   */
  public int[] getSolution(IntVar[] of) {
    if (solution == null) {
      return null;
    }
    int[] result = new int[of.length];
    for (int k = 0; k < of.length; k++) {
      int s = of[k].index();
      result[k] = s >= 0 && s < storeSolution.length ? storeSolution[s] : of[k].min();
    }
    return result;
  }

  /**
   * Returns the value of the cost variable in the best solution.
   *
   * @return the cost.
   */
  public int getCostValue() {
    return solutionCost;
  }

  /**
   * Returns the number of solutions checked in the store and reported.
   *
   * @return the solutions.
   */
  public long getSolutions() {
    return solutions;
  }

  /**
   * Returns the number of steps (a violated constraint examined).
   *
   * @return the steps.
   */
  public long getSteps() {
    return steps;
  }

  /**
   * Returns the number of moves (a variable changed).
   *
   * @return the moves.
   */
  public long getMoves() {
    return moves;
  }

  /**
   * Returns the number of restarts from the best assignment.
   *
   * @return the restarts.
   */
  public long getRestarts() {
    return restarts;
  }

  /**
   * Returns the number of assignments the local search took for solutions that the store rejected.
   *
   * @return the rejected assignments.
   */
  public long getRejected() {
    return rejected;
  }

  /**
   * Returns how many constraints were evaluated as linear rows, by a copy, and not at all.
   *
   * @return linear, copied and unsupported constraints.
   */
  public int[] getConstraintCounts() {
    return new int[] {linearCount, checkedCount, unsupportedCount};
  }

  /**
   * Returns the number of evaluations of copied constraints.
   *
   * @return the evaluations.
   */
  public long getEvaluations() {
    return evaluations;
  }

  // ---------------------------------------------------------------- model

  private boolean applicable() {
    for (int i = 0; i < store.size(); i++) {
      Var v = store.vars[i];
      if (v != null && !(v instanceof IntVar) && !v.singleton()) {
        return false;
      }
    }
    return true;
  }

  private void build() {
    Set<Constraint> constraints = store.getConstraints();
    List<IntVar> varList = new ArrayList<>();
    if (order != null) {
      for (IntVar x : order) {
        addVar(x, varList);
      }
    }
    orderCount = varList.size();
    if (cost != null) {
      addVar(cost, varList);
    }
    List<Object[]> rows = new ArrayList<>();
    List<Constraint> checked = new ArrayList<>();
    List<Violation> measured = new ArrayList<>();
    for (Constraint c : constraints) {
      if (c instanceof LinearRelaxation || c instanceof EnergyPrecedence) {
        // only add pruning to the other constraints
        continue;
      }
      int before = rows.size();
      if (compileLinear(c, rows, varList)) {
        classes.merge("L:" + c.getClass().getSimpleName(), 1, Integer::sum);
        continue;
      }
      rows.subList(before, rows.size()).clear();
      Violation measure = measure(c);
      if (measure != null && intArguments(c)) {
        classes.merge("M:" + c.getClass().getSimpleName(), 1, Integer::sum);
        for (Var x : c.arguments()) {
          addVar((IntVar) x, varList);
        }
        measured.add(measure);
        measuredConstraints.add(c);
        continue;
      }
      if (supportedCopy(c, varList)) {
        classes.merge("C:" + className(c), 1, Integer::sum);
        checked.add(c);
        continue;
      }
      classes.merge("U:" + className(c), 1, Integer::sum);
      unsupportedCount++;
      for (Var v : c.arguments()) {
        if (v instanceof IntVar x) {
          addVar(x, varList);
        }
      }
    }
    int n = varList.size();
    vars = varList.toArray(new IntVar[0]);
    domains = new IntDomain[n];
    for (int i = 0; i < n; i++) {
      domains[i] = vars[i].dom().cloneLight();
    }
    val = new int[n];
    tabu = new long[n];
    // one row more for the bound on the cost
    m = rows.size() + measured.size() + checked.size() + (cost != null ? 1 : 0);
    weight = new double[m];
    Arrays.fill(weight, 1.0);
    viol = new long[m];
    scope = new int[m][];
    coef = new long[m][];
    rhs = new long[m];
    rel = new int[m];
    enforcer = new int[m];
    Arrays.fill(enforcer, -1);
    enforcedValue = new int[m];
    lhs = new long[m];
    copies = new IntVar[m][];
    measures = new Violation[m];
    int c = 0;
    for (Object[] row : rows) {
      scope[c] = (int[]) row[0];
      coef[c] = (long[]) row[1];
      rhs[c] = (long) row[2];
      rel[c] = (int) row[3];
      int[] enf = (int[]) row[4];
      if (enf != null) {
        enforcer[c] = enf[0];
        enforcedValue[c] = enf[1];
      }
      c++;
    }
    linearCount = rows.size();
    slot = new int[store.size()];
    Arrays.fill(slot, -1);
    for (int i = 0; i < n; i++) {
      int si = vars[i].index();
      if (si >= 0 && si < slot.length) {
        slot[si] = i;
      }
    }
    for (int k = 0; k < measured.size(); k++) {
      measures[c] = measured.get(k);
      scope[c] = scopeOf(measuredConstraints.get(k));
      c++;
    }
    measuredCount = measured.size();
    scratch = checked.isEmpty() ? null : new Store();
    for (Constraint k : checked) {
      if (copy(k, c)) {
        c++;
      } else {
        unsupportedCount++;
      }
    }
    checkedCount = c - linearCount - measuredCount;
    if (cost != null) {
      costIndex = index.get(cost);
      boundRow = c;
      scope[c] = new int[] {costIndex};
      coef[c] = new long[] {1};
      rhs[c] = Long.MAX_VALUE / 4;
      rel[c] = LE;
      c++;
    }
    m = c;
    if (scratch != null && !scratch.consistency()) {
      // a copy fails on the root domains; it cannot be evaluated
      scratch = null;
    }
    buildOccurrences();
    violated = new int[m];
    violatedPos = new int[m];
    Arrays.fill(violatedPos, -1);
  }

  // the constraints read through their own violation, in the order of measures
  private final List<Constraint> measuredConstraints = new ArrayList<>();
  private int measuredCount;

  /**
   * The violation of a constraint that measures it itself, or of a reified or implied one whose
   * nested constraint does; null for other constraints.
   */
  private static Violation measure(Constraint c) {
    if (c instanceof Violation v) {
      return v;
    }
    if ((c.getClass() == Reified.class || c.getClass() == Implies.class)
        && ((AbstractReifiedConstraint) c).c instanceof Violation inner) {
      IntVar b = ((AbstractReifiedConstraint) c).b;
      boolean reified = c.getClass() == Reified.class;
      return value -> {
        boolean holds = inner.violation(value) == 0;
        boolean on = value.applyAsInt(b) == 1;
        return (reified ? on == holds : !on || holds) ? 0 : 1;
      };
    }
    return null;
  }

  private static String className(Constraint c) {
    String name = c.getClass().getSimpleName();
    return c instanceof AbstractReifiedConstraint r
        ? name + "(" + r.c.getClass().getSimpleName() + ")"
        : name;
  }

  private static boolean intArguments(Constraint c) {
    for (Var v : c.arguments()) {
      if (!(v instanceof IntVar)) {
        return false;
      }
    }
    return true;
  }

  private int[] scopeOf(Constraint c) {
    Set<Var> args = c.arguments();
    int[] s = new int[args.size()];
    int k = 0;
    for (Var v : args) {
      s[k++] = index.get(v);
    }
    return s;
  }

  /** The values of the variables, with one of them moved to another value. */
  private final class Values implements ToIntFunction<IntVar> {

    int moved = -1;
    int movedValue;

    @Override
    public int applyAsInt(IntVar x) {
      int s = x.index();
      int i = s >= 0 && s < slot.length ? slot[s] : -1;
      if (i < 0) {
        Integer j = index.get(x);
        if (j == null) {
          return x.min();
        }
        i = j;
      }
      return i == moved ? movedValue : val[i];
    }
  }

  private int addVar(IntVar x, List<IntVar> varList) {
    Integer i = index.get(x);
    if (i != null) {
      return i;
    }
    index.put(x, varList.size());
    varList.add(x);
    return varList.size() - 1;
  }

  /**
   * Adds the rows of a linear constraint, or of a reified or implied one: {@code b <=> form} is the
   * two rows {@code b = 1 -> form} and {@code b = 0 -> not form}.
   */
  private boolean compileLinear(Constraint c, List<Object[]> rows, List<IntVar> varList) {
    LinearForm f = LinearForms.of(c);
    if (f != null) {
      return addRow(f, null, rows, varList);
    }
    if (c instanceof XplusClteqZImplied h) {
      LinearForm row =
          new LinearForm(new IntVar[] {h.x, h.z}, new long[] {1, -1}, -h.c, LinearForm.LE);
      if (h.b.singleton()) {
        return h.b.value() == 0 || addRow(row, null, rows, varList);
      }
      return addRow(row, new int[] {addVar(h.b, varList), 1}, rows, varList);
    }
    if (c instanceof AbstractReifiedConstraint r
        && (c.getClass() == Reified.class || c.getClass() == Implies.class)) {
      LinearForm inner = LinearForms.of(r.c);
      if (inner == null) {
        return false;
      }
      if (r.b.singleton()) {
        if (r.b.value() == 1) {
          return addRow(inner, null, rows, varList);
        }
        return c.getClass() != Reified.class || addRow(inner.negated(), null, rows, varList);
      }
      int b = addVar(r.b, varList);
      boolean ok = addRow(inner, new int[] {b, 1}, rows, varList);
      if (ok && c.getClass() == Reified.class) {
        ok = addRow(inner.negated(), new int[] {b, 0}, rows, varList);
      }
      return ok;
    }
    return false;
  }

  private boolean addRow(LinearForm f, int[] enf, List<Object[]> rows, List<IntVar> varList) {
    // a variable may occur more than once in a form
    Map<IntVar, Long> merged = new IdentityHashMap<>();
    List<IntVar> distinct = new ArrayList<>();
    long constant = 0;
    try {
      for (int k = 0; k < f.vars().length; k++) {
        IntVar x = f.vars()[k];
        long w = f.weights()[k];
        if (x.singleton()) {
          constant = Math.addExact(constant, Math.multiplyExact(w, x.value()));
        } else if (merged.merge(x, w, Long::sum) == w) {
          distinct.add(x);
        }
      }
    } catch (ArithmeticException overflow) {
      return false;
    }
    int[] s = new int[distinct.size()];
    long[] w = new long[distinct.size()];
    int k = 0;
    for (IntVar x : distinct) {
      long a = merged.get(x);
      if (a != 0) {
        s[k] = addVar(x, varList);
        w[k] = a;
        k++;
      }
    }
    rows.add(
        new Object[] {
          Arrays.copyOf(s, k), Arrays.copyOf(w, k), f.c() - constant, f.relation(), enf
        });
    return true;
  }

  private boolean supportedCopy(Constraint c, List<IntVar> varList) {
    if (!Copyable.canCopy(c)) {
      return false;
    }
    for (Var v : c.arguments()) {
      if (!(v instanceof IntVar x)
          || (x.getClass() != IntVar.class && !(x instanceof BooleanVar))) {
        return false;
      }
    }
    for (Var v : c.arguments()) {
      addVar((IntVar) v, varList);
    }
    return true;
  }

  // imposes a copy of the constraint over fresh variables in the scratch store
  private boolean copy(Constraint c, int row) {
    Map<Var, Var> map = new IdentityHashMap<>();
    List<Integer> s = new ArrayList<>();
    List<IntVar> ys = new ArrayList<>();
    for (Var v : c.arguments()) {
      IntVar x = (IntVar) v;
      if (map.containsKey(x)) {
        continue;
      }
      IntVar y =
          x instanceof BooleanVar
              ? new BooleanVar(scratch, x.min(), x.max())
              : new IntVar(scratch, x.dom().cloneLight());
      map.put(x, y);
      s.add(index.get(x));
      ys.add(y);
    }
    VarMap varMap =
        new VarMap() {
          @Override
          public Store target() {
            return scratch;
          }

          @Override
          @SuppressWarnings("unchecked")
          public <V extends Var> V get(V v) {
            Var y = map.get(v);
            if (y == null) {
              throw new IllegalArgumentException(v + " is not a variable of the constraint");
            }
            return (V) y;
          }
        };
    try {
      scratch.impose(((Copyable<?>) c).copy(varMap));
    } catch (RuntimeException e) {
      return false;
    }
    scope[row] = s.stream().mapToInt(Integer::intValue).toArray();
    copies[row] = ys.toArray(new IntVar[0]);
    return true;
  }

  private void buildOccurrences() {
    int n = vars.length;
    int[] count = new int[n];
    for (int c = 0; c < m; c++) {
      for (int i : scope[c]) {
        count[i]++;
      }
      if (enforcer[c] >= 0 && !contains(scope[c], enforcer[c])) {
        count[enforcer[c]]++;
      }
    }
    occ = new int[n][];
    occCoef = new long[n][];
    for (int i = 0; i < n; i++) {
      occ[i] = new int[count[i]];
      occCoef[i] = new long[count[i]];
    }
    Arrays.fill(count, 0);
    for (int c = 0; c < m; c++) {
      for (int k = 0; k < scope[c].length; k++) {
        int i = scope[c][k];
        occ[i][count[i]] = c;
        occCoef[i][count[i]] = coef[c] == null ? 0 : coef[c][k];
        count[i]++;
      }
      int e = enforcer[c];
      if (e >= 0 && !contains(scope[c], e)) {
        occ[e][count[e]] = c;
        occCoef[e][count[e]] = 0;
        count[e]++;
      }
    }
  }

  private static boolean contains(int[] a, int x) {
    for (int y : a) {
      if (y == x) {
        return true;
      }
    }
    return false;
  }

  // ---------------------------------------------------------------- assignment

  /**
   * Gives every variable a value by one dive of propagation in the store: each variable not fixed
   * yet takes its hint, or the value nearest to zero, and a value whose propagation fails is kept
   * without being propagated.
   */
  private void initialAssignment() {
    Map<IntVar, Integer> hints = new IdentityHashMap<>();
    if (hintVars != null) {
      for (int k = 0; k < hintVars.length; k++) {
        hints.put(hintVars[k], hintValues[k]);
      }
    }
    int base = store.level;
    try {
      for (int i = 0; i < vars.length; i++) {
        IntVar x = vars[i];
        if (x.singleton()) {
          val[i] = x.value();
          continue;
        }
        Integer h = hints.get(x);
        int v = h != null && x.domain.contains(h) ? h : nearestToZero(x.dom());
        val[i] = v;
        if ((i & 63) == 0 && timeUp()) {
          // the rest keeps the value nearest to zero without propagation
          for (int j = i + 1; j < vars.length; j++) {
            val[j] = vars[j].singleton() ? vars[j].value() : nearestToZero(vars[j].dom());
          }
          break;
        }
        store.setLevel(store.level + 1);
        boolean ok;
        try {
          x.domain.in(store.level, x, v, v);
          ok = store.consistency();
        } catch (FailException e) {
          ok = false;
        }
        if (!ok) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        }
      }
    } finally {
      while (store.level > base) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
    }
    for (int i = 0; i < vars.length; i++) {
      if (!domains[i].contains(val[i])) {
        val[i] = nearestToZero(domains[i]);
      }
    }
    evaluateAll();
    bestAssignment = val.clone();
  }

  private static int nearestToZero(IntDomain d) {
    if (d.min() >= 0) {
      return d.min();
    }
    if (d.max() <= 0) {
      return d.max();
    }
    return d.contains(0) ? 0 : d.nextValue(0);
  }

  private void evaluateAll() {
    violatedCount = 0;
    Arrays.fill(violatedPos, -1);
    for (int c = 0; c < m; c++) {
      if (coef[c] != null) {
        long s = 0;
        for (int k = 0; k < scope[c].length; k++) {
          s = sat(s + coef[c][k] * val[scope[c][k]]);
        }
        lhs[c] = s;
      }
      setViolation(c, currentViolation(c));
    }
  }

  private static long sat(long x) {
    return Math.max(-Long.MAX_VALUE / 4, Math.min(Long.MAX_VALUE / 4, x));
  }

  private long currentViolation(int c) {
    if (measures[c] != null) {
      return measured(c, -1, 0);
    }
    if (copies[c] != null) {
      return check(c, -1, 0);
    }
    if (enforcer[c] >= 0 && val[enforcer[c]] != enforcedValue[c]) {
      return 0;
    }
    return amount(rel[c], lhs[c], rhs[c]);
  }

  private static long amount(int relation, long l, long r) {
    return switch (relation) {
      case LE -> Math.max(0, l - r);
      case GE -> Math.max(0, r - l);
      case EQ -> Math.abs(l - r);
      default -> l == r ? 1 : 0;
    };
  }

  private void setViolation(int c, long v) {
    viol[c] = v;
    int p = violatedPos[c];
    if (v > 0 && p < 0) {
      violatedPos[c] = violatedCount;
      violated[violatedCount++] = c;
    } else if (v == 0 && p >= 0) {
      int last = violated[--violatedCount];
      violated[p] = last;
      violatedPos[last] = p;
      violatedPos[c] = -1;
    }
  }

  /**
   * Checks a copied constraint by propagating it over the current values, with variable i at value
   * v instead (i = -1 for none).
   */
  private long check(int c, int i, int v) {
    if (scratch == null) {
      return 0;
    }
    evaluations++;
    int[] s = scope[c];
    IntVar[] ys = copies[c];
    int level = scratch.level + 1;
    scratch.setLevel(level);
    boolean ok = true;
    try {
      for (int k = 0; k < s.length && ok; k++) {
        int x = s[k] == i ? v : val[s[k]];
        IntVar y = ys[k];
        if (!y.domain.contains(x)) {
          ok = false;
        } else if (!y.singleton()) {
          y.domain.in(level, y, x, x);
        }
      }
      ok = ok && scratch.consistency();
    } catch (FailException e) {
      ok = false;
    } finally {
      scratch.removeLevel(level);
      scratch.setLevel(level - 1);
    }
    return ok ? 0 : 1;
  }

  private long measured(int c, int i, int v) {
    evaluations++;
    values.moved = i;
    values.movedValue = v;
    try {
      return measures[c].violation(values);
    } finally {
      values.moved = -1;
    }
  }

  // ---------------------------------------------------------------- moves

  private long violationAfter(int c, int i, int v, long a) {
    if (measures[c] != null) {
      return measured(c, i, v);
    }
    if (copies[c] != null) {
      return check(c, i, v);
    }
    int e = enforcer[c];
    if (e >= 0 && (e == i ? v : val[e]) != enforcedValue[c]) {
      return 0;
    }
    long l = a == 0 ? lhs[c] : sat(lhs[c] + a * ((long) v - val[i]));
    return amount(rel[c], l, rhs[c]);
  }

  /** The change of the weighted violation if variable i takes value v. */
  private double delta(int i, int v) {
    double d = 0;
    int[] cs = occ[i];
    long[] as = occCoef[i];
    for (int k = 0; k < cs.length; k++) {
      int c = cs[k];
      long after = violationAfter(c, i, v, as[k]);
      if (after != viol[c]) {
        d += weight[c] * (scaled(after) - scaled(viol[c]));
      }
    }
    return d;
  }

  // large amounts would drown the 0/1 violations of the copied constraints
  private static double scaled(long amount) {
    return amount <= 1 ? amount : 1 + Math.log(amount);
  }

  private void move(int i, int v) {
    int old = val[i];
    val[i] = v;
    moves++;
    int[] cs = occ[i];
    long[] as = occCoef[i];
    for (int k = 0; k < cs.length; k++) {
      int c = cs[k];
      if (coef[c] != null && as[k] != 0) {
        lhs[c] = sat(lhs[c] + as[k] * ((long) v - old));
      }
      setViolation(c, currentViolation(c));
    }
  }

  // ---------------------------------------------------------------- search

  private void search() {
    double bestScore = Double.MAX_VALUE;
    long lastImprovement = 0;
    int[] candidates = new int[64];
    while (!stopRequested) {
      if ((steps & 255) == 0 && timeUp()) {
        return;
      }
      if (violatedCount == 0) {
        if (feasible()) {
          if (firstSolution) {
            return;
          }
          bestScore = Double.MAX_VALUE;
          lastImprovement = steps;
          continue;
        }
        perturb();
        continue;
      }
      steps++;
      double score = totalViolation();
      if (score < bestScore) {
        bestScore = score;
        lastImprovement = steps;
        System.arraycopy(val, 0, bestAssignment, 0, val.length);
      } else if (steps - lastImprovement > stallSteps) {
        restart();
        bestScore = Double.MAX_VALUE;
        lastImprovement = steps;
        continue;
      }
      step(violated[random.nextInt(violatedCount)], candidates);
    }
  }

  // the number of violated constraints, the unweighted measure of progress
  private double totalViolation() {
    return violatedCount;
  }

  private void step(int c, int[] candidates) {
    int[] s = scope[c];
    int bestVar = -1;
    int bestVal = 0;
    double best = Double.MAX_VALUE;
    int ties = 0;
    int size = s.length + (enforcer[c] >= 0 ? 1 : 0);
    int scan = Math.min(size, SCAN_LIMIT);
    int offset = size > SCAN_LIMIT ? random.nextInt(size) : 0;
    for (int t = 0; t < scan; t++) {
      int p = (offset + t) % size;
      int i = p < s.length ? s[p] : enforcer[c];
      if (domains[i].singleton()) {
        continue;
      }
      boolean isTabu = tabu[i] > steps;
      int nc = candidates(i, c, p < s.length ? coef(c, p) : 0, candidates);
      for (int k = 0; k < nc; k++) {
        int v = candidates[k];
        double d = delta(i, v);
        if (isTabu && d >= 0) {
          continue;
        }
        if (d < best) {
          best = d;
          bestVar = i;
          bestVal = v;
          ties = 1;
        } else if (d == best && random.nextInt(++ties) == 0) {
          bestVar = i;
          bestVal = v;
        }
      }
    }
    if (bestVar >= 0 && best < 0) {
      move(bestVar, bestVal);
      tabu[bestVar] = steps + 3 + random.nextInt(8);
      return;
    }
    // a local minimum for this constraint: weigh it more, and sometimes move anyway
    weight[c] += 1;
    if (weight[c] > WEIGHT_LIMIT) {
      for (int k = 0; k < m; k++) {
        weight[k] = Math.max(1, weight[k] * 1e-6);
      }
    }
    if (bestVar >= 0 && random.nextInt(10) == 0) {
      move(bestVar, bestVal);
      tabu[bestVar] = steps + 3 + random.nextInt(8);
    }
  }

  private long coef(int c, int p) {
    return coef[c] == null ? 0 : coef[c][p];
  }

  /** The values tried for variable i in the step on constraint c, where its coefficient is a. */
  private int candidates(int i, int c, long a, int[] out) {
    IntDomain d = domains[i];
    int old = val[i];
    int n = 0;
    if (d.getSize() <= SMALL_DOMAIN) {
      for (int k = 0; k < d.getSize(); k++) {
        int v = d.getElementAt(k);
        if (v != old) {
          out[n++] = v;
        }
      }
      return n;
    }
    if (a != 0 && coef[c] != null && enforcer[c] != i) {
      // the values that satisfy the row, or come nearest to it
      long excess = lhs[c] - rhs[c];
      long target = (long) old - Math.floorDiv(excess, a);
      long target2 = (long) old - Math.ceilDiv(excess, a);
      n = addSnapped(d, target, old, out, n);
      n = addSnapped(d, target2, old, out, n);
    }
    n = addSnapped(d, old + 1L, old, out, n);
    n = addSnapped(d, old - 1L, old, out, n);
    int r = d.getElementAt(random.nextInt(d.getSize()));
    if (r != old) {
      out[n++] = r;
    }
    if (coef[c] == null) {
      n = addSnapped(d, d.min(), old, out, n);
      n = addSnapped(d, d.max(), old, out, n);
      r = d.getElementAt(random.nextInt(d.getSize()));
      if (r != old) {
        out[n++] = r;
      }
    }
    return n;
  }

  // the domain values next to the target on either side
  private static int addSnapped(IntDomain d, long target, int old, int[] out, int n) {
    int t = (int) Math.max(d.min(), Math.min(d.max(), target));
    int below = d.contains(t) ? t : d.previousValue(t);
    int above = d.contains(t) ? t : d.nextValue(t);
    if (below != old && d.contains(below) && !has(out, n, below)) {
      out[n++] = below;
    }
    if (above != below && above != old && d.contains(above) && !has(out, n, above)) {
      out[n++] = above;
    }
    return n;
  }

  private static boolean has(int[] a, int n, int v) {
    for (int k = 0; k < n; k++) {
      if (a[k] == v) {
        return true;
      }
    }
    return false;
  }

  // starts again from the best assignment of this round, with some variables changed at random
  private void restart() {
    restarts++;
    int[] from = solution != null && random.nextBoolean() ? solution : bestAssignment;
    System.arraycopy(from, 0, val, 0, val.length);
    for (int k = 0; k < m; k++) {
      weight[k] = 1 + (weight[k] - 1) * 0.5;
    }
    evaluateAll();
    perturb();
  }

  // changes a few variables of violated constraints, or any, to random values
  private void perturb() {
    int changes = 1 + random.nextInt(Math.min(8, vars.length));
    for (int k = 0; k < changes; k++) {
      int i;
      if (violatedCount > 0) {
        int[] s = scope[violated[random.nextInt(violatedCount)]];
        if (s.length == 0) {
          continue;
        }
        i = s[random.nextInt(s.length)];
      } else {
        i = random.nextInt(vars.length);
      }
      IntDomain d = domains[i];
      if (!d.singleton()) {
        move(i, d.getElementAt(random.nextInt(d.getSize())));
      }
    }
  }

  /**
   * Checks the assignment, which violates no constraint of the local search, in the store and
   * reports it. For optimisation, the bound on the cost then excludes it.
   *
   * @return false when the store rejected it.
   */
  private boolean feasible() {
    int base = store.level;
    boolean ok;
    try {
      ok = fixInStore();
      if (ok) {
        solutions++;
        solution = val.clone();
        storeSolution = new int[store.size()];
        for (int k = 0; k < store.size(); k++) {
          if (store.vars[k] instanceof IntVar x) {
            storeSolution[k] = x.value();
          }
        }
        if (cost != null) {
          solutionCost = cost.value();
        }
        if (solutionHandler != null) {
          solutionHandler.accept(this);
        }
      }
    } finally {
      while (store.level > base) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
    }
    if (!ok) {
      rejected++;
      return false;
    }
    if (cost != null) {
      tightenBound();
    }
    return true;
  }

  /**
   * Fixes the variables of the given order to their values and propagates; then the other
   * variables, each to its value if propagation accepts it; then gives the variables still not
   * fixed their smallest value. The levels are left for the caller to remove.
   *
   * @return false when the store rejects the assignment.
   */
  private boolean fixInStore() {
    store.setLevel(store.level + 1);
    try {
      for (int i = 0; i < orderCount; i++) {
        IntVar x = vars[i];
        if (!x.domain.contains(val[i])) {
          return false;
        }
        if (!x.singleton()) {
          x.domain.in(store.level, x, val[i], val[i]);
        }
      }
      if (!store.consistency()) {
        return false;
      }
    } catch (FailException e) {
      return false;
    }
    for (int i = orderCount; i < vars.length; i++) {
      IntVar x = vars[i];
      if (x.singleton() || !x.domain.contains(val[i])) {
        continue;
      }
      store.setLevel(store.level + 1);
      boolean ok;
      try {
        x.domain.in(store.level, x, val[i], val[i]);
        ok = store.consistency();
      } catch (FailException e) {
        ok = false;
      }
      if (!ok) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
    }
    return completeOthers();
  }

  // gives the variables still not fixed their smallest value, with propagation
  private boolean completeOthers() {
    try {
      for (int k = 0; k < store.size(); k++) {
        if (store.vars[k] instanceof IntVar x && !x.singleton()) {
          store.setLevel(store.level + 1);
          x.domain.in(store.level, x, x.min(), x.min());
          if (!store.consistency()) {
            return false;
          }
        }
      }
    } catch (FailException e) {
      return false;
    }
    return true;
  }

  private void tightenBound() {
    long bound = solutionCost;
    if (sharedBound != null) {
      bound = Math.min(bound, sharedBound.getAsInt());
    }
    rhs[boundRow] = bound - 1;
    setViolation(boundRow, currentViolation(boundRow));
  }

  private boolean timeUp() {
    if (stopRequested) {
      return true;
    }
    if (System.currentTimeMillis() >= deadline) {
      return true;
    }
    if (sharedBound != null && boundRow >= 0) {
      int b = sharedBound.getAsInt();
      if (b != Integer.MAX_VALUE && b - 1L < rhs[boundRow]) {
        rhs[boundRow] = b - 1L;
        setViolation(boundRow, currentViolation(boundRow));
      }
    }
    return false;
  }

  @Override
  public String toString() {
    return "LocalSearch(vars="
        + (vars == null ? 0 : vars.length)
        + ", linear="
        + linearCount
        + ", checked="
        + checkedCount
        + ", unsupported="
        + unsupportedCount
        + ", "
        + classes
        + ")";
  }

  /** Builds a {@link LocalSearch}. */
  public static final class Builder {

    private final Store store;
    private IntVar cost;
    private long timeLimitMillis;
    private Consumer<LocalSearch> solutionHandler;
    private IntSupplier sharedBound;
    private boolean firstSolution;
    private long seed = 1;
    private IntVar[] order;
    private IntVar[] hintVars;
    private int[] hintValues;
    private long stallSteps = 20_000;

    private Builder(Store store) {
      this.store = store;
    }

    /**
     * Minimises a cost variable. Each solution found adds the bound that the next one is better.
     *
     * @param cost the cost variable.
     * @return this builder.
     */
    public Builder minimize(IntVar cost) {
      this.cost = cost;
      return this;
    }

    /**
     * Sets the variables given values first in the initial assignment, in this order; the others
     * follow in the order of the constraints.
     *
     * @param vars the variables.
     * @return this builder.
     */
    public Builder order(IntVar... vars) {
      this.order = vars.clone();
      return this;
    }

    /**
     * Gives values that the initial assignment takes where they are in the domains.
     *
     * @param vars the variables.
     * @param values their values.
     * @return this builder.
     */
    public Builder hint(IntVar[] vars, int[] values) {
      if (vars.length != values.length) {
        throw new IllegalArgumentException("a hint needs one value per variable");
      }
      this.hintVars = vars.clone();
      this.hintValues = values.clone();
      return this;
    }

    /**
     * Sets the time limit.
     *
     * @param limit the limit.
     * @return this builder.
     */
    public Builder timeLimit(Duration limit) {
      this.timeLimitMillis = limit.toMillis();
      return this;
    }

    /**
     * Sets the seed of the random choices.
     *
     * @param seed the seed.
     * @return this builder.
     */
    public Builder seed(long seed) {
      this.seed = seed;
      return this;
    }

    /**
     * Makes optimisation stop at its first solution too.
     *
     * @param first true to stop at the first solution.
     * @return this builder.
     */
    public Builder stopAtFirstSolution(boolean first) {
      this.firstSolution = first;
      return this;
    }

    /**
     * Sets after how many steps without fewer violated constraints the search starts again from the
     * best assignment.
     *
     * @param steps the steps.
     * @return this builder.
     */
    public Builder stallSteps(long steps) {
      this.stallSteps = steps;
      return this;
    }

    /**
     * Sets what is done with each solution, called with the store in the state of the solution (all
     * variables fixed) at a level above the root that is removed afterwards.
     *
     * @param handler the handler.
     * @return this builder.
     */
    public Builder onSolution(Consumer<LocalSearch> handler) {
      this.solutionHandler = handler;
      return this;
    }

    /**
     * Sets a bound on the cost shared with other searches: a solution must be better than it.
     *
     * @param bound the bound, {@link Integer#MAX_VALUE} while there is none.
     * @return this builder.
     */
    public Builder sharedBound(IntSupplier bound) {
      this.sharedBound = bound;
      return this;
    }

    /**
     * Builds the local search.
     *
     * @return the local search.
     */
    public LocalSearch build() {
      return new LocalSearch(this);
    }
  }
}
