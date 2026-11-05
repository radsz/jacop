/*
 * ScenarioChance.java
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

package org.jacop.prob.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.Monotone;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Linearizations;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.prob.scenario.ScenarioSet;

/**
 * A chance constraint over scenarios: the scenarios s whose linear constraint {@code sum(i, a[s][i]
 * * x[i]) <= b[s]} holds must have a total weight of at least {@code alpha}. With weights that are
 * probability numerators over a denominator D it states Pr(a x &lt;= b) &gt;= alpha / D for a
 * random row (a, b) of a finite distribution, the sample average approximation of a chance
 * constraint (Luedtke and Ahmed, SIAM J. Optim. 19, 2008).
 *
 * <p>It replaces the usual expansion into one reified linear constraint per scenario and a weighted
 * sum of their Booleans. From the bounds of x it finds the dead scenarios (the minimal activity is
 * above b[s]) and the sure ones (the maximal activity is at most b[s]). It fails when the live
 * weight is below alpha. Otherwise the live weight above alpha is a slack: a value of x[i] is
 * removed when the scenarios it would kill weigh more than the slack, which bounds each variable by
 * a sweep over the scenarios sorted by the value at which they die. All arithmetic is exact on
 * longs.
 *
 * <p>With indicator variables, ok[s] = 1 exactly when scenario s holds, and the chance is the
 * weighted sum of the indicators. The constraint then also fixes indicators (dead to 0, sure to 1,
 * and to 1 a scenario whose weight is above the slack), propagates the row of a scenario whose
 * indicator is 1 and the negated row of one whose indicator is 0, and gives the linear relaxation
 * the big-M rows of the scenarios and the weighted sum. The indicators carry no search of their
 * own, but lazy clause generation learns over them and the relaxation bounds the objective.
 *
 * <p>It explains its pruning for lazy clause generation: the negation of a pruned atom leads, with
 * the bounds before it, to a forced scenario that is dead, an excluded scenario that is sure, or
 * dead and excluded scenarios whose weight leaves less than alpha. The bounds of a dead or sure
 * scenario are taken largest move from the root first, the last one weakened as far as it can be.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ScenarioChance extends Constraint
    implements SatisfiedPresent,
        Copyable<ScenarioChance>,
        Monotone,
        Explainable,
        Linearizations.Relaxable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // the activities must stay far from overflow: |a x| + |b| below 2^62 over the initial bounds
  private static final double ACTIVITY_LIMIT = 0x1p62;

  /** The variables, without duplicates and without those of coefficient 0 in every scenario. */
  final IntVar[] x;

  /** The indicator of each scenario, or null. */
  final IntVar[] ok;

  // scenario s: the variable indices and coefficients of its row, sparse
  final int[][] rowIndex;
  final long[][] rowCoef;

  // variable i: the scenarios it occurs in and its coefficient there
  final int[][] colScenario;
  final long[][] colCoef;

  final long[] b;
  final long[] w;
  final long alpha;

  // the sum of all weights
  final long total;

  // scratch: the bounds at the start of a round, per scenario activities, sort keys of the sweep
  private final long[] lo0;
  private final long[] hi0;
  private final long[] minAct;
  private final long[] maxAct;
  private long[] keys;

  /**
   * It constructs the constraint sum over {s : a[s] x &lt;= b[s]} of w[s] &gt;= alpha.
   *
   * @param x the variables
   * @param a the coefficients, one row of x.length coefficients for each scenario
   * @param b the right-hand side of each scenario
   * @param w the weight of each scenario, at least 0 (a probability numerator)
   * @param alpha the weight that the satisfied scenarios must reach
   */
  public ScenarioChance(IntVar[] x, int[][] a, int[] b, long[] w, long alpha) {
    this(x, toLong(a), toLong(b), w, alpha, null);
  }

  /**
   * It constructs the constraint with indicators: ok[s] = 1 exactly when a[s] x &lt;= b[s], and
   * sum(w[s] * ok[s]) &gt;= alpha.
   *
   * @param x the variables
   * @param a the coefficients, one row of x.length coefficients for each scenario
   * @param b the right-hand side of each scenario
   * @param w the weight of each scenario, at least 0 (a probability numerator)
   * @param alpha the weight that the satisfied scenarios must reach
   * @param ok the 0/1 indicator of each scenario
   */
  public ScenarioChance(IntVar[] x, int[][] a, int[] b, long[] w, long alpha, IntVar[] ok) {
    this(x, toLong(a), toLong(b), w, alpha, ok);
  }

  /**
   * It constructs the constraint over the scenarios of a scenario set whose parameters are, for
   * each scenario, the coefficients of x followed by the right-hand side.
   *
   * @param x the variables
   * @param scenarios the scenarios, of dimension x.length + 1, with their probabilities
   * @param alpha the probability numerator, over the set's denominator, that must be reached
   * @return the constraint
   */
  public static ScenarioChance linear(IntVar[] x, ScenarioSet scenarios, long alpha) {
    if (scenarios.size() > 0 && scenarios.dimension() != x.length + 1) {
      throw new IllegalArgumentException(
          "Scenarios of dimension " + scenarios.dimension() + " for " + x.length + " variables");
    }
    long[][] a = new long[scenarios.size()][x.length];
    long[] b = new long[scenarios.size()];
    for (int s = 0; s < scenarios.size(); s++) {
      for (int i = 0; i < x.length; i++) {
        a[s][i] = scenarios.value(s, i);
      }
      b[s] = scenarios.value(s, x.length);
    }
    return new ScenarioChance(x, a, b, scenarios.weights(), alpha, null);
  }

  /**
   * It constructs the constraint sum over {s : a[s] x &lt;= b[s]} of w[s] &gt;= alpha with long
   * coefficients, and with indicators unless ok is null.
   *
   * @param x the variables
   * @param a the coefficients, one row of x.length coefficients for each scenario
   * @param b the right-hand side of each scenario
   * @param w the weight of each scenario, at least 0
   * @param alpha the weight that the satisfied scenarios must reach
   * @param ok the 0/1 indicator of each scenario, or null for none
   */
  public ScenarioChance(IntVar[] x, long[][] a, long[] b, long[] w, long alpha, IntVar[] ok) {
    checkInputForNullness(
        new String[] {"x", "a", "b", "w"}, x, a, new Object[] {b}, new Object[] {w});
    if (a.length != b.length || a.length != w.length || ok != null && ok.length != a.length) {
      throw new IllegalArgumentException("ScenarioChance has a, b, w and ok of different lengths");
    }
    for (int s = 0; s < a.length; s++) {
      if (a[s] == null || a[s].length != x.length) {
        throw new IllegalArgumentException(
            "ScenarioChance row " + s + " is not of length " + x.length);
      }
      if (w[s] < 0) {
        throw new IllegalArgumentException("ScenarioChance has a negative weight " + w[s]);
      }
    }
    if (ok != null) {
      checkInputForNullness("ok", ok);
      for (IntVar v : ok) {
        if (v.min() < 0 || v.max() > 1 || Arrays.asList(x).contains(v)) {
          throw new IllegalArgumentException(
              "ScenarioChance indicators must be 0/1 variables outside x: " + v);
        }
      }
      if (Arrays.stream(ok).distinct().count() != ok.length) {
        throw new IllegalArgumentException("ScenarioChance indicators must be distinct");
      }
    }

    numberId = idNumber.incrementAndGet();
    queueIndex = 2;

    // the distinct variables, with the coefficients of duplicates summed; without indicators the
    // scenarios of weight 0 are dropped
    Map<IntVar, Integer> position = new LinkedHashMap<>();
    for (IntVar v : x) {
      position.putIfAbsent(v, position.size());
    }
    List<Integer> kept = new ArrayList<>();
    for (int s = 0; s < a.length; s++) {
      if (w[s] > 0 || ok != null) {
        kept.add(s);
      }
    }
    int scenarios = kept.size();
    long[][] dense = new long[scenarios][position.size()];
    for (int k = 0; k < scenarios; k++) {
      int s = kept.get(k);
      for (int i = 0; i < x.length; i++) {
        int p = position.get(x[i]);
        dense[k][p] = Math.addExact(dense[k][p], a[s][i]);
      }
    }
    IntVar[] distinct = position.keySet().toArray(new IntVar[0]);
    boolean[] used = new boolean[distinct.length];
    for (long[] row : dense) {
      for (int p = 0; p < row.length; p++) {
        used[p] |= row[p] != 0;
      }
    }
    int[] newIndex = new int[distinct.length];
    int n = 0;
    for (int p = 0; p < distinct.length; p++) {
      newIndex[p] = used[p] ? n++ : -1;
    }
    this.x = new IntVar[n];
    for (int p = 0; p < distinct.length; p++) {
      if (used[p]) {
        this.x[newIndex[p]] = distinct[p];
      }
    }
    this.ok = ok == null ? null : ok.clone();

    this.b = new long[scenarios];
    this.w = new long[scenarios];
    this.rowIndex = new int[scenarios][];
    this.rowCoef = new long[scenarios][];
    int[] colSize = new int[n];
    long sum = 0;
    for (int k = 0; k < scenarios; k++) {
      int s = kept.get(k);
      this.b[k] = b[s];
      this.w[k] = w[s];
      sum = Math.addExact(sum, w[s]);
      int nz = 0;
      for (long c : dense[k]) {
        if (c != 0) {
          nz++;
        }
      }
      rowIndex[k] = new int[nz];
      rowCoef[k] = new long[nz];
      nz = 0;
      double activity = Math.abs((double) b[s]);
      for (int p = 0; p < dense[k].length; p++) {
        long c = dense[k][p];
        if (c != 0) {
          int i = newIndex[p];
          rowIndex[k][nz] = i;
          rowCoef[k][nz++] = c;
          colSize[i]++;
          IntVar v = this.x[i];
          activity +=
              Math.abs((double) c)
                  * Math.max(Math.abs((double) v.min()), Math.abs((double) v.max()));
        }
      }
      if (activity >= ACTIVITY_LIMIT) {
        throw new IllegalArgumentException(
            "ScenarioChance activities may overflow a long in scenario " + s);
      }
    }
    this.total = sum;
    this.alpha = alpha;

    colScenario = new int[n][];
    colCoef = new long[n][];
    for (int i = 0; i < n; i++) {
      colScenario[i] = new int[colSize[i]];
      colCoef[i] = new long[colSize[i]];
      colSize[i] = 0;
    }
    for (int k = 0; k < scenarios; k++) {
      for (int t = 0; t < rowIndex[k].length; t++) {
        int i = rowIndex[k][t];
        colScenario[i][colSize[i]] = k;
        colCoef[i][colSize[i]++] = rowCoef[k][t];
      }
    }

    lo0 = new long[n];
    hi0 = new long[n];
    minAct = new long[scenarios];
    maxAct = new long[scenarios];
    keys = new long[16];

    setScope(
        this.ok == null
            ? Arrays.stream(this.x)
            : Stream.concat(Arrays.stream(this.x), Arrays.stream(this.ok)));
  }

  private static long[] toLong(int[] b) {
    if (b == null) {
      throw new IllegalArgumentException("ScenarioChance has b null");
    }
    return Arrays.stream(b).asLongStream().toArray();
  }

  private static long[][] toLong(int[][] a) {
    if (a == null) {
      throw new IllegalArgumentException("ScenarioChance has a null");
    }
    long[][] result = new long[a.length][];
    for (int s = 0; s < a.length; s++) {
      if (a[s] == null) {
        throw new IllegalArgumentException("ScenarioChance row " + s + " is null");
      }
      result[s] = Arrays.stream(a[s]).asLongStream().toArray();
    }
    return result;
  }

  /**
   * Returns the number of scenarios.
   *
   * @return the number of scenarios
   */
  public int scenarios() {
    return w.length;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  // whether minAct and maxAct hold the activities over the bounds in lo0 and hi0
  private boolean activitiesKnown;

  // the bounds of x and the minimal and maximal activity of every scenario, updated from the
  // bounds of the previous call: only the columns of variables whose bounds differ are visited, at
  // any level, since the activities are sums over the bounds remembered with them
  private void activities() {
    if (!activitiesKnown) {
      for (int i = 0; i < x.length; i++) {
        lo0[i] = x[i].min();
        hi0[i] = x[i].max();
      }
      for (int s = 0; s < w.length; s++) {
        long lo = 0;
        long hi = 0;
        int[] idx = rowIndex[s];
        long[] coef = rowCoef[s];
        for (int t = 0; t < idx.length; t++) {
          int i = idx[t];
          long c = coef[t];
          if (c > 0) {
            lo += c * lo0[i];
            hi += c * hi0[i];
          } else {
            lo += c * hi0[i];
            hi += c * lo0[i];
          }
        }
        minAct[s] = lo;
        maxAct[s] = hi;
      }
      activitiesKnown = true;
      return;
    }
    for (int i = 0; i < x.length; i++) {
      long lo = x[i].min();
      long hi = x[i].max();
      if (lo == lo0[i] && hi == hi0[i]) {
        continue;
      }
      long dLo = lo - lo0[i];
      long dHi = hi - hi0[i];
      int[] scen = colScenario[i];
      long[] coef = colCoef[i];
      for (int t = 0; t < scen.length; t++) {
        int s = scen[t];
        long c = coef[t];
        if (c > 0) {
          minAct[s] += c * dLo;
          maxAct[s] += c * dHi;
        } else {
          minAct[s] += c * dHi;
          maxAct[s] += c * dLo;
        }
      }
      lo0[i] = lo;
      hi0[i] = hi;
    }
  }

  @Override
  public void consistency(Store store) {
    boolean changed = true;
    while (changed) {
      changed = false;
      activities();
      long live = 0;
      long sure = 0;
      for (int s = 0; s < w.length; s++) {
        boolean dead = minAct[s] > b[s];
        boolean holds = maxAct[s] <= b[s];
        if (ok != null) {
          IntVar o = ok[s];
          if (dead && o.max() == 1) {
            o.domain.inMax(store.level, o, 0);
            changed = true;
          } else if (holds && o.min() == 0) {
            o.domain.inMin(store.level, o, 1);
            changed = true;
          }
          if (o.max() == 0) {
            continue;
          }
        }
        if (!dead) {
          live += w[s];
          if (holds) {
            sure += w[s];
          }
        }
      }
      if (live < alpha) {
        throw Store.failException;
      }
      if (ok == null && sure >= alpha) {
        removeConstraint();
        return;
      }
      long slack = live - alpha;
      if (ok != null) {
        for (int s = 0; s < w.length; s++) {
          IntVar o = ok[s];
          if (o.min() == 0 && o.max() == 1 && minAct[s] <= b[s] && w[s] > slack) {
            o.domain.inMin(store.level, o, 1);
            changed = true;
          }
          if (o.min() == 1) {
            changed |= pruneRow(store, s, false);
          } else if (o.max() == 0) {
            changed |= pruneRow(store, s, true);
          }
        }
      }
      for (int i = 0; i < x.length; i++) {
        // a fixed variable kills no live scenario, else the scenario would be dead
        if (!x[i].singleton()) {
          changed |= pruneUpper(store, i, slack);
          changed |= pruneLower(store, i, slack);
        }
      }
    }
  }

  // the bounds of the row of scenario s (a x <= b), or of its negation (a x >= b + 1)
  private boolean pruneRow(Store store, int s, boolean negated) {
    long sign = negated ? -1 : 1;
    long rhs = negated ? -b[s] - 1 : b[s];
    long least = negated ? -maxAct[s] : minAct[s];
    if (least > rhs) {
      throw Store.failException;
    }
    boolean changed = false;
    int[] idx = rowIndex[s];
    long[] coef = rowCoef[s];
    for (int t = 0; t < idx.length; t++) {
      int i = idx[t];
      long c = sign * coef[t];
      IntVar v = x[i];
      if (c > 0) {
        long last = lo0[i] + (rhs - least) / c;
        if (last < v.max()) {
          v.domain.inMax(store.level, v, (int) last);
          changed = true;
        }
      } else {
        long first = hi0[i] - (rhs - least) / -c;
        if (first > v.min()) {
          v.domain.inMin(store.level, v, (int) first);
          changed = true;
        }
      }
    }
    return changed;
  }

  // whether scenario s is live and may die, so the sweep weighs it
  private boolean sweeps(int s) {
    return minAct[s] <= b[s] && (ok == null || ok[s].min() == 0 && ok[s].max() == 1);
  }

  // the largest value of x[i] at which the live scenarios it kills weigh at most slack
  private boolean pruneUpper(Store store, int i, long slack) {
    IntVar v = x[i];
    long lo = lo0[i];
    int hi = v.max();
    int count = 0;
    long killable = 0;
    int[] scen = colScenario[i];
    long[] coef = colCoef[i];
    for (int t = 0; t < scen.length; t++) {
      int s = scen[t];
      long c = coef[t];
      if (c > 0 && sweeps(s)) {
        // the largest value of x[i] that keeps s alive
        long last = lo + (b[s] - minAct[s]) / c;
        if (last < hi) {
          count = addKey(count, last - lo, t);
          killable += w[s];
        }
      }
    }
    if (killable <= slack) {
      return false;
    }
    Arrays.sort(keys, 0, count);
    long killed = 0;
    for (int k = 0; k < count; k++) {
      killed += w[scen[(int) keys[k]]];
      if (killed > slack) {
        // any value above this scenario's last one kills it and those before it
        v.domain.inMax(store.level, v, (int) (lo + (keys[k] >>> 32)));
        return true;
      }
    }
    return false;
  }

  // the smallest value of x[i] at which the live scenarios it kills weigh at most slack
  private boolean pruneLower(Store store, int i, long slack) {
    IntVar v = x[i];
    int lo = v.min();
    long hi = hi0[i];
    int count = 0;
    long killable = 0;
    int[] scen = colScenario[i];
    long[] coef = colCoef[i];
    for (int t = 0; t < scen.length; t++) {
      int s = scen[t];
      long c = coef[t];
      if (c < 0 && sweeps(s)) {
        // the smallest value of x[i] that keeps s alive
        long first = hi - (b[s] - minAct[s]) / -c;
        if (first > lo) {
          count = addKey(count, hi - first, t);
          killable += w[s];
        }
      }
    }
    if (killable <= slack) {
      return false;
    }
    Arrays.sort(keys, 0, count);
    long killed = 0;
    for (int k = 0; k < count; k++) {
      killed += w[scen[(int) keys[k]]];
      if (killed > slack) {
        v.domain.inMin(store.level, v, (int) (hi - (keys[k] >>> 32)));
        return true;
      }
    }
    return false;
  }

  // a sort key: the distance in the high 32 bits (below 2^32 inside the bounds), the position low
  private int addKey(int count, long distance, int t) {
    if (count == keys.length) {
      keys = Arrays.copyOf(keys, 2 * count);
    }
    keys[count] = distance << 32 | t;
    return count + 1;
  }

  // the activity of scenario s at the upper (or lower) end of the current bounds
  private long activity(int s, boolean upper) {
    long act = 0;
    int[] idx = rowIndex[s];
    long[] coef = rowCoef[s];
    for (int t = 0; t < idx.length; t++) {
      IntVar v = x[idx[t]];
      act += coef[t] * ((coef[t] > 0) == upper ? v.max() : v.min());
    }
    return act;
  }

  @Override
  public boolean satisfied() {
    long weight = 0;
    for (int s = 0; s < w.length; s++) {
      boolean holds = activity(s, true) <= b[s];
      if (ok == null) {
        weight += holds ? w[s] : 0;
        continue;
      }
      if (!ok[s].singleton()) {
        return false;
      }
      if (ok[s].value() == 1) {
        if (!holds) {
          return false;
        }
        weight += w[s];
      } else if (activity(s, false) <= b[s]) {
        return false;
      }
    }
    return weight >= alpha;
  }

  @Override
  public int freeDirections(Var v) {
    if (ok != null) {
      // the indicators tie every variable to its scenarios both ways
      return 0;
    }
    boolean positive = false;
    boolean negative = false;
    for (int i = 0; i < x.length; i++) {
      if (x[i] == v) {
        for (long c : colCoef[i]) {
          positive |= c > 0;
          negative |= c < 0;
        }
      }
    }
    // a smaller value of a variable with coefficients of at least 0 keeps every scenario satisfied
    return (positive ? 0 : DECREASE) | (negative ? 0 : INCREASE);
  }

  // ---- linear relaxation

  @Override
  public List<LinearForm> relaxation() {
    List<LinearForm> rows = new ArrayList<>();
    if (ok == null) {
      return rows;
    }
    activities();
    for (int s = 0; s < w.length; s++) {
      int[] idx = rowIndex[s];
      int k = idx.length;
      IntVar[] vars = new IntVar[k + 1];
      long[] coef = Arrays.copyOf(rowCoef[s], k + 1);
      for (int t = 0; t < k; t++) {
        vars[t] = x[idx[t]];
      }
      vars[k] = ok[s];
      // ok = 1 gives a x <= b, ok = 0 leaves a x <= maxAct
      long bigUp = maxAct[s] - b[s];
      if (bigUp > 0) {
        coef[k] = bigUp;
        rows.add(new LinearForm(vars, coef.clone(), Math.addExact(b[s], bigUp), LinearForm.LE));
      }
      // ok = 0 gives a x >= b + 1, ok = 1 leaves a x >= minAct
      long bigDown = b[s] + 1 - minAct[s];
      if (bigDown > 0) {
        coef[k] = bigDown;
        rows.add(new LinearForm(vars, coef.clone(), b[s] + 1, LinearForm.GE));
      }
    }
    rows.add(new LinearForm(ok.clone(), w.clone(), alpha, LinearForm.GE));
    return rows;
  }

  // ---- lazy clause generation

  // the bounds just before a trail position, with one bound replaced by a hypothesis
  private final class State {
    final AtomicTrail trail;
    final int position;
    final IntVar hypothesisVar;
    final boolean hypothesisLower;
    final long hypothesis;

    State(AtomicTrail trail, int position, IntVar var, boolean lower, long hypothesis) {
      this.trail = trail;
      this.position = position;
      this.hypothesisVar = var;
      this.hypothesisLower = lower;
      this.hypothesis = hypothesis;
    }

    long min(IntVar v) {
      return v == hypothesisVar && hypothesisLower ? hypothesis : trail.minBefore(v, position);
    }

    long max(IntVar v) {
      return v == hypothesisVar && !hypothesisLower ? hypothesis : trail.maxBefore(v, position);
    }

    // the activity of scenario s at the lower (or upper) end of the bounds
    long activity(int s, boolean upper) {
      long act = 0;
      int[] idx = rowIndex[s];
      long[] coef = rowCoef[s];
      for (int t = 0; t < idx.length; t++) {
        IntVar v = x[idx[t]];
        act += coef[t] * ((coef[t] > 0) == upper ? max(v) : min(v));
      }
      return act;
    }

    // adds the atom of a bound unless it is the hypothesis
    void addBound(IntVar v, boolean lower, EntryList out) {
      if (v != hypothesisVar || hypothesisLower != lower) {
        if (lower) {
          trail.addLowerBound(v, position, out);
        } else {
          trail.addUpperBound(v, position, out);
        }
      }
    }

    /**
     * Adds the bounds that make scenario s dead (a x &gt; b, sure false) or sure (a x &lt;= b, sure
     * true): those that move its activity most from the root bounds first, until the activity is
     * past b, the last one weakened as far as the remaining gap allows.
     */
    void addRowReason(int s, boolean sure, EntryList out) {
      int[] idx = rowIndex[s];
      long sign = sure ? -1 : 1;
      // sum(c * y) > rhs over the lower bounds of y for c > 0 and the upper ones for c < 0
      long rhs = sure ? -b[s] - 1 : b[s];
      long[] coef = rowCoef[s];
      long activity = 0;
      long[] move = new long[idx.length];
      long[] now = new long[idx.length];
      long[] root = new long[idx.length];
      List<Integer> order = new ArrayList<>();
      for (int t = 0; t < idx.length; t++) {
        IntVar v = x[idx[t]];
        long c = sign * coef[t];
        boolean lower = c > 0;
        now[t] = lower ? min(v) : max(v);
        if (v == hypothesisVar && hypothesisLower == lower) {
          activity += c * now[t];
          continue;
        }
        IntDomain rootDomain = trail.rootDomain(v);
        root[t] = lower ? rootDomain.min() : rootDomain.max();
        activity += c * root[t];
        move[t] = c * (now[t] - root[t]);
        if (move[t] > 0) {
          order.add(t);
        }
      }
      long need = rhs - activity + 1;
      order.sort((p, q) -> Long.compare(move[q], move[p]));
      for (int k = 0; k < order.size() && need > 0; k++) {
        int t = order.get(k);
        long c = sign * coef[t];
        long limit = now[t];
        if (move[t] >= need) {
          // the weakest bound that still closes the gap
          long steps = (need + Math.abs(c) - 1) / Math.abs(c);
          limit = c > 0 ? root[t] + steps : root[t] - steps;
        }
        trail.addBoundReaching(x[idx[t]], position, c > 0, limit, out);
        need -= move[t];
      }
    }

    /** Adds the reason why the bounds cannot all hold under the constraint, or returns false. */
    boolean contradiction(EntryList out) {
      int scenarios = w.length;
      long[] lowAct = new long[scenarios];
      for (int s = 0; s < scenarios; s++) {
        lowAct[s] = activity(s, false);
      }
      if (ok != null) {
        // a scenario that must hold is dead, or one that must not hold is sure
        for (int s = 0; s < scenarios; s++) {
          if (min(ok[s]) == 1 && lowAct[s] > b[s]) {
            addBound(ok[s], true, out);
            addRowReason(s, false, out);
            return true;
          }
        }
        for (int s = 0; s < scenarios; s++) {
          if (max(ok[s]) == 0 && activity(s, true) <= b[s]) {
            addBound(ok[s], false, out);
            addRowReason(s, true, out);
            return true;
          }
        }
      }
      // the excluded and the dead scenarios weigh more than total - alpha; the heaviest first,
      // an excluded one by its indicator
      List<Integer> lost = new ArrayList<>();
      for (int s = 0; s < scenarios; s++) {
        if (lowAct[s] > b[s] || ok != null && max(ok[s]) == 0) {
          lost.add(s);
        }
      }
      lost.sort((p, q) -> Long.compare(w[q], w[p]));
      long needed = total - alpha;
      long weight = 0;
      int used = 0;
      while (used < lost.size() && weight <= needed) {
        weight += w[lost.get(used++)];
      }
      if (weight <= needed) {
        return false;
      }
      for (int k = 0; k < used; k++) {
        int s = lost.get(k);
        if (ok != null && max(ok[s]) == 0) {
          addBound(ok[s], false, out);
        } else {
          addRowReason(s, false, out);
        }
      }
      return true;
    }
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return false;
    }
    IntVar y = trail.variable(entry);
    boolean isX = Arrays.asList(x).contains(y);
    if (!isX && (ok == null || !Arrays.asList(ok).contains(y))) {
      return false;
    }
    // the bound the propagation computed, before the domain moved over holes next to it
    int bound = isX ? trail.skippedBound(entry) : trail.value(entry);
    // the negation of the atom: y >= bound + 1 for y <= bound, y <= bound - 1 for y >= bound
    boolean lower = kind == AtomicTrail.LE;
    long hypothesis = lower ? (long) bound + 1 : (long) bound - 1;
    int mark = out.size();
    if (!new State(trail, entry, y, lower, hypothesis).contradiction(out)) {
      out.truncate(mark);
      return false;
    }
    if (bound != trail.value(entry)) {
      trail.addSkippedHoles(entry, bound, out);
    }
    out.sortUnique(mark);
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int mark = out.size();
    if (!new State(trail, trail.size(), null, false, 0).contradiction(out)) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  @Override
  public ScenarioChance copy(VarMap map) {
    long[][] a = new long[w.length][x.length];
    for (int s = 0; s < w.length; s++) {
      for (int t = 0; t < rowIndex[s].length; t++) {
        a[s][rowIndex[s][t]] = rowCoef[s][t];
      }
    }
    return new ScenarioChance(
        map.get(x), a, b.clone(), w.clone(), alpha, ok == null ? null : map.get(ok));
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder();
    result.append(id()).append(" : ScenarioChance([");
    for (int i = 0; i < x.length; i++) {
      result.append(x[i]);
      if (i < x.length - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(w.length).append(" scenarios, weight >= ").append(alpha);
    result.append(" of ").append(total);
    if (ok != null) {
      result.append(", ok: ").append(Arrays.toString(ok));
    }
    return result.append(')').toString();
  }
}
