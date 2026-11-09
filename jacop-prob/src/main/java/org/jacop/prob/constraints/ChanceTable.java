/*
 * ChanceTable.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * A chance constraint over scenario tables: {@code p = sum(s, w[s] * [x satisfies scenario s])}.
 * Scenario s holds when x is a tuple of every table (factor) it lists, and its weight is a
 * probability numerator, so p is the probability that the scenario drawn holds. It is the one-stage
 * stochastic CSP of Walsh (Stochastic constraint programming, ECAI 2002) with the decisions taken
 * before the random variables are observed: the constraints that mention random variables become,
 * for each value of them, tables over the decisions only. A table shared by many scenarios, such as
 * the projection of one constraint for one value of its random variable, is stored and checked
 * once.
 *
 * <p>Filtering is weighted generalised arc consistency on each table, the filtering of a compact
 * table (Demeulenaere et al., CP 2016) with the scenarios counted by weight: a value (x[i], v) is
 * supported by a scenario when each of its tables has a tuple with x[i] = v whose other values are
 * in the domains. A value whose supporting scenarios weigh less than the lower bound of p is
 * removed. The upper bound of p is the weight of the scenarios whose tables all still have a tuple,
 * its lower bound the weight of those whose tables contain every tuple of the domains, so p is
 * fixed when x is. With p maximised this is the bound of branch and bound for the most probable
 * decision; with p &gt;= alpha it is the chance constraint Pr(x satisfies the scenario) &gt;=
 * alpha.
 *
 * <p>A scenario whose tables share variables is a conjunction, so its support is checked table by
 * table: sound, and exact when the tables of each scenario have disjoint scopes (unary tables, for
 * example). It explains its pruning for lazy clause generation: a scenario that does not support a
 * value has a table whose tuples with that value each contain a removed value, and those removals,
 * the heaviest scenarios first, with the bound of p that their weight needs, are the reason.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ChanceTable extends Constraint
    implements SatisfiedPresent, Copyable<ChanceTable>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // the largest number of values between the bounds of a variable
  private static final int SPAN_LIMIT = 1 << 20;

  /** The variables, without duplicates. */
  final IntVar[] x;

  /** The weighted number of satisfied scenarios. */
  final IntVar p;

  // table f: its scope (indices into x) and its tuples, as offsets from base of each variable
  final int[][] scope;
  final int[][][] tuples;

  // scenario s: its tables and weight, the scenarios in decreasing weight
  final int[][] scenarioTables;
  final long[] weight;
  final long total;
  private final int[] byWeight;

  // variable i: its smallest value at construction and the number of values up to its largest
  final int[] base;
  final int[] span;

  // the inputs as given, for copies
  private final IntVar[] givenX;
  private final int[][] givenScopes;
  private final int[][][] givenTuples;
  private final int[][] givenScenarios;
  private final long[] givenWeights;

  private final Map<Var, Integer> position;

  /**
   * It constructs the constraint with one table over all of x for each scenario.
   *
   * @param x the decisions
   * @param tables the tuples of each scenario, each of x.length values
   * @param weights the weight of each scenario, at least 0
   * @param p the total weight of the scenarios that x satisfies
   */
  public ChanceTable(IntVar[] x, int[][][] tables, long[] weights, IntVar p) {
    this(x, fullScopes(x.length, tables.length), tables, identity(tables.length), weights, p);
  }

  /**
   * It constructs the constraint over shared tables.
   *
   * @param x the decisions
   * @param scopes the scope of each table, indices into x
   * @param tuples the tuples of each table, each with the values of its scope
   * @param scenarios the tables of each scenario, indices into scopes; it holds when x is a tuple
   *     of each of them
   * @param weights the weight of each scenario, at least 0, of total at most Integer.MAX_VALUE
   * @param p the total weight of the scenarios that x satisfies
   */
  public ChanceTable(
      IntVar[] x, int[][] scopes, int[][][] tuples, int[][] scenarios, long[] weights, IntVar p) {
    checkInput(x, scopes, tuples, scenarios, weights, p);
    this.givenX = x.clone();
    this.givenScopes = scopes;
    this.givenTuples = tuples;
    this.givenScenarios = scenarios;
    this.givenWeights = weights;
    this.p = p;

    // the distinct variables
    Map<Var, Integer> index = new IdentityHashMap<>();
    int[] map = new int[x.length];
    List<IntVar> vars = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      Integer k = index.get(x[i]);
      if (k == null) {
        k = vars.size();
        index.put(x[i], k);
        vars.add(x[i]);
      }
      map[i] = k;
    }
    this.x = vars.toArray(new IntVar[0]);
    this.position = index;
    int n = this.x.length;
    base = new int[n];
    span = new int[n];
    for (int i = 0; i < n; i++) {
      base[i] = this.x[i].min();
      long width = (long) this.x[i].max() - this.x[i].min() + 1;
      if (width > SPAN_LIMIT) {
        throw new IllegalArgumentException(
            "ChanceTable: variable " + this.x[i] + " spans more than " + SPAN_LIMIT + " values");
      }
      span[i] = (int) width;
    }

    // the tables: their tuples inside the domains, without repeats or two values of one variable
    scope = new int[scopes.length][];
    this.tuples = new int[scopes.length][][];
    for (int f = 0; f < scopes.length; f++) {
      int[] sc = new int[scopes[f].length];
      for (int k = 0; k < sc.length; k++) {
        sc[k] = map[scopes[f][k]];
      }
      scope[f] = sc;
      Set<List<Integer>> seen = new LinkedHashSet<>();
      for (int[] t : tuples[f]) {
        if (fits(sc, t)) {
          List<Integer> key = new ArrayList<>(sc.length);
          for (int k = 0; k < sc.length; k++) {
            key.add(t[k] - base[sc[k]]);
          }
          seen.add(key);
        }
      }
      int[][] kept = new int[seen.size()][];
      int r = 0;
      for (List<Integer> key : seen) {
        kept[r++] = key.stream().mapToInt(Integer::intValue).toArray();
      }
      this.tuples[f] = kept;
    }

    // the scenarios of positive weight
    List<int[]> sTables = new ArrayList<>();
    List<Long> sWeights = new ArrayList<>();
    long sum = 0;
    for (int s = 0; s < scenarios.length; s++) {
      if (weights[s] > 0) {
        sTables.add(Arrays.stream(scenarios[s]).distinct().toArray());
        sWeights.add(weights[s]);
        sum += weights[s];
      }
    }
    scenarioTables = sTables.toArray(new int[0][]);
    weight = sWeights.stream().mapToLong(Long::longValue).toArray();
    total = sum;
    byWeight =
        IntStream.range(0, weight.length)
            .boxed()
            .sorted((a, b) -> Long.compare(weight[b], weight[a]))
            .mapToInt(Integer::intValue)
            .toArray();

    numberId = idNumber.incrementAndGet();
    queueIndex = 2;
    setScope(Stream.concat(Arrays.stream(this.x), Stream.of(p)));
  }

  private static void checkInput(
      IntVar[] x, int[][] scopes, int[][][] tuples, int[][] scenarios, long[] weights, IntVar p) {
    if (scopes.length != tuples.length || scenarios.length != weights.length) {
      throw new IllegalArgumentException("ChanceTable: arrays of different lengths");
    }
    for (IntVar v : x) {
      if (v == p) {
        throw new IllegalArgumentException("ChanceTable: p must not be one of the decisions");
      }
    }
    for (int f = 0; f < scopes.length; f++) {
      for (int i : scopes[f]) {
        if (i < 0 || i >= x.length) {
          throw new IllegalArgumentException("ChanceTable: scope index " + i + " out of range");
        }
      }
      for (int[] t : tuples[f]) {
        if (t.length != scopes[f].length) {
          throw new IllegalArgumentException("ChanceTable: tuple of wrong length in table " + f);
        }
      }
    }
    long sum = 0;
    for (int s = 0; s < scenarios.length; s++) {
      if (weights[s] < 0) {
        throw new IllegalArgumentException("ChanceTable: negative weight");
      }
      sum += weights[s];
      if (sum > Integer.MAX_VALUE) {
        throw new IllegalArgumentException("ChanceTable: total weight above Integer.MAX_VALUE");
      }
      for (int f : scenarios[s]) {
        if (f < 0 || f >= scopes.length) {
          throw new IllegalArgumentException("ChanceTable: table index " + f + " out of range");
        }
      }
    }
  }

  private static int[][] fullScopes(int n, int count) {
    int[][] result = new int[count][];
    for (int f = 0; f < count; f++) {
      result[f] = IntStream.range(0, n).toArray();
    }
    return result;
  }

  private static int[][] identity(int count) {
    int[][] result = new int[count][];
    for (int s = 0; s < count; s++) {
      result[s] = new int[] {s};
    }
    return result;
  }

  // whether a tuple lies in the initial domains and gives one value to each repeated variable
  private boolean fits(int[] sc, int[] t) {
    for (int k = 0; k < sc.length; k++) {
      if (!x[sc[k]].domain.contains(t[k])) {
        return false;
      }
      for (int j = 0; j < k; j++) {
        if (sc[j] == sc[k] && t[j] != t[k]) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Returns the number of scenarios of positive weight.
   *
   * @return the number of scenarios
   */
  public int scenarios() {
    return weight.length;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getConsistencyPruningEvent(Var var) {
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(var);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    return var == p ? IntDomain.BOUND : IntDomain.ANY;
  }

  // ---------------------------------------------------------------------------------------------
  // the analysis of a state: the domains of x as flags, and the bounds of p

  /** The state of the tables and scenarios for given domains of x. */
  final class Analysis {
    final boolean[][] in;
    final int[] size;
    // table f: alive, its number of tuples inside the domains, its supported values per position
    final boolean[] alive;
    final long[] valid;
    final boolean[][][] supported;
    // per value of x: the weight of the alive scenarios that do not support it
    final long[][] unsupported;
    final int[][] stamp;
    long live;
    long sure;

    Analysis() {
      int n = x.length;
      in = new boolean[n][];
      unsupported = new long[n][];
      stamp = new int[n][];
      for (int i = 0; i < n; i++) {
        in[i] = new boolean[span[i]];
        unsupported[i] = new long[span[i]];
        stamp[i] = new int[span[i]];
      }
      size = new int[n];
      alive = new boolean[scope.length];
      valid = new long[scope.length];
      supported = new boolean[scope.length][][];
      for (int f = 0; f < scope.length; f++) {
        supported[f] = new boolean[scope[f].length][];
        for (int k = 0; k < scope[f].length; k++) {
          supported[f][k] = new boolean[span[scope[f][k]]];
        }
      }
    }

    void readDomains() {
      for (int i = 0; i < x.length; i++) {
        Arrays.fill(in[i], false);
        int count = 0;
        for (ValueEnumeration e = x[i].dom().valueEnumeration(); e.hasMoreElements(); ) {
          int v = e.nextElement() - base[i];
          if (v >= 0 && v < span[i]) {
            in[i][v] = true;
            count++;
          }
        }
        size[i] = count;
      }
    }

    void readTrail(AtomicTrail trail, int pos) {
      EntryList scratch = new EntryList();
      for (int i = 0; i < x.length; i++) {
        int count = 0;
        for (int v = 0; v < span[i]; v++) {
          scratch.clear();
          in[i][v] = !trail.excludedBefore(x[i], base[i] + v, pos, scratch);
          if (in[i][v]) {
            count++;
          }
        }
        size[i] = count;
      }
    }

    void run() {
      for (int f = 0; f < scope.length; f++) {
        table(f);
      }
      for (int i = 0; i < x.length; i++) {
        Arrays.fill(unsupported[i], 0);
        Arrays.fill(stamp[i], 0);
      }
      live = 0;
      sure = 0;
      for (int s = 0; s < weight.length; s++) {
        if (!scenarioAlive(s)) {
          continue;
        }
        live += weight[s];
        if (scenarioSure(s)) {
          sure += weight[s];
        }
        for (int f : scenarioTables[s]) {
          int[] sc = scope[f];
          for (int k = 0; k < sc.length; k++) {
            int i = sc[k];
            boolean[] sup = supported[f][k];
            for (int v = 0; v < span[i]; v++) {
              if (in[i][v] && !sup[v] && stamp[i][v] != s + 1) {
                stamp[i][v] = s + 1;
                unsupported[i][v] += weight[s];
              }
            }
          }
        }
      }
    }

    boolean scenarioAlive(int s) {
      for (int f : scenarioTables[s]) {
        if (!alive[f]) {
          return false;
        }
      }
      return true;
    }

    boolean scenarioSure(int s) {
      for (int f : scenarioTables[s]) {
        if (!full(f)) {
          return false;
        }
      }
      return true;
    }

    // whether every tuple of the domains of the scope is in the table
    boolean full(int f) {
      long box = 1;
      int[] sc = scope[f];
      for (int k = 0; k < sc.length; k++) {
        boolean repeated = false;
        for (int j = 0; j < k; j++) {
          repeated |= sc[j] == sc[k];
        }
        if (!repeated) {
          box *= size[sc[k]];
          if (box > valid[f]) {
            return false;
          }
        }
      }
      return box == valid[f];
    }

    private void table(int f) {
      int[] sc = scope[f];
      for (boolean[] sup : supported[f]) {
        Arrays.fill(sup, false);
      }
      long count = 0;
      for (int[] t : tuples[f]) {
        int bad = -1;
        boolean twice = false;
        for (int k = 0; k < sc.length && !twice; k++) {
          if (!in[sc[k]][t[k]]) {
            if (bad >= 0) {
              twice = true;
            } else {
              bad = k;
            }
          }
        }
        if (twice) {
          continue;
        }
        if (bad < 0) {
          count++;
          for (int k = 0; k < sc.length; k++) {
            supported[f][k][t[k]] = true;
          }
        } else {
          supported[f][bad][t[bad]] = true;
        }
      }
      valid[f] = count;
      alive[f] = count > 0;
    }
  }

  private Analysis analysis;

  @Override
  public void consistency(Store store) {
    if (analysis == null) {
      analysis = new Analysis();
    }
    Analysis a = analysis;
    boolean changed = true;
    while (changed) {
      changed = false;
      a.readDomains();
      a.run();
      p.domain.in(store.level, p, (int) a.sure, (int) a.live);
      int alpha = p.min();
      for (int i = 0; i < x.length; i++) {
        for (int v = 0; v < span[i]; v++) {
          if (a.in[i][v] && a.live - a.unsupported[i][v] < alpha) {
            x[i].domain.inComplement(store.level, x[i], base[i] + v);
            changed = true;
          }
        }
      }
    }
  }

  @Override
  public boolean satisfied() {
    if (!p.singleton()) {
      return false;
    }
    long w = 0;
    for (IntVar v : x) {
      if (!v.singleton()) {
        return false;
      }
    }
    for (int s = 0; s < weight.length; s++) {
      if (holds(s)) {
        w += weight[s];
      }
    }
    return w == p.value();
  }

  // whether scenario s holds for ground x
  private boolean holds(int s) {
    for (int f : scenarioTables[s]) {
      boolean found = false;
      for (int[] t : tuples[f]) {
        boolean match = true;
        for (int k = 0; k < t.length && match; k++) {
          match = x[scope[f][k]].value() - base[scope[f][k]] == t[k];
        }
        if (match) {
          found = true;
          break;
        }
      }
      if (!found) {
        return false;
      }
    }
    return true;
  }

  // ---------------------------------------------------------------------------------------------
  // explanations

  /** One explanation: the state at a trail position and the proofs found so far. */
  private final class Explanation {
    final AtomicTrail trail;
    final int pos;
    final Analysis state;
    // key (table, relaxed position + 1 or 0, value) to the entries that kill its tuples, or null
    final Map<Long, int[]> proofs = new HashMap<>();
    final EntryList scratch = new EntryList();

    Explanation(AtomicTrail trail, int pos) {
      this.trail = trail;
      this.pos = pos;
      this.state = new Analysis();
      state.readTrail(trail, pos);
      state.run();
    }

    // the entries that kill every tuple of table f, or every tuple with value v at position k
    // when k >= 0; null when some such tuple has all its other values in the domains
    int[] killers(int f, int k, int v) {
      long key = ((long) f << 40) | ((long) (k + 1) << 20) | v;
      if (proofs.containsKey(key)) {
        return proofs.get(key);
      }
      int[] sc = scope[f];
      EntryList found = new EntryList();
      int[] result = null;
      boolean all = true;
      for (int[] t : tuples[f]) {
        if (k >= 0 && t[k] != v) {
          continue;
        }
        boolean killed = false;
        for (int j = 0; j < sc.length && !killed; j++) {
          if (j != k && !state.in[sc[j]][t[j]]) {
            scratch.clear();
            trail.excludedBefore(x[sc[j]], base[sc[j]] + t[j], pos, scratch);
            for (int r = 0; r < scratch.size(); r++) {
              found.add(scratch.get(r));
            }
            killed = true;
          }
        }
        if (!killed) {
          all = false;
          break;
        }
      }
      if (all) {
        found.sortUnique(0);
        result = new int[found.size()];
        for (int r = 0; r < result.length; r++) {
          result[r] = found.get(r);
        }
      }
      proofs.put(key, result);
      return result;
    }

    // a proof that scenario s does not support value v of x[i] (any value when i < 0): a table
    // with no tuple left, or one whose tuples with the value are all killed by other variables
    int[] notSupporting(int s, int i, int v) {
      for (int f : scenarioTables[s]) {
        int k = -1;
        int[] sc = scope[f];
        for (int j = 0; j < sc.length; j++) {
          if (sc[j] == i) {
            k = j;
          }
        }
        int[] proof = k >= 0 ? killers(f, k, v) : killers(f, -1, 0);
        if (proof != null) {
          return proof;
        }
      }
      return null;
    }

    // adds the proofs of the heaviest scenarios that do not support (i, v) until the rest weighs
    // below p's lower bound; returns the bound of p they need, or -1 when none suffices
    long excludeBelow(int i, int v, EntryList out) {
      long pMin = trail.minBefore(p, pos);
      long rest = total;
      for (int s : byWeight) {
        if (rest < pMin) {
          break;
        }
        int[] proof = notSupporting(s, i, v);
        if (proof != null) {
          for (int e : proof) {
            out.add(e);
          }
          rest -= weight[s];
        }
      }
      return rest < pMin ? rest + 1 : -1;
    }

    // adds the proofs that the heaviest sure scenarios are sure until they weigh at least need
    boolean sureAtLeast(long need, EntryList out) {
      long got = 0;
      Set<Integer> vars = new LinkedHashSet<>();
      for (int s : byWeight) {
        if (got >= need) {
          break;
        }
        if (state.scenarioAlive(s) && state.scenarioSure(s)) {
          got += weight[s];
          for (int f : scenarioTables[s]) {
            for (int i : scope[f]) {
              vars.add(i);
            }
          }
        }
      }
      if (got < need) {
        return false;
      }
      for (int i : vars) {
        trail.atomsBefore(x[i], pos, out);
      }
      return true;
    }
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    Integer index = position.get(trail.variable(entry));
    int kind = trail.kind(entry);
    int mark = out.size();
    Explanation ex = new Explanation(trail, entry);
    boolean ok;
    if (index == null) {
      ok = trail.variable(entry) == p && explainBound(ex, entry, kind, out);
    } else {
      ok = explainValues(ex, index, entry, kind, out);
    }
    if (!ok) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  private boolean explainBound(Explanation ex, int entry, int kind, EntryList out) {
    AtomicTrail trail = ex.trail;
    if (kind == AtomicTrail.NE) {
      return false;
    }
    int bound = trail.skippedBound(entry);
    boolean ok =
        kind == AtomicTrail.GE ? ex.sureAtLeast(bound, out) : deadDownTo(ex, bound, out) >= 0;
    if (ok && bound != trail.value(entry)) {
      trail.addSkippedHoles(entry, bound, out);
    }
    return ok;
  }

  // adds the proofs of the heaviest dead scenarios until the rest weighs at most limit
  private long deadDownTo(Explanation ex, long limit, EntryList out) {
    long rest = total;
    for (int s : byWeight) {
      if (rest <= limit) {
        break;
      }
      int[] proof = ex.notSupporting(s, -1, 0);
      if (proof != null) {
        for (int e : proof) {
          out.add(e);
        }
        rest -= weight[s];
      }
    }
    return rest <= limit ? rest : -1;
  }

  private boolean explainValues(Explanation ex, int i, int entry, int kind, EntryList out) {
    AtomicTrail trail = ex.trail;
    IntVar var = x[i];
    int lo;
    int hi;
    if (kind == AtomicTrail.NE) {
      lo = trail.value(entry);
      hi = lo;
    } else if (kind == AtomicTrail.GE) {
      // the values below the bound before are excluded by that bound
      lo = trail.minBefore(var, entry);
      hi = trail.value(entry) - 1;
      trail.addLowerBound(var, entry, out);
    } else {
      lo = trail.value(entry) + 1;
      hi = trail.maxBefore(var, entry);
      trail.addUpperBound(var, entry, out);
    }
    long need = Long.MIN_VALUE;
    for (long u = lo; u <= hi; u++) {
      int v = (int) (u - base[i]);
      if (trail.excludedBefore(var, (int) u, entry, out)) {
        continue;
      }
      if (v < 0 || v >= span[i]) {
        return false;
      }
      long n = ex.excludeBelow(i, v, out);
      if (n < 0) {
        return false;
      }
      need = Math.max(need, n);
    }
    if (need > Long.MIN_VALUE) {
      trail.addBoundReaching(p, entry, true, need, out);
    }
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int mark = out.size();
    int pos = trail.size();
    Explanation ex = new Explanation(trail, pos);
    Analysis a = ex.state;
    long pMin = trail.minBefore(p, pos);
    long pMax = trail.maxBefore(p, pos);
    boolean ok = false;
    if (a.live < pMin) {
      long rest = deadDownTo(ex, pMin - 1, out);
      ok = rest >= 0;
      if (ok) {
        trail.addBoundReaching(p, pos, true, rest + 1, out);
      }
    } else if (a.sure > pMax) {
      ok = ex.sureAtLeast(pMax + 1, out);
      if (ok) {
        trail.addBoundReaching(p, pos, false, pMax, out);
      }
    } else {
      ok = emptyVariable(ex, out);
    }
    if (!ok) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  // a variable all of whose values are unsupported by enough weight
  private boolean emptyVariable(Explanation ex, EntryList out) {
    Analysis a = ex.state;
    long pMin = ex.trail.minBefore(p, ex.pos);
    for (int i = 0; i < x.length; i++) {
      boolean empty = true;
      for (int v = 0; v < span[i] && empty; v++) {
        empty = !a.in[i][v] || a.live - a.unsupported[i][v] < pMin;
      }
      if (!empty) {
        continue;
      }
      int mark = out.size();
      ex.trail.atomsBefore(x[i], ex.pos, out);
      long need = Long.MIN_VALUE;
      boolean ok = true;
      for (int v = 0; v < span[i] && ok; v++) {
        if (a.in[i][v]) {
          long n = ex.excludeBelow(i, v, out);
          ok = n >= 0;
          need = Math.max(need, n);
        }
      }
      if (ok) {
        if (need > Long.MIN_VALUE) {
          ex.trail.addBoundReaching(p, ex.pos, true, need, out);
        }
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  @Override
  public ChanceTable copy(VarMap map) {
    return new ChanceTable(
        map.get(givenX), givenScopes, givenTuples, givenScenarios, givenWeights, map.get(p));
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder();
    result.append(id()).append(" : ChanceTable([");
    for (int i = 0; i < x.length; i++) {
      result.append(i == 0 ? "" : ", ").append(x[i]);
    }
    result.append("], ").append(scope.length).append(" tables, ");
    result.append(weight.length).append(" scenarios of weight ").append(total);
    result.append(", ").append(p).append(")");
    return result.toString();
  }
}
