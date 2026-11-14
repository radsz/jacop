/*
 * ConjunctionSum.java
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
package org.jacop.constraints;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * A lower bound on a weighted sum of conjunctions of value literals: {@code sum >= w[0] * [c[0]] +
 * ... + w[m-1] * [c[m-1]]}, where each conjunction {@code c[t]} is a set of literals {@code x = a}
 * or {@code x != a} and every weight is at least 0. Such sums are the objectives of soft
 * constraints written out term by term, as {@code sum(i, j) [y[i] = a /\ y[j] = b /\ x[a][b] = 0]}.
 *
 * <p>A linear sum over the indicators of the conjunctions counts a term only once all its literals
 * hold. This constraint also counts the terms that wait for one variable only: a term whose
 * literals on other variables all hold costs its weight for every value of that variable that
 * satisfies its own literals on it. The terms waiting for a variable add up to a cost per value,
 * and the least cost over the values left in its domain is a lower bound for that variable; the
 * bound is the weight of the terms that hold plus these least costs, since each term waits for one
 * variable at most. It is the lower bound of partial forward checking for weighted constraint
 * satisfaction (Freuder and Wallace, Partial constraint satisfaction, Artificial Intelligence 58,
 * 1992; Larrosa, Meseguer and Schiex, Maintaining reversible DAC for Max-CSP, Artificial
 * Intelligence 107, 1999), applied to the terms of a sum. The constraint raises the minimum of
 * {@code sum} to the bound and removes the values whose cost would take the bound above the maximum
 * of {@code sum}. The reasons for lazy clause generation are the literals of the terms counted and
 * the removed values of the variables waited for.
 *
 * <p>The bound is kept incrementally. A term with two variables open for it (variables on which one
 * of its literals does not hold yet) costs nothing and watches two of them, as clauses watch two
 * literals in a SAT solver, so it is looked at again only when a watched variable gets fixed. A
 * term left with one open variable or none becomes active until backtracking: its weight goes to
 * the costs of the values of its open variable that satisfy its literals there, or to the weight of
 * the terms that hold. Each propagation then reads the least costs of the variables in their
 * domains. A reason is built from the terms active just before its atom.
 *
 * <p>The constraint is redundant next to the linear sum it bounds: it neither fixes the indicators
 * nor bounds the sum from above.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ConjunctionSum extends Constraint
    implements SatisfiedPresent, Copyable<ConjunctionSum>, Explainable, Stateful {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The largest span of values of a variable in a literal. */
  public static final int MAX_SPAN = 1024;

  private final IntVar[] vars;
  private final int[] weights;
  private final IntVar sum;

  // literals of term t at start[t] .. start[t + 1] - 1: variable index, value, and equality or not
  private final int[] start;
  private final int[] litVar;
  private final int[] litValue;
  private final boolean[] litEq;

  // per variable: the least value of its initial domain and the offset of its costs in cost and
  // ecost; ecost holds the costs that evaluate computes for explanations
  private final int[] base;
  private final int[] offset;
  private final long[] ecost;

  // per term: -2 not counted, -1 holds, else the variable it waits for (filled by evaluate)
  private final int[] status;
  // the variables some term waits for, and whether each is listed
  private final int[] waited;
  private int waitedCount;
  private final boolean[] isWaited;
  // the least cost of each variable waited for
  private final long[] eleast;

  // per variable, and at index n for the terms that hold: the stack positions of the active terms
  // waiting for it, in stack order
  private final int[][] bucket;
  private final int[] bucketSize;

  // ---- incremental state, kept by consistency ----
  // each term not active watches two variables that are open for it (some literal of the term on
  // the variable does not hold), as two watched literals do in a SAT solver; a term with at most
  // one open variable is active: it costs its weight in fixedSum (none open) or in the costs per
  // value of its open variable, which only grow as the other variables of the term stay fixed
  private final long[] cost;
  private long fixedSum;
  private final int[] pendingCount;
  private final int[] watch1;
  private final int[] watch2;
  private final int[][] watches;
  private final int[] watchSize;
  private final boolean[] active;
  private final int[] openVar;
  private final int[] stackTerm;
  private final int[] stackLevel;
  // the size of the trail of lazy clause generation when the term was activated: the term's
  // literals
  // hold in the domains given by the atoms before that position
  private final int[] stackPos;
  private int stackSize;
  private Store store;
  private final int[] queue;
  private final boolean[] queued;
  private int queueSize;
  private final int[] seen;
  private int seenStamp;
  private final Map<IntVar, Integer> indexOf;

  // the conjunctions as given, for copies and printing
  private final IntVar[][] termVars;
  private final int[][] termValues;
  private final boolean[][] termEq;

  /**
   * It constructs the bound.
   *
   * @param termVars the variables of the literals of each term.
   * @param termValues the values of the literals of each term.
   * @param termEq for each literal, true for {@code x = a} and false for {@code x != a}.
   * @param weights the weight of each term, at least 0.
   * @param sum the variable bounded from below by the weighted sum.
   */
  public ConjunctionSum(
      IntVar[][] termVars, int[][] termValues, boolean[][] termEq, int[] weights, IntVar sum) {
    if (termVars == null
        || termValues == null
        || termEq == null
        || weights == null
        || sum == null) {
      throw new IllegalArgumentException("ConjunctionSum needs terms, weights and a sum");
    }
    int m = termVars.length;
    if (termValues.length != m || termEq.length != m || weights.length != m) {
      throw new IllegalArgumentException(
          "ConjunctionSum needs a value, a kind and a weight per term");
    }
    this.numberId = idNumber.incrementAndGet();
    this.termVars = termVars;
    this.termValues = termValues;
    this.termEq = termEq;
    this.weights = Arrays.copyOf(weights, m);
    this.sum = sum;

    Map<IntVar, Integer> index = new IdentityHashMap<>();
    int literals = 0;
    for (int t = 0; t < m; t++) {
      if (weights[t] < 0) {
        throw new IllegalArgumentException("ConjunctionSum needs weights of at least 0");
      }
      if (termValues[t].length != termVars[t].length || termEq[t].length != termVars[t].length) {
        throw new IllegalArgumentException("ConjunctionSum needs a value and a kind per literal");
      }
      for (IntVar x : termVars[t]) {
        if (x == sum) {
          throw new IllegalArgumentException("ConjunctionSum: the sum cannot be in a literal");
        }
        index.putIfAbsent(x, index.size());
      }
      literals += termVars[t].length;
    }
    int n = index.size();
    this.vars = new IntVar[n];
    for (Map.Entry<IntVar, Integer> e : index.entrySet()) {
      vars[e.getValue()] = e.getKey();
    }
    this.base = new int[n];
    this.offset = new int[n + 1];
    for (int v = 0; v < n; v++) {
      long span = (long) vars[v].max() - vars[v].min() + 1;
      if (span > MAX_SPAN) {
        throw new IllegalArgumentException(
            "ConjunctionSum needs variables with at most " + MAX_SPAN + " values: " + vars[v]);
      }
      base[v] = vars[v].min();
      offset[v + 1] = offset[v] + (int) span;
    }
    this.ecost = new long[offset[n]];
    this.cost = new long[offset[n]];
    this.start = new int[m + 1];
    this.litVar = new int[literals];
    this.litValue = new int[literals];
    this.litEq = new boolean[literals];
    int k = 0;
    for (int t = 0; t < m; t++) {
      start[t] = k;
      for (int l = 0; l < termVars[t].length; l++) {
        litVar[k] = index.get(termVars[t][l]);
        litValue[k] = termValues[t][l];
        litEq[k] = termEq[t][l];
        k++;
      }
    }
    start[m] = k;
    this.status = new int[m];
    this.waited = new int[n];
    this.isWaited = new boolean[n];
    this.eleast = new long[n];
    this.bucket = new int[n + 1][4];
    this.bucketSize = new int[n + 1];
    this.pendingCount = new int[n];
    this.watch1 = new int[m];
    this.watch2 = new int[m];
    this.watches = new int[n][4];
    this.watchSize = new int[n];
    this.active = new boolean[m];
    this.openVar = new int[m];
    this.stackTerm = new int[m];
    this.stackLevel = new int[m];
    this.stackPos = new int[m];
    this.queue = new int[n];
    this.queued = new boolean[n];
    this.seen = new int[m];
    this.indexOf = index;

    this.explained = new int[n];
    this.leastStamp = new int[n];
    this.queueIndex = 2;
    setScope(Stream.concat(Arrays.stream(vars), Stream.of(sum)));
  }

  // ---- the bound over the current domains -------------------------------------------------

  /** The domains the bound is computed over: now, or just before a trail position. */
  private interface Domains {
    boolean contains(int v, int value);

    int min(int v);

    int max(int v);

    boolean singleton(int v, int value);
  }

  private final Domains now =
      new Domains() {
        @Override
        public boolean contains(int v, int value) {
          return vars[v].domain.contains(value);
        }

        @Override
        public int min(int v) {
          return vars[v].min();
        }

        @Override
        public int max(int v) {
          return vars[v].max();
        }

        @Override
        public boolean singleton(int v, int value) {
          return vars[v].singleton(value);
        }
      };

  // the domains just before a trail position: the bounds read once per variable, and a value
  // between them once when first asked for
  private final class Before implements Domains {
    private AtomicTrail trail;
    private int position;
    private int stamp;
    private int[] boundsRead;
    private int[] lo;
    private int[] hi;
    private int[] valueRead;
    private boolean[] in;
    private final EntryList scratch = new EntryList();

    void reset(AtomicTrail trail, int position) {
      if (boundsRead == null) {
        int n = vars.length;
        boundsRead = new int[n];
        lo = new int[n];
        hi = new int[n];
        valueRead = new int[offset[n]];
        in = new boolean[offset[n]];
      }
      this.trail = trail;
      this.position = position;
      stamp++;
    }

    private void read(int v) {
      if (boundsRead[v] != stamp) {
        boundsRead[v] = stamp;
        lo[v] = trail.minBefore(vars[v], position);
        hi[v] = trail.maxBefore(vars[v], position);
      }
    }

    @Override
    public boolean contains(int v, int value) {
      read(v);
      if (value < lo[v] || value > hi[v]) {
        return false;
      }
      if (value == lo[v] || value == hi[v]) {
        return true;
      }
      int i = offset[v] + value - base[v];
      if (valueRead[i] != stamp) {
        valueRead[i] = stamp;
        scratch.clear();
        in[i] = !trail.excludedBefore(vars[v], value, position, scratch);
      }
      return in[i];
    }

    @Override
    public int min(int v) {
      read(v);
      return lo[v];
    }

    @Override
    public int max(int v) {
      read(v);
      return hi[v];
    }

    @Override
    public boolean singleton(int v, int value) {
      read(v);
      return lo[v] == value && hi[v] == value;
    }
  }

  private final Before before = new Before();

  private boolean holds(int k, Domains d) {
    return litEq[k] ? d.singleton(litVar[k], litValue[k]) : !d.contains(litVar[k], litValue[k]);
  }

  private boolean fails(int k, Domains d) {
    return litEq[k] ? !d.contains(litVar[k], litValue[k]) : d.singleton(litVar[k], litValue[k]);
  }

  // whether value b of variable v satisfies the literals of term t on v
  private boolean satisfiedBy(int t, int v, int b) {
    for (int k = start[t]; k < start[t + 1]; k++) {
      if (litVar[k] == v && (litEq[k] ? litValue[k] != b : litValue[k] == b)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Computes the status of every term, the costs per value of the variables waited for and their
   * least costs over the given domains.
   *
   * @return the weight of the terms that hold
   */
  private long evaluate(Domains d) {
    for (int i = 0; i < waitedCount; i++) {
      int v = waited[i];
      isWaited[v] = false;
      Arrays.fill(ecost, offset[v], offset[v + 1], 0L);
    }
    waitedCount = 0;
    long fixed = 0;
    int m = weights.length;
    for (int t = 0; t < m; t++) {
      int pending = -1;
      int st = -1;
      for (int k = start[t]; k < start[t + 1]; k++) {
        if (holds(k, d)) {
          continue;
        }
        int v = litVar[k];
        if (fails(k, d)) {
          st = -2;
          break;
        }
        if (pending == -1) {
          pending = v;
        } else if (pending != v) {
          st = -2;
          // a later literal may fail; either way the term is not counted
          break;
        }
      }
      if (st == -2 || weights[t] == 0) {
        status[t] = -2;
        continue;
      }
      if (pending == -1) {
        status[t] = -1;
        fixed += weights[t];
        continue;
      }
      status[t] = pending;
      if (!isWaited[pending]) {
        isWaited[pending] = true;
        waited[waitedCount++] = pending;
      }
      int o = offset[pending] - base[pending];
      for (int b = d.min(pending); b <= d.max(pending); b++) {
        if (d.contains(pending, b) && satisfiedBy(t, pending, b)) {
          ecost[o + b] += weights[t];
        }
      }
    }
    for (int i = 0; i < waitedCount; i++) {
      int v = waited[i];
      long low = Long.MAX_VALUE;
      int o = offset[v] - base[v];
      for (int b = d.min(v); b <= d.max(v); b++) {
        if (d.contains(v, b) && ecost[o + b] < low) {
          low = ecost[o + b];
        }
      }
      eleast[v] = low == Long.MAX_VALUE ? 0 : low;
    }
    return fixed;
  }

  // whether variable v is open for term t: a literal of t on v does not hold
  private boolean open(int t, int v) {
    for (int k = start[t]; k < start[t + 1]; k++) {
      if (litVar[k] == v && !holds(k, now)) {
        return true;
      }
    }
    return false;
  }

  // the first open variable of t other than skip and avoid, or -1
  private int otherOpen(int t, int skip, int avoid) {
    for (int k = start[t]; k < start[t + 1]; k++) {
      int v = litVar[k];
      if (v != skip && v != avoid && !holds(k, now)) {
        return v;
      }
    }
    return -1;
  }

  private void addWatch(int v, int t) {
    if (watchSize[v] == watches[v].length) {
      watches[v] = Arrays.copyOf(watches[v], 2 * watches[v].length);
    }
    watches[v][watchSize[v]++] = t;
  }

  private void activate(int t, int level, int u) {
    active[t] = true;
    openVar[t] = u;
    int b = u < 0 ? vars.length : u;
    if (bucketSize[b] == bucket[b].length) {
      bucket[b] = Arrays.copyOf(bucket[b], 2 * bucket[b].length);
    }
    bucket[b][bucketSize[b]++] = stackSize;
    stackTerm[stackSize] = t;
    stackLevel[stackSize] = level;
    stackPos[stackSize++] =
        store != null && store.domainChangeRecorder instanceof AtomicTrail trail ? trail.size() : 0;
    contribute(t, u, weights[t]);
  }

  // adds w to the cost of t: to fixedSum, or to the values of u that satisfy t's literals on u
  private void contribute(int t, int u, long w) {
    if (u < 0) {
      fixedSum += w;
      return;
    }
    pendingCount[u] += w > 0 ? 1 : -1;
    addCost(cost, t, u, w);
  }

  // adds w to costs at the values of u that satisfy t's literals on u
  private void addCost(long[] costs, int t, int u, long w) {
    int o = offset[u] - base[u];
    int eq = Integer.MIN_VALUE;
    boolean anyNe = false;
    for (int k = start[t]; k < start[t + 1]; k++) {
      if (litVar[k] != u) {
        continue;
      }
      if (!litEq[k]) {
        anyNe = true;
      } else if (eq == Integer.MIN_VALUE) {
        eq = litValue[k];
      } else if (eq != litValue[k]) {
        // two different values: no value satisfies the term
        return;
      }
    }
    if (eq != Integer.MIN_VALUE) {
      // a literal u = a: only a can satisfy the term
      if (eq >= base[u]
          && eq < base[u] + offset[u + 1] - offset[u]
          && (!anyNe || satisfiedBy(t, u, eq))) {
        costs[o + eq] += w;
      }
      return;
    }
    for (int i = offset[u]; i < offset[u + 1]; i++) {
      costs[i] += w;
    }
    for (int k = start[t]; k < start[t + 1]; k++) {
      int a = litValue[k];
      if (litVar[k] == u
          && a >= base[u]
          && a < base[u] + offset[u + 1] - offset[u]
          && firstNe(t, k)) {
        costs[o + a] -= w;
      }
    }
  }

  // whether literal k of term t is the first literal u != a of t for its variable and value
  private boolean firstNe(int t, int k) {
    for (int j = start[t]; j < k; j++) {
      if (litVar[j] == litVar[k] && litValue[j] == litValue[k]) {
        return false;
      }
    }
    return true;
  }

  @Override
  public void impose(Store store) {
    super.impose(store);
    this.store = store;
    for (int t = 0; t < weights.length; t++) {
      if (weights[t] == 0) {
        continue;
      }
      int a = otherOpen(t, -1, -1);
      int b = a < 0 ? -1 : otherOpen(t, a, -1);
      if (b >= 0) {
        watch1[t] = a;
        watch2[t] = b;
        addWatch(a, t);
        addWatch(b, t);
      } else {
        watch1[t] = a;
        watch2[t] = -1;
        if (a >= 0) {
          addWatch(a, t);
        }
        activate(t, store.level, a);
      }
    }
  }

  @Override
  public void queueVariable(int level, Var var) {
    Integer i = indexOf.get(var);
    if (i != null && !queued[i]) {
      queued[i] = true;
      queue[queueSize++] = i;
    }
  }

  @Override
  public void removeLevel(int level) {
    while (stackSize > 0 && stackLevel[stackSize - 1] >= level) {
      int t = stackTerm[--stackSize];
      active[t] = false;
      bucketSize[openVar[t] < 0 ? vars.length : openVar[t]]--;
      contribute(t, openVar[t], -weights[t]);
    }
  }

  // the terms watching v whose literals on v all hold now look for another open variable
  private void process(int v, int level) {
    int[] list = watches[v];
    int size = watchSize[v];
    int kept = 0;
    seenStamp++;
    for (int i = 0; i < size; i++) {
      int t = list[i];
      if ((watch1[t] != v && watch2[t] != v) || seen[t] == seenStamp) {
        // moved away, or listed twice
        continue;
      }
      seen[t] = seenStamp;
      if (active[t] || open(t, v)) {
        list[kept++] = t;
        continue;
      }
      int other = watch1[t] == v ? watch2[t] : watch1[t];
      if (other >= 0 && !open(t, other)) {
        other = -1;
      }
      int first = other >= 0 ? other : otherOpen(t, v, -1);
      int second = first < 0 ? -1 : otherOpen(t, v, first);
      if (second >= 0) {
        // two open variables again: t leaves v
        if (first != watch1[t] && first != watch2[t]) {
          addWatch(first, t);
        }
        if (second != watch1[t] && second != watch2[t]) {
          addWatch(second, t);
        }
        watch1[t] = first;
        watch2[t] = second;
        continue;
      }
      // at most one open variable: t is active and keeps watching v
      list[kept++] = t;
      activate(t, level, first);
    }
    // terms added to this list while it was scanned cannot be v's own: copy the rest over
    int added = watchSize[v] - size;
    if (added > 0) {
      System.arraycopy(watches[v], size, watches[v], kept, added);
    }
    watchSize[v] = kept + added;
  }

  @Override
  public void consistency(Store store) {
    boolean changed;
    do {
      changed = false;
      while (queueSize > 0) {
        int v = queue[--queueSize];
        queued[v] = false;
        process(v, store.level);
      }
      long lb = fixedSum;
      for (int v = 0; v < vars.length; v++) {
        long low = 0;
        if (pendingCount[v] > 0) {
          low = Long.MAX_VALUE;
          IntDomain d = vars[v].domain;
          int o = offset[v] - base[v];
          for (int b = d.min(); b <= d.max(); b++) {
            if (cost[o + b] < low && d.contains(b)) {
              low = cost[o + b];
            }
          }
        }
        eleast[v] = low;
        lb += low;
      }
      if (lb > sum.max()) {
        throw Store.failException;
      }
      if (lb > sum.min()) {
        sum.domain.inMin(store.level, sum, (int) lb);
      }
      long max = sum.max();
      for (int v = 0; v < vars.length; v++) {
        if (pendingCount[v] == 0) {
          continue;
        }
        long slack = max - (lb - eleast[v]);
        IntVar x = vars[v];
        int o = offset[v] - base[v];
        for (int b = x.min(); b <= x.max(); b++) {
          if (cost[o + b] > slack && x.domain.contains(b)) {
            x.domain.inComplement(store.level, x, b);
            changed = true;
          }
        }
      }
    } while (changed || queueSize > 0);
  }

  /**
   * Returns the bound computed from scratch over the current domains, which the incremental bound
   * of {@link #consistency} reaches at its fixpoint; for tests.
   *
   * @return the weight of the terms that hold plus the least costs of the variables waited for
   */
  public long scratchBound() {
    long lb = evaluate(now);
    for (int i = 0; i < waitedCount; i++) {
      lb += eleast[waited[i]];
    }
    return lb;
  }

  // ---- explanations -----------------------------------------------------------------------

  // the explanation being built: its domains, the number of stack entries active before its atom,
  // the variables whose bounds it cites and whose costs and least costs it has computed
  private Before explaining;
  private int prefix;
  private int[] cited;
  private int citeStamp;
  private final int[] explained;
  private final int[] leastStamp;

  /**
   * Starts an explanation at a trail position. The terms active just before it are a prefix of the
   * stack, those activated when the trail was not longer than the position, since the stack and the
   * trail grow together.
   */
  private Before startExplanation(AtomicTrail trail, int position) {
    before.reset(trail, position);
    explaining = before;
    if (cited == null) {
      cited = new int[vars.length];
    }
    citeStamp++;
    int lo = 0;
    int hi = stackSize;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (stackPos[mid] <= position) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    prefix = lo;
    return before;
  }

  // the number of entries of bucket b in the prefix
  private int inPrefix(int b) {
    int size = bucketSize[b];
    if (size == 0 || bucket[b][size - 1] < prefix) {
      return size;
    }
    int lo = 0;
    int hi = size;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (bucket[b][mid] < prefix) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return lo;
  }

  // the costs of v's values from the terms of the prefix in ecost: the costs now less those of the
  // terms activated after the prefix
  private void costsAt(int v) {
    if (explained[v] == citeStamp) {
      return;
    }
    explained[v] = citeStamp;
    int o = offset[v];
    System.arraycopy(cost, o, ecost, o, offset[v + 1] - o);
    for (int i = inPrefix(v); i < bucketSize[v]; i++) {
      int t = stackTerm[bucket[v][i]];
      addCost(ecost, t, v, -weights[t]);
    }
  }

  // the least cost of v over its domain before the position, from the terms of the prefix
  private long leastAt(int v, Domains d) {
    if (leastStamp[v] == citeStamp) {
      return eleast[v];
    }
    leastStamp[v] = citeStamp;
    costsAt(v);
    long low = Long.MAX_VALUE;
    int o = offset[v] - base[v];
    for (int b = d.min(v); b <= d.max(v); b++) {
      if (ecost[o + b] < low && d.contains(v, b)) {
        low = ecost[o + b];
      }
    }
    eleast[v] = low == Long.MAX_VALUE ? 0 : low;
    return eleast[v];
  }

  // the reasons of the terms of the prefix waiting for v, except their literals on v
  private void waitingReason(AtomicTrail trail, int position, int v, EntryList out) {
    int end = inPrefix(v);
    for (int i = 0; i < end; i++) {
      termReason(trail, position, stackTerm[bucket[v][i]], v, out);
    }
  }

  // the reason that literal k holds just before the position: the bounds of its variable when it
  // is fixed, cited once per explanation, else the removal of the value of a disequality
  private void literalReason(AtomicTrail trail, int position, int k, EntryList out) {
    int v = litVar[k];
    IntVar x = vars[v];
    if (explaining.singleton(v, explaining.min(v))) {
      if (cited[v] != citeStamp) {
        cited[v] = citeStamp;
        trail.addLowerBound(x, position, out);
        trail.addUpperBound(x, position, out);
      }
      return;
    }
    trail.excludedBefore(x, litValue[k], position, out);
  }

  // the reasons of term t's literals that hold, except those on variable skip
  private void termReason(AtomicTrail trail, int position, int t, int skip, EntryList out) {
    for (int k = start[t]; k < start[t + 1]; k++) {
      if (litVar[k] != skip) {
        literalReason(trail, position, k, out);
      }
    }
  }

  // the reason of variable v's least cost: its removed values that cost less, and its terms
  private void leastReason(AtomicTrail trail, int position, int v, Domains d, EntryList out) {
    IntVar x = vars[v];
    IntDomain root = trail.rootDomain(x);
    int o = offset[v] - base[v];
    for (int b = root.min(); b <= root.max(); b++) {
      if (ecost[o + b] < eleast[v] && root.contains(b) && !d.contains(v, b)) {
        // a removed value cheaper than the least; values outside the initial domain need none
        trail.excludedBefore(x, b, position, out);
      }
    }
    // the values left cost at least eleast[v] through the terms waiting for v
    waitingReason(trail, position, v, out);
  }

  /**
   * Adds the reasons of terms that hold and of least costs, skipping variable skip, until they
   * reach need; false when all of them fall short.
   */
  private boolean contributions(
      AtomicTrail trail, int position, Domains d, int skip, long need, EntryList out) {
    long got = 0;
    int held = inPrefix(vars.length);
    for (int i = 0; i < held && got < need; i++) {
      int t = stackTerm[bucket[vars.length][i]];
      termReason(trail, position, t, -1, out);
      got += weights[t];
    }
    for (int v = 0; v < vars.length && got < need; v++) {
      if (v != skip && inPrefix(v) > 0) {
        long least = leastAt(v, d);
        if (least > 0) {
          leastReason(trail, position, v, d, out);
          got += least;
        }
      }
    }
    return got >= need;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    int mark = out.size();
    Before d = startExplanation(trail, entry);
    if (y == sum) {
      if (trail.kind(entry) != AtomicTrail.GE) {
        return false;
      }
      if (!contributions(trail, entry, d, -1, trail.value(entry), out)) {
        out.truncate(mark);
        return false;
      }
      out.sortUnique(mark);
      return true;
    }
    Integer index = indexOf.get(y);
    if (index == null || inPrefix(index) == 0) {
      return false;
    }
    int v = index;
    costsAt(v);
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    long max = trail.maxBefore(sum, entry);
    long need = 0;
    boolean any = false;
    int o = offset[v] - base[v];
    for (int b = lo; b <= hi; b++) {
      if (!d.contains(v, b)) {
        trail.excludedBefore(y, b, entry, out);
        continue;
      }
      any = true;
      // b costs ecost[o + b] through the terms waiting for v; the others must bring the rest
      need = Math.max(need, max + 1 - ecost[o + b]);
    }
    if (any) {
      trail.addUpperBound(sum, entry, out);
      waitingReason(trail, entry, v, out);
      if (!contributions(trail, entry, d, v, need, out)) {
        out.truncate(mark);
        return false;
      }
    }
    out.sortUnique(mark);
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int mark = out.size();
    int position = trail.size();
    Before d = startExplanation(trail, position);
    long max = trail.maxBefore(sum, position);
    trail.addUpperBound(sum, position, out);
    if (!contributions(trail, position, d, -1, max + 1, out)) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  // ---- the rest -----------------------------------------------------------------------------

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    for (IntVar x : vars) {
      if (!x.singleton()) {
        return false;
      }
    }
    long total = 0;
    for (int t = 0; t < weights.length; t++) {
      boolean all = true;
      for (int k = start[t]; k < start[t + 1] && all; k++) {
        all = holds(k, now);
      }
      if (all) {
        total += weights[t];
      }
    }
    return total <= sum.min();
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : ConjunctionSum([");
    for (int t = 0; t < weights.length; t++) {
      if (t > 0) {
        result.append(", ");
      }
      result.append(weights[t]).append("*(");
      for (int l = 0; l < termVars[t].length; l++) {
        if (l > 0) {
          result.append(" /\\ ");
        }
        result.append(termVars[t][l].id()).append(termEq[t][l] ? " = " : " != ");
        result.append(termValues[t][l]);
      }
      result.append(")");
    }
    result.append("], ").append(sum).append(")");
    return result.toString();
  }

  @Override
  public ConjunctionSum copy(VarMap map) {
    return new ConjunctionSum(map.get(termVars), termValues, termEq, weights, map.get(sum));
  }
}
