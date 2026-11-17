/*
 * FunctionalTabuSearch.java
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

import java.util.Arrays;
import java.util.SplittableRandom;
import java.util.function.BooleanSupplier;
import java.util.function.IntUnaryOperator;
import org.jacop.core.IntDomain;

/**
 * Tabu search over a cost that is a function of a few decision variables: every other variable is
 * defined by one linear equality, one product or one other function of variables defined before it,
 * and no constraint is left over, so any assignment of the decision variables whose defined values
 * lie in their domains is a solution. A move changes one decision variable to another value of its
 * domain; the values it changes are followed through the definitions in topological order, a linear
 * definition by the change of its inputs alone, so a move costs as much as the variables it
 * changes. A linear variable whose domain holds every value its definition can take and that one
 * linear variable reads (a partial sum of a long sum) is folded into its reader and not evaluated
 * by moves; its domain is checked only when it does not.
 *
 * <p>The search is the memetic tabu search of Gallardo, Cotta and Fernández ("Finding low
 * autocorrelation binary sequences with memetic algorithms", Applied Soft Computing 9(4), 2009,
 * 1252-1262): a population of assignments, each new one the uniform crossover of two parents picked
 * by binary tournament, mutated with probability 1/n per variable and improved by a tabu walk,
 * replaces the worst member when it is better and new. A walk has a random length between half and
 * one and a half times the number n of decision variables; each step takes the best move of a
 * variable that is not tabu (or of any variable when it improves on the walk's best), ties broken
 * at random, and the changed variable stays tabu for a tenth of the walk's length plus a random
 * fiftieth. {@link #improve} instead walks from the current assignment and restarts each walk from
 * the best one with a few variables changed.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class FunctionalTabuSearch {

  /** A variable that is not defined: the moves change it. */
  public static final int DECISION = 0;

  /** A variable defined as a constant plus a weighted sum of its inputs. */
  public static final int LINEAR = 1;

  /** A variable defined as the product of its two inputs. */
  public static final int PRODUCT = 2;

  /** A variable defined by a function of the values of the other variables. */
  public static final int FUNCTION = 3;

  /** A function that defines a variable from the values of the others. */
  @FunctionalInterface
  public interface Definition {

    /**
     * Returns the value of the defined variable.
     *
     * @param value the value of each variable, by its index
     * @return the value of the defined variable
     */
    long value(IntUnaryOperator value);
  }

  // a linear variable put into the linear variable that reads it: not evaluated by moves
  private static final int INLINED = 4;

  private final int n;
  // the definitions as given, in topological order
  private final int[] defKind;
  private final int[][] defInputs;
  private final long[][] defCoefficients;
  private final long[] defConstant;
  private final int[] order;
  // the defined variables whose domain a move must check
  private final boolean[] restrictive;
  // the definitions the moves evaluate
  private final int[] kind;
  private final int[][] inputs;
  private final long[][] coefficients;
  private final long[] constant;
  private final Definition[] functions;
  private final IntDomain[] domains;
  private final long[] lo;
  private final long[] hi;
  private final boolean[] holes;
  private final int cost;
  // the decision variables and the values of their domains
  private final int[] decisions;
  private final int[][] choices;
  // the defined variables that read each variable, and the coefficient of a linear one
  private final int[][] readers;
  private final long[][] readerCoefficients;
  private final int[] rank;
  private final int ranks;
  // the current values; the values of a trial move with their stamp
  private final long[] value;
  private final long[] trial;
  private final long[] pending;
  private final long[] stamp;
  private long epoch;
  // the variables a trial changed, and the queue of definitions to evaluate per rank
  private final int[] changed;
  private int changedSize;
  private final int[][] queue;
  private final int[] queueSize;
  private final IntUnaryOperator trialValue = this::get;
  private final SplittableRandom random;
  private final long[] tabu;
  private long steps;
  private long walks;
  private long best = Long.MAX_VALUE;
  private int[] bestValues;
  private long evaluations;
  // the population of the memetic search: decision values and costs
  private final int populationSize;
  private int[][] population;
  private long[] populationCost;
  private int members;
  // the best assignment of the current walk, as decision values
  private long walkBest;
  private final int[] walkValues;
  private final int[] moveVar;
  private final int[] moveValue;
  // checks after every move that the values equal those of the definitions, for tests
  private boolean verify;

  /**
   * A search over variables 0..n-1.
   *
   * @param kind the kind of each variable ({@link #DECISION}, {@link #LINEAR}, {@link #PRODUCT},
   *     {@link #FUNCTION})
   * @param inputs the variables each defined variable reads (two for a product)
   * @param coefficients the weight of each input of a linear variable, otherwise unused
   * @param constant the constant of a linear variable
   * @param functions the definition of a {@link #FUNCTION} variable, otherwise null
   * @param domains the domain of each variable; a move that gives a defined variable a value
   *     outside its domain is not taken
   * @param cost the variable minimized
   * @param seed the seed of the random choices
   * @throws IllegalArgumentException when the definitions have a cycle
   */
  public FunctionalTabuSearch(
      int[] kind,
      int[][] inputs,
      long[][] coefficients,
      long[] constant,
      Definition[] functions,
      IntDomain[] domains,
      int cost,
      long seed) {
    n = kind.length;
    defKind = kind;
    defInputs = inputs;
    defCoefficients = coefficients;
    defConstant = constant;
    this.functions = functions;
    this.domains = domains;
    this.cost = cost;
    lo = new long[n];
    hi = new long[n];
    holes = new boolean[n];
    int decisionCount = 0;
    for (int v = 0; v < n; v++) {
      lo[v] = domains[v].min();
      hi[v] = domains[v].max();
      holes[v] = domains[v].getSize() != hi[v] - lo[v] + 1;
      if (kind[v] == DECISION) {
        decisionCount++;
      }
    }
    decisions = new int[decisionCount];
    choices = new int[decisionCount][];
    for (int v = 0, d = 0; v < n; v++) {
      if (kind[v] == DECISION) {
        decisions[d] = v;
        choices[d] = values(domains[v]);
        d++;
      }
    }
    // the definitions in topological order, and the bounds of each over the decisions' domains
    int[][] defReaders = readers(kind, inputs);
    int[] defRank = ranks(kind, inputs, defReaders);
    Integer[] sorted = new Integer[n];
    for (int v = 0; v < n; v++) {
      sorted[v] = v;
    }
    Arrays.sort(sorted, (x, y) -> Integer.compare(defRank[x], defRank[y]));
    order = new int[n];
    for (int v = 0; v < n; v++) {
      order[v] = sorted[v];
    }
    restrictive = restrictive();
    // a linear variable whose domain holds all its values and that one linear variable reads is
    // put into its reader (the partial sums of a long sum)
    this.kind = kind.clone();
    this.inputs = inputs.clone();
    this.coefficients = coefficients.clone();
    this.constant = constant.clone();
    for (int v : order) {
      if (kind[v] == LINEAR
          && v != cost
          && !restrictive[v]
          && defReaders[v].length == 1
          && kind[defReaders[v][0]] == LINEAR) {
        this.kind[v] = INLINED;
      }
    }
    for (int v : order) {
      if (this.kind[v] == LINEAR || this.kind[v] == INLINED) {
        expand(v);
      }
    }
    for (int v = 0; v < n; v++) {
      if (this.kind[v] == INLINED) {
        this.inputs[v] = new int[0];
      }
    }
    readers = readers(this.kind, this.inputs);
    readerCoefficients = new long[n][];
    for (int v = 0; v < n; v++) {
      readerCoefficients[v] = new long[readers[v].length];
    }
    int[] count = new int[n];
    for (int v = 0; v < n; v++) {
      if (this.kind[v] != DECISION) {
        for (int k = 0; k < this.inputs[v].length; k++) {
          int u = this.inputs[v][k];
          readerCoefficients[u][count[u]++] = this.kind[v] == LINEAR ? this.coefficients[v][k] : 0;
        }
      }
    }
    rank = ranks(this.kind, this.inputs, readers);
    int top = 0;
    int[] perRank = new int[n + 1];
    for (int v = 0; v < n; v++) {
      top = Math.max(top, rank[v]);
      perRank[rank[v]]++;
    }
    ranks = top + 1;
    queue = new int[ranks][];
    for (int r = 0; r < ranks; r++) {
      queue[r] = new int[perRank[r]];
    }
    queueSize = new int[ranks];
    value = new long[n];
    trial = new long[n];
    pending = new long[n];
    stamp = new long[n];
    changed = new int[n];
    tabu = new long[decisionCount];
    random = new SplittableRandom(seed);
    populationSize = Math.clamp(2000 / Math.max(1, decisionCount), 8, 100);
    walkValues = new int[decisionCount];
    moveVar = new int[4 * decisionCount + 4];
    moveValue = new int[4 * decisionCount + 4];
  }

  // the terms of a linear variable over variables that are not put into their readers
  private void expand(int v) {
    java.util.Map<Integer, Long> terms = new java.util.LinkedHashMap<>();
    long c = defConstant[v];
    for (int k = 0; k < defInputs[v].length; k++) {
      int u = defInputs[v][k];
      long a = defCoefficients[v][k];
      if (kind[u] == INLINED) {
        c += a * constant[u];
        for (int i = 0; i < inputs[u].length; i++) {
          terms.merge(inputs[u][i], a * coefficients[u][i], Long::sum);
        }
      } else {
        terms.merge(u, a, Long::sum);
      }
    }
    terms.values().removeIf(a -> a == 0);
    inputs[v] = terms.keySet().stream().mapToInt(Integer::intValue).toArray();
    coefficients[v] = terms.values().stream().mapToLong(Long::longValue).toArray();
    constant[v] = c;
  }

  // the defined variables whose domain does not hold every value their definition can take
  private boolean[] restrictive() {
    long[] min = new long[n];
    long[] max = new long[n];
    boolean[] r = new boolean[n];
    for (int v : order) {
      switch (defKind[v]) {
        case DECISION -> {
          min[v] = lo[v];
          max[v] = hi[v];
          continue;
        }
        case LINEAR -> {
          long a = defConstant[v];
          long b = defConstant[v];
          for (int k = 0; k < defInputs[v].length; k++) {
            long w = defCoefficients[v][k];
            int u = defInputs[v][k];
            a += w > 0 ? w * min[u] : w * max[u];
            b += w > 0 ? w * max[u] : w * min[u];
          }
          min[v] = a;
          max[v] = b;
        }
        case PRODUCT -> {
          int x = defInputs[v][0];
          int y = defInputs[v][1];
          if (x == y) {
            long m = Math.max(Math.abs(min[x]), Math.abs(max[x]));
            min[v] = min[x] <= 0 && max[x] >= 0 ? 0 : Math.min(min[x] * min[x], max[x] * max[x]);
            max[v] = m * m;
          } else {
            long p = min[x] * min[y];
            long q = min[x] * max[y];
            long t = max[x] * min[y];
            long u = max[x] * max[y];
            min[v] = Math.min(Math.min(p, q), Math.min(t, u));
            max[v] = Math.max(Math.max(p, q), Math.max(t, u));
          }
        }
        default -> {
          min[v] = lo[v];
          max[v] = hi[v];
          r[v] = true;
          continue;
        }
      }
      r[v] =
          min[v] < lo[v]
              || max[v] > hi[v]
              || (holes[v] && !domains[v].contains((int) min[v], (int) max[v]));
      // a variable read with its domain gives later bounds no wider than the domain
      min[v] = Math.max(min[v], lo[v]);
      max[v] = Math.min(max[v], hi[v]);
    }
    return r;
  }

  // the values of a domain
  private static int[] values(IntDomain d) {
    int[] vs = new int[d.getSize()];
    int k = 0;
    for (var e = d.valueEnumeration(); e.hasMoreElements(); ) {
      vs[k++] = e.nextElement();
    }
    return vs;
  }

  // the defined variables that read each variable
  private int[][] readers(int[] kinds, int[][] ins) {
    int[] count = new int[n];
    for (int v = 0; v < n; v++) {
      if (kinds[v] != DECISION) {
        for (int u : ins[v]) {
          count[u]++;
        }
      }
    }
    int[][] rs = new int[n][];
    for (int v = 0; v < n; v++) {
      rs[v] = new int[count[v]];
    }
    Arrays.fill(count, 0);
    for (int v = 0; v < n; v++) {
      if (kinds[v] != DECISION) {
        for (int u : ins[v]) {
          rs[u][count[u]++] = v;
        }
      }
    }
    return rs;
  }

  // the rank of each variable: 0 for a decision, one more than its highest input otherwise
  private int[] ranks(int[] kinds, int[][] ins, int[][] rs) {
    int[] r = new int[n];
    int[] missing = new int[n];
    int[] ready = new int[n];
    int readySize = 0;
    for (int v = 0; v < n; v++) {
      missing[v] = kinds[v] == DECISION ? 0 : ins[v].length;
      if (missing[v] == 0) {
        ready[readySize++] = v;
      }
    }
    int done = 0;
    while (readySize > 0) {
      int v = ready[--readySize];
      done++;
      for (int u : rs[v]) {
        r[u] = Math.max(r[u], r[v] + 1);
        if (--missing[u] == 0) {
          ready[readySize++] = u;
        }
      }
    }
    if (done < n) {
      throw new IllegalArgumentException("the definitions have a cycle");
    }
    return r;
  }

  @Override
  public String toString() {
    int[] kinds = new int[5];
    long reads = 0;
    int most = 0;
    for (int v = 0; v < n; v++) {
      kinds[kind[v]]++;
      reads += readers[v].length;
      most = Math.max(most, readers[v].length);
    }
    return "FunctionalTabuSearch(decisions "
        + kinds[DECISION]
        + ", linear "
        + kinds[LINEAR]
        + ", products "
        + kinds[PRODUCT]
        + ", functions "
        + kinds[FUNCTION]
        + ", inlined "
        + kinds[INLINED]
        + ", reads "
        + reads
        + ", most reads "
        + most
        + ", ranks "
        + ranks
        + ")";
  }

  /**
   * The number of decision variables.
   *
   * @return the number of decision variables
   */
  public int decisions() {
    return decisions.length;
  }

  /**
   * The size of the population of the memetic search.
   *
   * @return the number of assignments it keeps
   */
  public int populationSize() {
    return populationSize;
  }

  /**
   * The tabu steps made so far.
   *
   * @return the steps
   */
  public long steps() {
    return steps;
  }

  /**
   * The walks started so far.
   *
   * @return the walks
   */
  public long walks() {
    return walks;
  }

  /**
   * The moves evaluated so far.
   *
   * @return the evaluations
   */
  public long evaluations() {
    return evaluations;
  }

  /**
   * The best cost found, or {@link Long#MAX_VALUE}.
   *
   * @return the best cost
   */
  public long best() {
    return best;
  }

  /**
   * The values of every variable in the best assignment, or null.
   *
   * @return the values, by variable index
   */
  public int[] bestValues() {
    if (bestValues == null) {
      return null;
    }
    long[] vs = longs(bestValues);
    int[] all = bestValues.clone();
    for (int v : order) {
      if (kind[v] == INLINED) {
        vs[v] = define(v, u -> (int) vs[u], vs);
        all[v] = (int) vs[v];
      }
    }
    return all;
  }

  /** Forgets the best assignment, so that the next walks report what they find from now on. */
  public void forgetBest() {
    best = Long.MAX_VALUE;
    bestValues = null;
  }

  /**
   * The current cost.
   *
   * @return the cost of the current assignment
   */
  public long cost() {
    return value[cost];
  }

  /**
   * Starts from the given values of the decision variables (by variable index; the others are
   * ignored), or from random values for null. Fails when a defined variable falls outside its
   * domain.
   *
   * @param start the values, or null
   * @return true when the assignment is a solution
   */
  public boolean start(int[] start) {
    long[] vs = new long[n];
    for (int d = 0; d < decisions.length; d++) {
      int v = decisions[d];
      vs[v] = start == null ? choices[d][random.nextInt(choices[d].length)] : start[v];
    }
    if (!assign(vs)) {
      return false;
    }
    record();
    return true;
  }

  // evaluates every definition in rank order over the decisions of vs
  private boolean assign(long[] vs) {
    epoch++;
    for (int v : order) {
      if (defKind[v] != DECISION) {
        vs[v] = define(v, u -> (int) vs[u], vs);
      }
      if (!inDomain(v, vs[v])) {
        return false;
      }
    }
    System.arraycopy(vs, 0, value, 0, n);
    Arrays.fill(tabu, 0);
    return true;
  }

  // the value of a variable by its definition as given, over the values of vs
  private long define(int v, IntUnaryOperator of, long[] vs) {
    switch (defKind[v]) {
      case LINEAR -> {
        long s = defConstant[v];
        for (int k = 0; k < defInputs[v].length; k++) {
          s += defCoefficients[v][k] * vs[defInputs[v][k]];
        }
        return s;
      }
      case PRODUCT -> {
        return vs[defInputs[v][0]] * vs[defInputs[v][1]];
      }
      default -> {
        return functions[v].value(of);
      }
    }
  }

  private boolean inDomain(int v, long x) {
    if (x < lo[v] || x > hi[v]) {
      return false;
    }
    return !holes[v] || domains[v].contains((int) x);
  }

  // the value of a variable under the trial move
  private int get(int v) {
    return (int) (stamp[v] == epoch ? trial[v] : value[v]);
  }

  private long getLong(int v) {
    return stamp[v] == epoch ? trial[v] : value[v];
  }

  /**
   * The cost after changing a decision variable, or {@link Long#MAX_VALUE} when a defined variable
   * leaves its domain. The values of the trial stay until the next trial.
   */
  private long evaluate(int x, long to) {
    evaluations++;
    epoch++;
    changedSize = 0;
    set(x, to);
    for (int r = 1; r < ranks; r++) {
      int[] q = queue[r];
      for (int k = 0; k < queueSize[r]; k++) {
        int v = q[k];
        long now;
        if (kind[v] == LINEAR) {
          now = value[v] + pending[v];
        } else if (kind[v] == PRODUCT) {
          now = getLong(inputs[v][0]) * getLong(inputs[v][1]);
        } else {
          now = functions[v].value(trialValue);
        }
        if (now != value[v]) {
          if (restrictive[v] && !inDomain(v, now)) {
            clearQueues(r);
            return Long.MAX_VALUE;
          }
          set(v, now);
        }
      }
      queueSize[r] = 0;
    }
    return getLong(cost);
  }

  private void clearQueues(int from) {
    for (int r = from; r < ranks; r++) {
      queueSize[r] = 0;
    }
  }

  // gives v its trial value and queues its readers
  private void set(int v, long now) {
    long delta = now - value[v];
    trial[v] = now;
    stamp[v] = epoch;
    changed[changedSize++] = v;
    int[] rs = readers[v];
    long[] cs = readerCoefficients[v];
    for (int k = 0; k < rs.length; k++) {
      int u = rs[k];
      if (stamp[u] != epoch && stamp[u] != -epoch) {
        // queued: the negative stamp marks a definition waiting in the queue of its rank
        stamp[u] = -epoch;
        pending[u] = 0;
        queue[rank[u]][queueSize[rank[u]]++] = u;
      }
      if (kind[u] == LINEAR) {
        pending[u] += cs[k] * delta;
      }
    }
  }

  // keeps the values of the last trial
  private void commit() {
    for (int k = 0; k < changedSize; k++) {
      int v = changed[k];
      value[v] = trial[v];
    }
    epoch++;
  }

  private void record() {
    if (value[cost] < best) {
      best = value[cost];
      bestValues = new int[n];
      for (int v = 0; v < n; v++) {
        bestValues[v] = (int) value[v];
      }
    }
  }

  /**
   * Runs the memetic search for at least the given number of steps (whole walks), or until stop
   * answers true: a population of assignments improved by tabu walks, each new one the uniform
   * crossover of two parents picked by binary tournament, mutated and improved by a walk, which
   * replaces the worst of the population when it is better and new.
   *
   * @param maxSteps the steps
   * @param stop asked between steps
   * @return the best cost found so far
   */
  public long run(long maxSteps, BooleanSupplier stop) {
    int nd = decisions.length;
    if (nd == 0) {
      return best;
    }
    if (population == null) {
      population = new int[populationSize][];
      populationCost = new long[populationSize];
    }
    long end = steps + maxSteps;
    while (steps < end && !stop.getAsBoolean()) {
      long[] vs = new long[n];
      if (members < populationSize) {
        for (int d = 0; d < nd; d++) {
          vs[decisions[d]] = choices[d][random.nextInt(choices[d].length)];
        }
      } else {
        int[] a = population[tournament()];
        int[] b = population[tournament()];
        for (int d = 0; d < nd; d++) {
          int x = random.nextBoolean() ? a[d] : b[d];
          if (random.nextInt(nd) == 0) {
            x = choices[d][random.nextInt(choices[d].length)];
          }
          vs[decisions[d]] = x;
        }
      }
      if (!assign(vs)) {
        if (members == 0) {
          // no assignment of the population yet: walk from the current one
          assign(value.clone());
        } else {
          continue;
        }
      }
      if (!walk(stop)) {
        return best;
      }
      insert(walkValues, walkBest);
    }
    return best;
  }

  /**
   * Runs tabu walks from the current assignment for at least the given number of steps (whole
   * walks), or until stop answers true; each walk after the first starts from the best assignment
   * with a random number of variables changed at random.
   *
   * @param maxSteps the steps
   * @param stop asked between steps
   * @return the best cost found so far
   */
  public long improve(long maxSteps, BooleanSupplier stop) {
    int nd = decisions.length;
    if (nd == 0) {
      return best;
    }
    long end = steps + maxSteps;
    while (steps < end && !stop.getAsBoolean()) {
      if (!walk(stop)) {
        return best;
      }
      long[] vs = new long[n];
      for (int d = 0; d < nd; d++) {
        vs[decisions[d]] = bestValues[decisions[d]];
      }
      int flips = 1 + random.nextInt(Math.max(1, nd / 4));
      for (int k = 0; k < flips; k++) {
        int d = random.nextInt(nd);
        vs[decisions[d]] = choices[d][random.nextInt(choices[d].length)];
      }
      if (!assign(vs)) {
        assign(longs(bestValues));
      }
    }
    return best;
  }

  private static long[] longs(int[] xs) {
    long[] ys = new long[xs.length];
    for (int k = 0; k < xs.length; k++) {
      ys[k] = xs[k];
    }
    return ys;
  }

  // the better of two members picked at random
  private int tournament() {
    int a = random.nextInt(members);
    int b = random.nextInt(members);
    return populationCost[a] <= populationCost[b] ? a : b;
  }

  // adds the decision values of an assignment to the population, in place of the worst member
  private void insert(int[] decisionValues, long c) {
    for (int k = 0; k < members; k++) {
      if (populationCost[k] == c && Arrays.equals(population[k], decisionValues)) {
        return;
      }
    }
    if (members < populationSize) {
      population[members] = decisionValues.clone();
      populationCost[members++] = c;
      return;
    }
    int worst = 0;
    for (int k = 1; k < members; k++) {
      if (populationCost[k] > populationCost[worst]) {
        worst = k;
      }
    }
    if (c < populationCost[worst]) {
      population[worst] = decisionValues.clone();
      populationCost[worst] = c;
    }
  }

  /**
   * One tabu walk from the current assignment, of a random length between half and one and a half
   * times the number of decision variables; walkBest and walkValues keep its best assignment.
   *
   * @return false when stop answered true
   */
  private boolean walk(BooleanSupplier stop) {
    int nd = decisions.length;
    walks++;
    long walkSteps = nd / 2 + random.nextInt(nd + 1) + 1;
    int minTenure = Math.max(1, (int) (walkSteps / 10));
    int extraTenure = Math.max(1, (int) (walkSteps / 50));
    Arrays.fill(tabu, 0);
    walkBest = value[cost];
    copyDecisions(walkValues);
    for (long step = 0; step < walkSteps; step++) {
      if ((steps & 15) == 0 && stop.getAsBoolean()) {
        return false;
      }
      steps++;
      long chosen = Long.MAX_VALUE;
      int ties = 0;
      for (int d = 0; d < nd; d++) {
        int v = decisions[d];
        boolean isTabu = tabu[d] > steps;
        for (int c : choices[d]) {
          if (c == value[v]) {
            continue;
          }
          long after = evaluate(v, c);
          if (after == Long.MAX_VALUE || (isTabu && after >= walkBest)) {
            continue;
          }
          if (after < chosen) {
            chosen = after;
            ties = 0;
          }
          if (after == chosen && ties < moveVar.length) {
            moveVar[ties] = d;
            moveValue[ties] = c;
            ties++;
          }
        }
      }
      if (ties == 0) {
        break;
      }
      int pick = random.nextInt(ties);
      int d = moveVar[pick];
      evaluate(decisions[d], moveValue[pick]);
      commit();
      tabu[d] = steps + minTenure + random.nextInt(extraTenure + 1);
      if (verify) {
        check();
      }
      if (value[cost] < walkBest) {
        walkBest = value[cost];
        copyDecisions(walkValues);
      }
      record();
    }
    return true;
  }

  /** Checks after every move that the values kept equal the values of the definitions. */
  void setVerify(boolean on) {
    verify = on;
  }

  private void check() {
    long[] vs = value.clone();
    for (int v : order) {
      if (defKind[v] != DECISION) {
        vs[v] = define(v, u -> (int) vs[u], vs);
      }
      if (kind[v] != INLINED && vs[v] != value[v]) {
        throw new IllegalStateException("variable " + v + " is " + value[v] + ", defined " + vs[v]);
      }
      if (!inDomain(v, vs[v])) {
        throw new IllegalStateException("variable " + v + " = " + vs[v] + " outside its domain");
      }
    }
  }

  private void copyDecisions(int[] into) {
    for (int d = 0; d < decisions.length; d++) {
      into[d] = (int) value[decisions[d]];
    }
  }
}
