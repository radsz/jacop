/*
 * PermutationFlowShop.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SplittableRandom;
import java.util.TreeSet;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;

/**
 * The iterated greedy search of Ruiz and Stützle (Eur. J. Oper. Res. 177(3), 2007) for a
 * permutation flow shop found in a model: an all different over n position variables {@code x[k]}
 * that is a permutation of the jobs, tables with the position as key that give the processing time
 * {@code d[i,k] = p[i, x[k]]} of each machine, and precedences {@code s[i,k] + d[i,k] <= s[i,k+1]}
 * and {@code s[i,k] + d[i,k] <= s[i+1,k]} between the operation starts that order the positions and
 * the machines. The sequence starts from the NEH insertion order (Nawaz, Enscore and Ham, Omega
 * 11(1), 1983); each iteration removes a few jobs, puts each back where it gives the smallest
 * makespan, improves the sequence by reinsertions, and keeps it by a simulated annealing criterion.
 * The makespans of all insertion points of a job are computed together in O(nm) by the heads and
 * tails of Taillard (Eur. J. Oper. Res. 47(1), 1990).
 *
 * <p>The model may hold more than this: every better sequence is given to the store, which fixes
 * the positions and checks the other constraints, and the search gives up when the store's cost is
 * not the makespan of the sequence.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class PermutationFlowShop {

  /** It is told of each better sequence and asked whether to go on. */
  interface Listener {

    /**
     * A sequence better than every one before it.
     *
     * @param sequence the job of each position.
     * @param makespan its makespan.
     * @return false when the search should give up (the store rejects the sequences, or its cost is
     *     not the makespan).
     */
    boolean report(int[] sequence, int makespan);

    /**
     * Whether the search should stop now.
     *
     * @return true to stop.
     */
    boolean stop();
  }

  final int n;
  final int m;
  // p[i][j]: the time of job j on the i-th machine
  final int[][] p;
  // the position variables in sequence order, and the value of each job
  final IntVar[] position;
  final int[] value;

  private final SplittableRandom random;

  private long iterations;

  // whether the listener asked to stop: it answers true once, not on every later call
  private boolean stopped;

  // the heads, tails and insertion heads of Taillard's acceleration
  private final int[][] e;
  private final int[][] q;

  private PermutationFlowShop(int[][] p, IntVar[] position, int[] value, SplittableRandom random) {
    this.p = p;
    this.m = p.length;
    this.n = p[0].length;
    this.position = position;
    this.value = value;
    this.random = random;
    e = new int[m][n + 1];
    q = new int[m][n + 2];
  }

  /**
   * The number of iterations run.
   *
   * @return the iterations.
   */
  long iterations() {
    return iterations;
  }

  // ----------------------------------------------------------------- detection

  // a table column that is a function of the key: the value for each job
  private record Column(IntVar var, List<Integer> values) {}

  // an operation: machine (array) and position
  private record Op(int machine, IntVar position) {}

  /**
   * Finds a permutation flow shop among the constraints (see the class comment).
   *
   * @param constraints the constraints of the model.
   * @param random the generator of the search.
   * @return the flow shop, or null when the constraints hold none.
   */
  static PermutationFlowShop detect(Collection<Constraint> constraints, SplittableRandom random) {
    Map<IntVar, List<HybridTable>> keyed = new IdentityHashMap<>();
    List<Set<Var>> alldiffs = new ArrayList<>();
    for (Constraint c : constraints) {
      if (c instanceof HybridTable t && t.columnCount() >= 2) {
        for (int k = 0; k < t.columnCount(); k++) {
          keyed.computeIfAbsent(t.column(k), v -> new ArrayList<>(1)).add(t);
        }
      } else if (c instanceof Alldistinct || c instanceof Alldifferent) {
        alldiffs.add(c.arguments());
      }
    }
    for (Set<Var> a : alldiffs) {
      PermutationFlowShop fs = detect(a, keyed, constraints, random);
      if (fs != null) {
        return fs;
      }
    }
    return null;
  }

  private static PermutationFlowShop detect(
      Set<Var> alldiff,
      Map<IntVar, List<HybridTable>> keyed,
      Collection<Constraint> constraints,
      SplittableRandom random) {
    int n = alldiff.size();
    if (n < 3) {
      return null;
    }
    List<IntVar> x = new ArrayList<>(n);
    TreeSet<Integer> union = new TreeSet<>();
    for (Var v : alldiff) {
      if (!(v instanceof IntVar xv) || !keyed.containsKey(xv) || xv.getSize() > n) {
        return null;
      }
      x.add(xv);
      for (ValueEnumeration en = xv.dom().valueEnumeration(); en.hasMoreElements(); ) {
        union.add(en.nextElement());
      }
    }
    if (union.size() != n) {
      return null;
    }
    int[] value = union.stream().mapToInt(Integer::intValue).toArray();
    // the columns of each position, by their values over the jobs
    Map<List<Integer>, Integer> arrayOf = new HashMap<>();
    List<List<Integer>> arrays = new ArrayList<>();
    List<Map<Integer, IntVar>> columns = new ArrayList<>();
    for (IntVar xv : x) {
      Map<Integer, IntVar> own = new HashMap<>();
      for (HybridTable t : keyed.get(xv)) {
        int key = -1;
        for (int c = 0; c < t.columnCount(); c++) {
          if (t.column(c) == xv) {
            key = c;
          }
        }
        // the tuple of each job: the other columns are functions of the position
        int[][] tuples = t.validPlainTuples();
        if (tuples == null) {
          continue;
        }
        Map<Integer, int[]> tupleOf = new HashMap<>();
        boolean function = true;
        for (int[] tuple : tuples) {
          function &= tupleOf.put(tuple[key], tuple) == null;
        }
        if (!function) {
          continue;
        }
        for (int c = 0; c < t.columnCount(); c++) {
          IntVar y = t.column(c);
          if (c == key || y == xv) {
            continue;
          }
          List<Integer> vs = new ArrayList<>(n);
          for (int v : value) {
            int[] tuple = tupleOf.get(v);
            if (tuple == null || tuple[c] < 0) {
              vs = null;
              break;
            }
            vs.add(tuple[c]);
          }
          if (vs == null) {
            continue;
          }
          Integer id = arrayOf.get(vs);
          if (id == null) {
            id = arrays.size();
            arrayOf.put(vs, id);
            arrays.add(vs);
          }
          own.putIfAbsent(id, y);
        }
      }
      columns.add(own);
    }
    // the machines: the arrays every position has
    List<Integer> machines = new ArrayList<>();
    for (int id = 0; id < arrays.size(); id++) {
      int a = id;
      if (columns.stream().allMatch(c -> c.containsKey(a))) {
        machines.add(id);
      }
    }
    int m = machines.size();
    if (m < 2) {
      return null;
    }
    // the operation of each duration variable
    Map<IntVar, Op> opOfDuration = new IdentityHashMap<>();
    for (int k = 0; k < n; k++) {
      for (int r = 0; r < m; r++) {
        if (opOfDuration.put(columns.get(k).get(machines.get(r)), new Op(r, x.get(k))) != null) {
          // one variable is the time of two operations
          return null;
        }
      }
    }
    // the precedences s + d <= t: the start of each operation and its successors
    Map<IntVar, IntVar> startOf = new IdentityHashMap<>();
    List<IntVar[]> rows = new ArrayList<>();
    for (Constraint c : constraints) {
      IntVar[] row = precedence(c, opOfDuration);
      if (row == null) {
        continue;
      }
      if (row[0] != null) {
        IntVar s = startOf.putIfAbsent(row[1], row[0]);
        if (s != null && s != row[0]) {
          return null;
        }
      }
      rows.add(row);
    }
    // the first operation may start at the constant 0 and have no start variable, and the last
    // one may have no successor (its end is the makespan)
    if (startOf.size() < opOfDuration.size() - 2) {
      return null;
    }
    Map<IntVar, IntVar> durationOfStart = new IdentityHashMap<>();
    for (Map.Entry<IntVar, IntVar> en : startOf.entrySet()) {
      if (durationOfStart.put(en.getValue(), en.getKey()) != null) {
        return null;
      }
    }
    int[] nextMachine = new int[m];
    Arrays.fill(nextMachine, -1);
    Map<IntVar, IntVar> nextPosition = new IdentityHashMap<>();
    for (IntVar[] row : rows) {
      IntVar d = durationOfStart.get(row[2]);
      if (d == null) {
        continue;
      }
      Op from = opOfDuration.get(row[1]);
      Op to = opOfDuration.get(d);
      if (from.position == to.position && from.machine != to.machine) {
        if (nextMachine[from.machine] >= 0 && nextMachine[from.machine] != to.machine) {
          return null;
        }
        nextMachine[from.machine] = to.machine;
      } else if (from.machine == to.machine && from.position != to.position) {
        IntVar was = nextPosition.put(from.position, to.position);
        if (was != null && was != to.position) {
          return null;
        }
      }
    }
    int[] machineOrder = chain(nextMachine);
    if (machineOrder == null) {
      return null;
    }
    // the positions in sequence order
    Map<IntVar, Integer> posIndex = new IdentityHashMap<>();
    for (int k = 0; k < n; k++) {
      posIndex.put(x.get(k), k);
    }
    int[] nextPos = new int[n];
    Arrays.fill(nextPos, -1);
    for (Map.Entry<IntVar, IntVar> en : nextPosition.entrySet()) {
      nextPos[posIndex.get(en.getKey())] = posIndex.get(en.getValue());
    }
    int[] positionOrder = chain(nextPos);
    if (positionOrder == null) {
      return null;
    }
    int[][] p = new int[m][n];
    for (int i = 0; i < m; i++) {
      List<Integer> a = arrays.get(machines.get(machineOrder[i]));
      for (int j = 0; j < n; j++) {
        p[i][j] = a.get(j);
      }
    }
    IntVar[] position = new IntVar[n];
    for (int k = 0; k < n; k++) {
      position[k] = x.get(positionOrder[k]);
    }
    return new PermutationFlowShop(p, position, value, random);
  }

  // the elements of a successor function that visits all of them from the one without a
  // predecessor; null when it is not one chain
  private static int[] chain(int[] next) {
    int size = next.length;
    boolean[] hasPred = new boolean[size];
    for (int a : next) {
      if (a >= 0) {
        if (hasPred[a]) {
          return null;
        }
        hasPred[a] = true;
      }
    }
    int first = -1;
    for (int a = 0; a < size; a++) {
      if (!hasPred[a]) {
        if (first >= 0) {
          return null;
        }
        first = a;
      }
    }
    if (first < 0) {
      return null;
    }
    int[] order = new int[size];
    int a = first;
    for (int k = 0; k < size; k++) {
      if (a < 0) {
        return null;
      }
      order[k] = a;
      a = next[a];
    }
    return a < 0 ? order : null;
  }

  // a row s + d <= t with d a duration: {s, d, t}, s null when the start is the constant 0
  // (d <= t); null otherwise
  private static IntVar[] precedence(Constraint c, Map<IntVar, Op> durations) {
    LinearForm f = LinearForms.of(c);
    if (f == null || f.vars().length < 2 || f.vars().length > 3) {
      return null;
    }
    long sign;
    if (f.relation() == LinearForm.LE) {
      sign = 1;
    } else if (f.relation() == LinearForm.GE) {
      sign = -1;
    } else {
      return null;
    }
    if (f.c() * sign != 0) {
      return null;
    }
    IntVar d = null;
    IntVar s = null;
    IntVar t = null;
    for (int k = 0; k < f.vars().length; k++) {
      long w = f.weights()[k] * sign;
      IntVar v = f.vars()[k];
      if (w == -1 && t == null) {
        t = v;
      } else if (w == 1 && d == null && durations.containsKey(v)) {
        d = v;
      } else if (w == 1 && s == null) {
        s = v;
      } else {
        return null;
      }
    }
    if (d == null || t == null || (s == null && f.vars().length == 3)) {
      return null;
    }
    return new IntVar[] {s, d, t};
  }

  // ------------------------------------------------------------------- search

  /**
   * Runs the iterated greedy search until the listener stops it or gives up.
   *
   * @param listener told of each better sequence.
   * @return true when stopped, false when the listener gave up.
   */
  boolean run(Listener listener) {
    int[] current = neh();
    int currentSpan = makespan(current, n);
    int[] best = current.clone();
    int bestSpan = currentSpan;
    if (!listener.report(best, bestSpan)) {
      return false;
    }
    long total = 0;
    for (int[] row : p) {
      for (int t : row) {
        total += t;
      }
    }
    // Ruiz and Stützle: T = 0.4, d = 4
    double temperature = 0.4 * total / (10.0 * n * m);
    int destroyed = Math.min(4, n - 1);
    int[] work = new int[n];
    int[] removed = new int[destroyed];
    int bound = lowerBound();
    // small flow shops stop after this many iterations without a better sequence, long before the
    // patience of the search; large ones do far fewer iterations in their time
    long stagnation = 1000L * n * m;
    long lastBest = 0;
    while (bestSpan > bound && iterations - lastBest < stagnation && !stopped(listener)) {
      iterations++;
      System.arraycopy(current, 0, work, 0, n);
      int len = n;
      for (int r = 0; r < destroyed; r++) {
        int at = random.nextInt(len);
        removed[r] = work[at];
        System.arraycopy(work, at + 1, work, at, len - at - 1);
        len--;
      }
      for (int r = 0; r < destroyed; r++) {
        insertBest(work, len, removed[r]);
        len++;
      }
      int span = localSearch(work, listener);
      if (span < currentSpan) {
        System.arraycopy(work, 0, current, 0, n);
        currentSpan = span;
        if (span < bestSpan) {
          bestSpan = span;
          lastBest = iterations;
          System.arraycopy(work, 0, best, 0, n);
          if (!listener.report(best, bestSpan)) {
            return false;
          }
        }
      } else if (random.nextDouble() < Math.exp(-(span - currentSpan) / temperature)) {
        System.arraycopy(work, 0, current, 0, n);
        currentSpan = span;
      }
    }
    return true;
  }

  // the largest machine load with the shortest head before and tail after the machine, and the
  // longest job: no sequence is shorter (Taillard 1993)
  int lowerBound() {
    long bound = 0;
    for (int j = 0; j < n; j++) {
      long job = 0;
      for (int i = 0; i < m; i++) {
        job += p[i][j];
      }
      bound = Math.max(bound, job);
    }
    for (int i = 0; i < m; i++) {
      long load = 0;
      long head = Long.MAX_VALUE;
      long tail = Long.MAX_VALUE;
      for (int j = 0; j < n; j++) {
        load += p[i][j];
        long h = 0;
        long t = 0;
        for (int k = 0; k < i; k++) {
          h += p[k][j];
        }
        for (int k = i + 1; k < m; k++) {
          t += p[k][j];
        }
        head = Math.min(head, h);
        tail = Math.min(tail, t);
      }
      bound = Math.max(bound, load + head + tail);
    }
    return (int) Math.min(bound, Integer.MAX_VALUE);
  }

  private boolean stopped(Listener listener) {
    if (!stopped) {
      stopped = listener.stop();
    }
    return stopped;
  }

  // NEH: jobs by decreasing total time, each inserted where the partial makespan is smallest
  int[] neh() {
    Integer[] jobs = new Integer[n];
    long[] sum = new long[n];
    for (int j = 0; j < n; j++) {
      jobs[j] = j;
      for (int i = 0; i < m; i++) {
        sum[j] += p[i][j];
      }
    }
    Arrays.sort(jobs, (a, b) -> sum[a] != sum[b] ? Long.compare(sum[b], sum[a]) : a - b);
    int[] seq = new int[n];
    for (int len = 0; len < n; len++) {
      insertBest(seq, len, jobs[len]);
    }
    return seq;
  }

  // reinsertion of every job, in a random order, at its best place, until none improves
  private int localSearch(int[] seq, Listener listener) {
    int span = makespan(seq, n);
    int[] order = new int[n];
    boolean improved = true;
    while (improved && !stopped(listener)) {
      improved = false;
      System.arraycopy(seq, 0, order, 0, n);
      for (int k = n - 1; k > 0; k--) {
        int r = random.nextInt(k + 1);
        int t = order[k];
        order[k] = order[r];
        order[r] = t;
      }
      for (int job : order) {
        int at = 0;
        while (seq[at] != job) {
          at++;
        }
        System.arraycopy(seq, at + 1, seq, at, n - at - 1);
        int s = insertBest(seq, n - 1, job);
        if (s < span) {
          span = s;
          improved = true;
        }
      }
    }
    return span;
  }

  /**
   * Inserts a job into the first len jobs of seq where the makespan is smallest (the first such
   * place), with Taillard's heads and tails.
   *
   * @return the makespan of the len + 1 jobs.
   */
  int insertBest(int[] seq, int len, int job) {
    // heads: e[i][k] the completion of the k-th job (from 1) on machine i
    for (int k = 1; k <= len; k++) {
      int j = seq[k - 1];
      int above = 0;
      for (int i = 0; i < m; i++) {
        int c = Math.max(above, e[i][k - 1]) + p[i][j];
        e[i][k] = c;
        above = c;
      }
    }
    // tails: q[i][k] the time from the start of the k-th job (from 1) on machine i to the end
    for (int i = 0; i < m; i++) {
      q[i][len + 1] = 0;
    }
    for (int k = len; k >= 1; k--) {
      int j = seq[k - 1];
      int below = 0;
      for (int i = m - 1; i >= 0; i--) {
        int c = Math.max(below, q[i][k + 1]) + p[i][j];
        q[i][k] = c;
        below = c;
      }
    }
    int bestAt = 0;
    int bestSpan = Integer.MAX_VALUE;
    for (int at = 0; at <= len; at++) {
      // the job after the first at jobs
      int above = 0;
      int span = 0;
      for (int i = 0; i < m; i++) {
        int c = Math.max(above, e[i][at]) + p[i][job];
        above = c;
        span = Math.max(span, c + q[i][at + 1]);
      }
      if (span < bestSpan) {
        bestSpan = span;
        bestAt = at;
      }
    }
    System.arraycopy(seq, bestAt, seq, bestAt + 1, len - bestAt);
    seq[bestAt] = job;
    return bestSpan;
  }

  /**
   * The makespan of the first len jobs of a sequence.
   *
   * @param seq the jobs.
   * @param len how many.
   * @return the makespan.
   */
  int makespan(int[] seq, int len) {
    int[] c = new int[m];
    for (int k = 0; k < len; k++) {
      int j = seq[k];
      int above = 0;
      for (int i = 0; i < m; i++) {
        above = Math.max(above, c[i]) + p[i][j];
        c[i] = above;
      }
    }
    return c[m - 1];
  }
}
