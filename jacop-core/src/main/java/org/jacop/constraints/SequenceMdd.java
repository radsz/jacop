/*
 * SequenceMdd.java
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
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * A relaxed multivalued decision diagram over the order in which a circuit visits its nodes, with
 * times along the arcs: a redundant constraint for routing and sequencing with time windows.
 *
 * <p>The circuit is given by its successor variables ({@code arcs[i] = offset + j} for the arc i to
 * j) or by its predecessor variables ({@code arcs[j] = offset + i} for the same arc). Each node j
 * has an arrival time {@code in[j]} and a departure time {@code out[j]}; the circuit's arc i to j
 * implies {@code in[j] >= out[i] + travel[i][j]}, and each node but the start {@code out[j] >=
 * in[j] + delta[j]}. {@link #NONE} as a travel time or a delta says the model links the two times
 * by nothing (a depot left at time 0, the arc from one vehicle's end to the next vehicle's start).
 * The time windows are the current bounds of the time variables, read at each call.
 *
 * <p>Each call compiles the diagram top-down from {@code start}, one layer per position, as Cire
 * and van Hoeve (Multivalued Decision Diagrams for Sequencing Problems, Operations Research
 * 61(6):1411-1428, 2013): a diagram node keeps the nodes visited on every path into it ({@code
 * all}) and on some path ({@code some}), and for each last node the earliest departure over the
 * paths into it. Nodes with the same {@code all} are merged without loss; when a layer has more
 * than {@code width} nodes, the nodes with the latest earliest departures are merged into one.
 * Since the diagram keeps every real circuit as a path with times no later than the real ones, it
 * removes successor values on no path from the start to the closing arc, and sets the minimum of
 * each {@code in[j]} and {@code out[j]} to the earliest time over the paths that go through j; the
 * closing arc sets the minimum of {@code in[start]}, which is the return time of a tour from a
 * depot, often the objective.
 *
 * <p>The pruning depends only on the current domains of the variables, so the generic reason of
 * lazy clause generation explains it; circuits of at most {@code -Djacop.sequenceMdd.replayNodes}
 * (32) nodes are explained by replaying the constraint instead.
 *
 * <p>A call allocates nothing: the arcs of the current domains are read into bit masks, each
 * diagram node keeps a mask of the last nodes of its paths, and the nodes of the next layer are
 * found by a Zobrist hash of their visited sets (Zobrist, A new hashing method with application for
 * game playing, Technical Report 88, University of Wisconsin, 1970).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class SequenceMdd extends Constraint
    implements SatisfiedPresent, Copyable<SequenceMdd>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** A travel time or a delta that links no times. */
  public static final int NONE = Integer.MIN_VALUE;

  private static final long INF = Long.MAX_VALUE / 4;

  private static final long NEG = -INF;

  /** The circuit's successor (or predecessor) variables. */
  public final IntVar[] arcs;

  /** True when {@link #arcs} are predecessor variables. */
  public final boolean pred;

  /** The value that stands for node 0. */
  public final int offset;

  /** Arrival time of each node; null for no time. */
  public final IntVar[] in;

  /** Departure time of each node; null for no time. */
  public final IntVar[] out;

  /** Least time from the departure of i to the arrival at j, or {@link #NONE}. */
  public final int[][] travel;

  /** Least time from the arrival at j to its departure, or {@link #NONE}. */
  public final int[] delta;

  /** The node the diagram starts from. */
  public final int start;

  /** The largest number of diagram nodes in a layer. */
  public final int width;

  /** The cost of each arc, or null for no cost. */
  public final int[][] costs;

  /** The cost of the circuit plus {@link #costOffset}, or null. */
  public final IntVar cost;

  /** The constant part of the cost. */
  public final long costOffset;

  /**
   * Time-dependent travel, or null: {@code stepTravel[i][j][s]} is the travel time from i to j when
   * i is left at a time t with {@code t / stepLength == s}; null rows use {@link #travel}.
   */
  public final int[][][] stepTravel;

  /** The length of a step of {@link #stepTravel}. */
  public final int stepLength;

  // stepBest[i][j][s]: the least s' * stepLength + stepTravel[i][j][s'] over s' >= s
  private final long[][][] stepBest;

  private final int n;
  private final int words;

  /** The most calls skipped after calls that pruned nothing ({@code -Djacop.sequenceMdd.skip}). */
  private static final int MAX_SKIP = Integer.getInteger("jacop.sequenceMdd.skip", 63);

  // the largest sort key of a candidate, so that key * candidates + index fits in a long
  private static final long MAX_KEY = 1L << 40;

  /**
   * The largest circuit whose pruning lazy clause generation explains by replaying the constraint
   * ({@code -Djacop.sequenceMdd.replayNodes}, 32 by default); a larger one gives the generic reason
   * at once. Each replay compiles the whole diagram again, which on circuits of 40 to 60 nodes cost
   * more than the shorter reasons saved.
   */
  private static final int REPLAY_NODES = Integer.getInteger("jacop.sequenceMdd.replayNodes", 32);

  private int rootLevel = -1;
  private int skip;
  private int backoff;
  private boolean pruned;

  // layer arrays, allocated at the first call: masks, per-last earliest departures and least costs
  // (INF for the nodes outside lastMask)
  private long[][][] allMask;
  private long[][][] someMask;
  private long[][][] lastMask;
  private long[][] nodeHash;
  private long[][][] time;
  // the least cost of the paths into each (node, last)
  private long[][][] top;
  private int[] count;
  // target[k][u][j]: index in layer k + 1 of the arc from node u of layer k labelled j, or -1
  private int[][][] target;

  // candidates of the next layer, found by the hash of their visited set in an open-addressing
  // table
  private long[][] candAll;
  private long[][] candSome;
  private long[][] candLast;
  private long[] candHash;
  private long[][] candTime;
  private long[][] candTop;
  private int[] candToNode;
  private long[] order;
  private int[] table;
  private int[] tableStamp;
  private int stamp;
  private long[] zobrist;

  // the arcs of the current domains: outMask[i] the successors of i, inMask[j] the predecessors of
  // j
  private long[][] outMask;
  // the bounds of the times at the start of the call
  private long[] loIn;
  private long[] hiIn;
  private long[] loOut;
  private long[] hiOut;
  private long[][] inMask;

  // backward pass
  private long[][] latest;
  private long[][] prev;
  private long[][] bottom;
  private long[][] prevBottom;
  private long[] minIn;
  private long[] minOut;
  private long[] maxIn;
  private long[] maxOut;
  private long[] leave;
  private long[] rest;
  private boolean[] support;

  /**
   * It creates the constraint.
   *
   * @param arcs successor variables, or predecessor variables when pred is true.
   * @param pred whether arcs are predecessor variables.
   * @param offset the value of arcs that stands for node 0.
   * @param in the arrival time of each node, null for none.
   * @param out the departure time of each node, null for none.
   * @param travel travel[i][j], the least time from out[i] to in[j], or NONE.
   * @param delta delta[j], the least time from in[j] to out[j], or NONE.
   * @param start the node the diagram starts from (the depot).
   * @param width the largest number of diagram nodes in a layer, at least 1.
   */
  public SequenceMdd(
      IntVar[] arcs,
      boolean pred,
      int offset,
      IntVar[] in,
      IntVar[] out,
      int[][] travel,
      int[] delta,
      int start,
      int width) {
    this(arcs, pred, offset, in, out, travel, delta, start, width, null, null, 0, null, 0);
  }

  /**
   * It creates the constraint with time-dependent travel: the arc i to j implies {@code in[j] >=
   * out[i] + stepTravel[i][j][out[i] / stepLength]}; i may be left later than its earliest time
   * when that arrives earlier. A departure after the last step uses the least travel time of the
   * arc. A null {@code stepTravel[i][j]} says the model links the two times by nothing.
   *
   * @param arcs successor variables, or predecessor variables when pred is true.
   * @param pred whether arcs are predecessor variables.
   * @param offset the value of arcs that stands for node 0.
   * @param in the arrival time of each node, null for none.
   * @param out the departure time of each node, null for none.
   * @param stepTravel stepTravel[i][j][s], the travel time from i to j when i is left in step s.
   * @param stepLength the length of a step, at least 1.
   * @param delta delta[j], the least time from in[j] to out[j], or NONE.
   * @param start the node the diagram starts from (the depot).
   * @param width the largest number of diagram nodes in a layer, at least 1.
   */
  public SequenceMdd(
      IntVar[] arcs,
      boolean pred,
      int offset,
      IntVar[] in,
      IntVar[] out,
      int[][][] stepTravel,
      int stepLength,
      int[] delta,
      int start,
      int width) {
    this(
        arcs,
        pred,
        offset,
        in,
        out,
        leastTravel(stepTravel, arcs.length),
        delta,
        start,
        width,
        null,
        null,
        0,
        stepTravel,
        stepLength);
  }

  private static int[][] leastTravel(int[][][] stepTravel, int size) {
    if (stepTravel == null || stepTravel.length != size) {
      throw new IllegalArgumentException("SequenceMdd needs a step travel row per node");
    }
    int[][] least = new int[size][size];
    for (int i = 0; i < size; i++) {
      if (stepTravel[i] == null || stepTravel[i].length != size) {
        throw new IllegalArgumentException("SequenceMdd needs " + size + " step travels per row");
      }
      for (int j = 0; j < size; j++) {
        int[] row = stepTravel[i][j];
        int m = NONE;
        if (row != null && row.length > 0) {
          m = Integer.MAX_VALUE;
          for (int v : row) {
            m = Math.min(m, v);
          }
        }
        least[i][j] = m;
      }
    }
    return least;
  }

  /**
   * It creates the constraint with a cost of the circuit: {@code cost = costOffset + sum of
   * costs[i][j]} over its arcs i to j. The diagram then also bounds the cost from below and removes
   * the arcs of no path cheaper than the maximum of the cost.
   *
   * @param arcs successor variables, or predecessor variables when pred is true.
   * @param pred whether arcs are predecessor variables.
   * @param offset the value of arcs that stands for node 0.
   * @param in the arrival time of each node, null for none.
   * @param out the departure time of each node, null for none.
   * @param travel travel[i][j], the least time from out[i] to in[j], or NONE.
   * @param delta delta[j], the least time from in[j] to out[j], or NONE.
   * @param start the node the diagram starts from (the depot).
   * @param width the largest number of diagram nodes in a layer, at least 1.
   * @param costs costs[i][j], the cost of the arc i to j, or null.
   * @param cost the cost of the circuit, or null.
   * @param costOffset the constant part of the cost.
   */
  public SequenceMdd(
      IntVar[] arcs,
      boolean pred,
      int offset,
      IntVar[] in,
      IntVar[] out,
      int[][] travel,
      int[] delta,
      int start,
      int width,
      int[][] costs,
      IntVar cost,
      long costOffset) {
    this(
        arcs, pred, offset, in, out, travel, delta, start, width, costs, cost, costOffset, null, 0);
  }

  private SequenceMdd(
      IntVar[] arcs,
      boolean pred,
      int offset,
      IntVar[] in,
      IntVar[] out,
      int[][] travel,
      int[] delta,
      int start,
      int width,
      int[][] costs,
      IntVar cost,
      long costOffset,
      int[][][] stepTravel,
      int stepLength) {
    checkInputForNullness("arcs", arcs);
    if (in == null || out == null || travel == null || delta == null) {
      throw new IllegalArgumentException("SequenceMdd needs travel times and deltas");
    }
    checkInputForDuplication("arcs", arcs);
    int size = arcs.length;
    if (in.length != size
        || out.length != size
        || travel.length != size
        || delta.length != size
        || start < 0
        || start >= size
        || width < 1) {
      throw new IllegalArgumentException(
          "SequenceMdd needs one time, travel row and delta per node");
    }
    for (int[] row : travel) {
      if (row == null || row.length != size) {
        throw new IllegalArgumentException("SequenceMdd needs " + size + " travel times per row");
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.arcs = Arrays.copyOf(arcs, size);
    this.pred = pred;
    this.offset = offset;
    this.in = Arrays.copyOf(in, size);
    this.out = Arrays.copyOf(out, size);
    this.travel = new int[size][];
    for (int i = 0; i < size; i++) {
      this.travel[i] = Arrays.copyOf(travel[i], size);
    }
    this.delta = Arrays.copyOf(delta, size);
    this.start = start;
    this.width = width;
    if ((costs == null) != (cost == null) || costs != null && costs.length != size) {
      throw new IllegalArgumentException("SequenceMdd needs a cost row per node and a cost");
    }
    if (costs != null) {
      this.costs = new int[size][];
      for (int i = 0; i < size; i++) {
        if (costs[i] == null || costs[i].length != size) {
          throw new IllegalArgumentException("SequenceMdd needs " + size + " costs per row");
        }
        this.costs[i] = Arrays.copyOf(costs[i], size);
      }
    } else {
      this.costs = null;
    }
    this.cost = cost;
    this.costOffset = costOffset;
    if (stepTravel != null && stepLength < 1) {
      throw new IllegalArgumentException("SequenceMdd needs a step length of at least 1");
    }
    this.stepLength = stepLength;
    if (stepTravel != null) {
      this.stepTravel = new int[size][size][];
      this.stepBest = new long[size][size][];
      for (int i = 0; i < size; i++) {
        for (int j = 0; j < size; j++) {
          int[] row = stepTravel[i][j];
          if (row == null) {
            continue;
          }
          this.stepTravel[i][j] = Arrays.copyOf(row, row.length);
          long[] best = new long[row.length + 1];
          best[row.length] = INF;
          for (int k = row.length - 1; k >= 0; k--) {
            best[k] = Math.min(best[k + 1], (long) k * stepLength + row[k]);
          }
          this.stepBest[i][j] = best;
        }
      }
    } else {
      this.stepTravel = null;
      this.stepBest = null;
    }
    this.n = size;
    this.words = (size + 63) >>> 6;
    this.queueIndex = 4;
    Set<Var> scope = new LinkedHashSet<>(Arrays.asList(arcs));
    for (int i = 0; i < size; i++) {
      if (in[i] != null) {
        scope.add(in[i]);
      }
      if (out[i] != null) {
        scope.add(out[i]);
      }
    }
    if (cost != null) {
      scope.add(cost);
    }
    setScope(scope);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    Integer event = getConsistencyPruningEventFromMap(v);
    if (event != null) {
      return event;
    }
    for (IntVar x : arcs) {
      if (x == v) {
        return IntDomain.ANY;
      }
    }
    return IntDomain.BOUND;
  }

  // whether the circuit may use the arc i -> j
  private boolean arc(int i, int j) {
    return pred ? arcs[j].domain.contains(offset + i) : arcs[i].domain.contains(offset + j);
  }

  private static long lo(IntVar v) {
    return v == null ? NEG : v.min();
  }

  private static long hi(IntVar v) {
    return v == null ? INF : v.max();
  }

  // the earliest arrival at j after leaving i at t, or INF when the window of j is missed
  private long arrival(int i, int j, long t) {
    long a = loIn[j];
    int d = travel[i][j];
    if (d != NONE && t > NEG) {
      a =
          Math.max(
              a, stepTravel == null || stepTravel[i][j] == null ? t + d : stepArrival(i, j, t));
    }
    return a > hiIn[j] ? INF : a;
  }

  // the travel time from i to j when i is left at t
  private long travelAt(int i, int j, long t) {
    int[] row = stepTravel == null ? null : stepTravel[i][j];
    if (row == null) {
      return travel[i][j];
    }
    long s = t < 0 ? 0 : t / stepLength;
    return s < row.length ? row[(int) s] : travel[i][j];
  }

  // the earliest arrival at j over the departures from i at t or later, up to the latest one
  private long stepArrival(int i, int j, long t) {
    int[] row = stepTravel[i][j];
    long[] best = stepBest[i][j];
    long latest = hiOut[i];
    long a = t + travelAt(i, j, t);
    long s = t < 0 ? 0 : t / stepLength + 1;
    for (; s < row.length && s * stepLength <= latest && best[(int) s] < a; s++) {
      a = Math.min(a, s * stepLength + row[(int) s]);
    }
    long beyond = (long) row.length * stepLength;
    if (beyond > t && beyond <= latest) {
      a = Math.min(a, beyond + travel[i][j]);
    }
    return a;
  }

  // the latest departure from i, at most the latest one, that arrives at j by x, or NEG when none
  private long stepLatest(int i, int j, long x) {
    int[] row = stepTravel[i][j];
    long latest = hiOut[i];
    long beyond = (long) row.length * stepLength;
    long d0 = Math.min(x - travel[i][j], latest);
    if (d0 >= beyond) {
      return d0;
    }
    for (int s = row.length - 1; s >= 0; s--) {
      long first = (long) s * stepLength;
      long d = Math.min(Math.min(first + stepLength - 1, x - row[s]), latest);
      if (d >= first) {
        return d;
      }
    }
    return NEG;
  }

  // the earliest departure from j after arriving at a, or INF when the window of j is missed
  private long departure(int j, long a) {
    long t = loOut[j];
    if (delta[j] != NONE && a > NEG) {
      t = Math.max(t, a + delta[j]);
    }
    return t > hiOut[j] ? INF : t;
  }

  private long arcCost(int i, int j) {
    return costs == null ? 0 : costs[i][j];
  }

  private void allocate() {
    allMask = new long[n][width][words];
    someMask = new long[n][width][words];
    lastMask = new long[n][width][words];
    nodeHash = new long[n][width];
    time = new long[n][width][n];
    top = new long[n][width][n];
    for (int k = 0; k < n; k++) {
      for (int u = 0; u < width; u++) {
        Arrays.fill(time[k][u], INF);
        Arrays.fill(top[k][u], INF);
      }
    }
    count = new int[n];
    target = new int[n][width][n];
    int cands = width * n;
    candAll = new long[cands][words];
    candSome = new long[cands][words];
    candLast = new long[cands][words];
    candHash = new long[cands];
    candTime = new long[cands][n];
    candTop = new long[cands][n];
    for (int c = 0; c < cands; c++) {
      Arrays.fill(candTime[c], INF);
      Arrays.fill(candTop[c], INF);
    }
    candToNode = new int[cands];
    order = new long[cands];
    int size = Integer.highestOneBit(Math.max(2 * cands - 1, 1)) << 1;
    table = new int[size];
    tableStamp = new int[size];
    zobrist = new long[n];
    long z = 0x9E3779B97F4A7C15L;
    for (int j = 0; j < n; j++) {
      z += 0x9E3779B97F4A7C15L;
      zobrist[j] = mix(z);
    }
    loIn = new long[n];
    hiIn = new long[n];
    loOut = new long[n];
    hiOut = new long[n];
    outMask = new long[n][words];
    inMask = new long[n][words];
    latest = new long[width][n];
    prev = new long[width][n];
    bottom = new long[width][n];
    prevBottom = new long[width][n];
    minIn = new long[n];
    minOut = new long[n];
    maxIn = new long[n];
    maxOut = new long[n];
    leave = new long[n];
    rest = new long[n];
    support = new boolean[n * n];
  }

  // a 64-bit finaliser (Stafford's variant 13 of the MurmurHash3 mixer)
  private static long mix(long z) {
    z = (z ^ (z >>> 30)) * 0xBF58476D1CE4E5B9L;
    z = (z ^ (z >>> 27)) * 0x94D049BB133111EBL;
    return z ^ (z >>> 31);
  }

  // the arcs the circuit may use now, as masks of successors and of predecessors
  private void arcMasks() {
    for (int j = 0; j < n; j++) {
      loIn[j] = lo(in[j]);
      hiIn[j] = hi(in[j]);
      loOut[j] = lo(out[j]);
      hiOut[j] = hi(out[j]);
    }
    for (int i = 0; i < n; i++) {
      Arrays.fill(outMask[i], 0L);
      Arrays.fill(inMask[i], 0L);
    }
    for (int x = 0; x < n; x++) {
      IntDomain d = arcs[x].domain;
      for (int y = 0; y < n; y++) {
        if (d.contains(offset + y)) {
          int i = pred ? y : x;
          int j = pred ? x : y;
          set(outMask[i], j);
          set(inMask[j], i);
        }
      }
    }
  }

  // clears the last nodes of a diagram node, so that its times and costs are all INF
  private void clearNode(int k, int u) {
    long[] lm = lastMask[k][u];
    long[] t = time[k][u];
    long[] p = top[k][u];
    for (int w = 0; w < words; w++) {
      for (long bits = lm[w]; bits != 0; bits &= bits - 1) {
        int i = (w << 6) + Long.numberOfTrailingZeros(bits);
        t[i] = INF;
        p[i] = INF;
      }
      lm[w] = 0L;
    }
  }

  @Override
  public void consistency(Store store) {
    if (n < 2) {
      return;
    }
    if (rootLevel < 0) {
      rootLevel = store.level;
    }
    // a call that pruned nothing makes the next ones skip, 1, 3, 7, ... up to MAX_SKIP calls; the
    // constraint is redundant, so a skipped call only delays its pruning to a later call
    if (store.level > rootLevel && skip > 0 && !groundArcs()) {
      skip--;
      return;
    }
    if (allMask == null) {
      allocate();
    }
    arcMasks();
    // layer 0: the start
    count[0] = 1;
    clearNode(0, 0);
    Arrays.fill(allMask[0][0], 0L);
    Arrays.fill(someMask[0][0], 0L);
    set(allMask[0][0], start);
    set(someMask[0][0], start);
    long t0 = loOut[start];
    if (t0 > hiOut[start]) {
      throw Store.failException;
    }
    set(lastMask[0][0], start);
    time[0][0][start] = t0;
    top[0][0][start] = 0;
    nodeHash[0][0] = zobrist[start];

    int startWord = start >>> 6;
    long startBit = 1L << start;
    for (int k = 0; k + 1 < n; k++) {
      if (++stamp == 0) {
        Arrays.fill(tableStamp, 0);
        stamp = 1;
      }
      int cands = 0;
      for (int u = 0; u < count[k]; u++) {
        int[] tgt = target[k][u];
        Arrays.fill(tgt, -1);
        long[] all = allMask[k][u];
        long[] some = someMask[k][u];
        long[] lm = lastMask[k][u];
        boolean full = bitCount(some) == k + 1;
        long h = nodeHash[k][u];
        long[] tu = time[k][u];
        long[] cu = top[k][u];
        for (int wi = 0; wi < words; wi++) {
          for (long lastBits = lm[wi]; lastBits != 0; lastBits &= lastBits - 1) {
            int i = (wi << 6) + Long.numberOfTrailingZeros(lastBits);
            long t = tu[i];
            long[] om = outMask[i];
            for (int wj = 0; wj < words; wj++) {
              long next = om[wj] & ~all[wj];
              if (full) {
                next &= ~some[wj];
              }
              if (wj == startWord) {
                next &= ~startBit;
              }
              for (; next != 0; next &= next - 1) {
                int j = (wj << 6) + Long.numberOfTrailingZeros(next);
                long a = arrival(i, j, t);
                if (a == INF) {
                  continue;
                }
                long d = departure(j, a);
                if (d == INF) {
                  continue;
                }
                int c = tgt[j];
                if (c < 0) {
                  c = candidate(h ^ zobrist[j], all, some, j, cands);
                  if (c == cands) {
                    cands++;
                  }
                  tgt[j] = c;
                }
                long[] ct = candTime[c];
                if (d < ct[j]) {
                  if (ct[j] == INF) {
                    set(candLast[c], j);
                  }
                  ct[j] = d;
                }
                long nc = cu[i] + arcCost(i, j);
                if (nc < candTop[c][j]) {
                  candTop[c][j] = nc;
                }
              }
            }
          }
        }
      }
      if (cands == 0) {
        throw Store.failException;
      }
      select(k + 1, cands);
      for (int u = 0; u < count[k]; u++) {
        int[] tgt = target[k][u];
        for (int j = 0; j < n; j++) {
          if (tgt[j] >= 0) {
            tgt[j] = candToNode[tgt[j]];
          }
        }
      }
    }
    pruned = false;
    prune(store);
    backoff = pruned ? 0 : Math.min(2 * backoff + 1, MAX_SKIP);
    skip = backoff;
  }

  // the candidate with the visited set all + j, found in the table of the layer or added as number
  // fresh; the some set of an existing one is extended by some + j
  private int candidate(long hash, long[] all, long[] some, int j, int fresh) {
    int mask = table.length - 1;
    int jw = j >>> 6;
    long jb = 1L << j;
    for (int s = (int) mix(hash) & mask; ; s = (s + 1) & mask) {
      if (tableStamp[s] != stamp) {
        tableStamp[s] = stamp;
        table[s] = fresh;
        long[] na = candAll[fresh];
        long[] ns = candSome[fresh];
        System.arraycopy(all, 0, na, 0, words);
        System.arraycopy(some, 0, ns, 0, words);
        na[jw] |= jb;
        ns[jw] |= jb;
        candHash[fresh] = hash;
        return fresh;
      }
      int c = table[s];
      if (candHash[c] == hash && sameWith(candAll[c], all, jw, jb)) {
        orInto(candSome[c], some);
        candSome[c][jw] |= jb;
        return c;
      }
    }
  }

  // whether mask equals all with the bit jb of word jw set
  private boolean sameWith(long[] mask, long[] all, int jw, long jb) {
    for (int w = 0; w < words; w++) {
      if (mask[w] != (w == jw ? all[w] | jb : all[w])) {
        return false;
      }
    }
    return true;
  }

  // copies the candidates of layer k into its nodes, merging the latest ones beyond the width
  private void select(int k, int cands) {
    if (cands > width) {
      // sorted by the least time (or cost) of each candidate, then by its index
      for (int c = 0; c < cands; c++) {
        long m = INF;
        // with a cost, merge the nodes of the most expensive paths, else of the latest ones
        long[] key = costs != null ? candTop[c] : candTime[c];
        long[] cl = candLast[c];
        for (int w = 0; w < words; w++) {
          for (long bits = cl[w]; bits != 0; bits &= bits - 1) {
            m = Math.min(m, key[(w << 6) + Long.numberOfTrailingZeros(bits)]);
          }
        }
        order[c] = Math.clamp(m, 0, MAX_KEY) * (width * n) + c;
      }
      Arrays.sort(order, 0, cands);
    } else {
      for (int c = 0; c < cands; c++) {
        order[c] = c;
      }
    }
    int nodes = Math.min(cands, width);
    for (int r = 0; r < cands; r++) {
      int c = (int) (order[r] % (width * n));
      int u = Math.min(r, width - 1);
      candToNode[c] = u;
      long[] cl = candLast[c];
      long[] ct = candTime[c];
      long[] cp = candTop[c];
      long[] t = time[k][u];
      long[] p = top[k][u];
      if (r <= u) {
        clearNode(k, u);
        System.arraycopy(candAll[c], 0, allMask[k][u], 0, words);
        System.arraycopy(candSome[c], 0, someMask[k][u], 0, words);
        System.arraycopy(cl, 0, lastMask[k][u], 0, words);
        nodeHash[k][u] = candHash[c];
      } else {
        long[] a = allMask[k][u];
        long[] s = someMask[k][u];
        long[] lm = lastMask[k][u];
        for (int w = 0; w < words; w++) {
          a[w] &= candAll[c][w];
          s[w] |= candSome[c][w];
          lm[w] |= cl[w];
        }
      }
      // takes the times and costs of the candidate and leaves its arrays at INF for the next layer
      for (int w = 0; w < words; w++) {
        for (long bits = cl[w]; bits != 0; bits &= bits - 1) {
          int j = (w << 6) + Long.numberOfTrailingZeros(bits);
          t[j] = Math.min(t[j], ct[j]);
          p[j] = Math.min(p[j], cp[j]);
          ct[j] = INF;
          cp[j] = INF;
        }
        cl[w] = 0L;
      }
    }
    if (cands > width) {
      // the merged node's visited set shrank; hash it again
      long[] a = allMask[k][width - 1];
      long h = 0;
      for (int w = 0; w < words; w++) {
        for (long bits = a[w]; bits != 0; bits &= bits - 1) {
          h ^= zobrist[(w << 6) + Long.numberOfTrailingZeros(bits)];
        }
      }
      nodeHash[k][width - 1] = h;
    }
    count[k] = nodes;
  }

  // the latest arrival at j after which j is left by l, or NEG when none; the start is not left
  private long arrivalLimit(int j, long l) {
    long earliest = loIn[j];
    long x = hiIn[j];
    if (earliest > x) {
      return NEG;
    }
    if (j != start) {
      if (loOut[j] > l) {
        return NEG;
      }
      if (delta[j] != NONE) {
        if (earliest + delta[j] > l) {
          return NEG;
        }
        x = Math.min(x, l - delta[j]);
      }
    }
    return x;
  }

  // the latest departure from i that arrives at j by x
  private long departureLimit(int i, int j, long x) {
    int tr = travel[i][j];
    if (tr == NONE) {
      return INF;
    }
    if (stepTravel != null && stepTravel[i][j] != null) {
      return x >= INF ? INF : stepLatest(i, j, x);
    }
    return x >= INF ? INF : x - tr;
  }

  // the latest departure from i after which j is reached and left by l, or NEG when none
  private long latestDeparture(int i, int j, long l) {
    long x = arrivalLimit(j, l);
    return x == NEG ? NEG : departureLimit(i, j, x);
  }

  // backward pass: the latest departure of each (node, last) that still reaches the closing arc;
  // keeps the arcs between an earliest and a latest time that meet, then prunes
  private void prune(Store store) {
    int last = n - 1;
    long[][] latest = this.latest;
    long[][] prev = this.prev;
    // the least cost from each (node, last) to the end of the circuit
    long[][] bottom = this.bottom;
    long[][] prevBottom = this.prevBottom;
    long budget = cost == null ? INF : cost.max() - costOffset;
    Arrays.fill(minIn, INF);
    Arrays.fill(minOut, INF);
    Arrays.fill(maxIn, NEG);
    Arrays.fill(maxOut, NEG);
    Arrays.fill(support, false);
    long closing = INF;
    for (int u = 0; u < count[last]; u++) {
      long[] tu = time[last][u];
      long[] lm = lastMask[last][u];
      for (int w = 0; w < words; w++) {
        for (long bits = lm[w]; bits != 0; bits &= bits - 1) {
          int i = (w << 6) + Long.numberOfTrailingZeros(bits);
          latest[u][i] = NEG;
          if (!get(outMask[i], start)) {
            continue;
          }
          long l = Math.min(hiOut[i], latestDeparture(i, start, INF));
          long b = arcCost(i, start);
          if (tu[i] <= l && top[last][u][i] + b <= budget) {
            latest[u][i] = l;
            bottom[u][i] = b;
            support[i * n + start] = true;
            closing = Math.min(closing, arrival(i, start, tu[i]));
            note(i, tu[i], l, minOut, maxIn, maxOut);
          }
        }
      }
    }
    if (closing == INF) {
      throw Store.failException;
    }
    for (int k = last - 1; k >= 0; k--) {
      for (int u = 0; u < count[k]; u++) {
        long[] tu = time[k][u];
        long[] cu = top[k][u];
        long[] lm = lastMask[k][u];
        int[] tgt = target[k][u];
        long[] lu = prev[u];
        long[] bu = prevBottom[u];
        for (int w = 0; w < words; w++) {
          for (long bits = lm[w]; bits != 0; bits &= bits - 1) {
            int i = (w << 6) + Long.numberOfTrailingZeros(bits);
            leave[i] = NEG;
            rest[i] = INF;
          }
        }
        for (int j = 0; j < n; j++) {
          int v = tgt[j];
          if (v < 0 || latest[v][j] == NEG) {
            continue;
          }
          long x = arrivalLimit(j, latest[v][j]);
          if (x == NEG) {
            continue;
          }
          long below = bottom[v][j];
          long[] im = inMask[j];
          for (int w = 0; w < words; w++) {
            for (long bits = lm[w] & im[w]; bits != 0; bits &= bits - 1) {
              int i = (w << 6) + Long.numberOfTrailingZeros(bits);
              long t = tu[i];
              long l = departureLimit(i, j, x);
              if (l < t) {
                continue;
              }
              long b = arcCost(i, j) + below;
              if (cu[i] + b > budget) {
                continue;
              }
              long a = arrival(i, j, t);
              long d = departure(j, a);
              if (a == INF || d == INF) {
                continue;
              }
              leave[i] = Math.max(leave[i], l);
              rest[i] = Math.min(rest[i], b);
              support[i * n + j] = true;
              minIn[j] = Math.min(minIn[j], a);
              minOut[j] = Math.min(minOut[j], d);
            }
          }
        }
        for (int w = 0; w < words; w++) {
          for (long bits = lm[w]; bits != 0; bits &= bits - 1) {
            int i = (w << 6) + Long.numberOfTrailingZeros(bits);
            long t = tu[i];
            long bst = Math.min(leave[i], hiOut[i]);
            lu[i] = NEG;
            if (bst >= t) {
              lu[i] = bst;
              bu[i] = rest[i];
              if (k > 0) {
                note(i, t, bst, minOut, maxIn, maxOut);
              }
            }
          }
        }
      }
      long[][] swap = latest;
      latest = prev;
      prev = swap;
      swap = bottom;
      bottom = prevBottom;
      prevBottom = swap;
    }
    if (latest[0][start] == NEG) {
      throw Store.failException;
    }
    if (cost != null && bottom[0][start] + costOffset > cost.min()) {
      pruned = true;
      raise(store, cost, bottom[0][start] + costOffset);
    }
    // successor values on no path
    for (int i = 0; i < n; i++) {
      long[] om = outMask[i];
      for (int w = 0; w < words; w++) {
        for (long bits = om[w]; bits != 0; bits &= bits - 1) {
          int j = (w << 6) + Long.numberOfTrailingZeros(bits);
          if (i != j && !support[i * n + j]) {
            IntVar x = pred ? arcs[j] : arcs[i];
            int value = offset + (pred ? i : j);
            x.domain.inComplement(store.level, x, value);
            pruned = true;
          }
        }
      }
    }
    minIn[start] = Math.min(minIn[start], closing);
    for (int j = 0; j < n; j++) {
      raise(store, in[j], minIn[j]);
      if (j != start) {
        raise(store, out[j], minOut[j]);
        lower(store, in[j], maxIn[j]);
        lower(store, out[j], maxOut[j]);
      }
    }
  }

  // a (node, last j) on a path: its departure lies in [t, l]; the arrival at j is at most l - delta
  private void note(int j, long t, long l, long[] minOut, long[] maxIn, long[] maxOut) {
    minOut[j] = Math.min(minOut[j], t);
    maxOut[j] = Math.max(maxOut[j], l);
    long a = hiIn[j];
    if (delta[j] != NONE) {
      a = Math.min(a, l - delta[j]);
    }
    maxIn[j] = Math.max(maxIn[j], a);
  }

  private static void lower(Store store, IntVar v, long max) {
    if (v != null && max != NEG && max < v.max()) {
      if (max < v.min()) {
        throw Store.failException;
      }
      v.domain.inMax(store.level, v, (int) max);
    }
  }

  private static void raise(Store store, IntVar v, long min) {
    if (v != null && min != INF && min > v.min()) {
      if (min > v.max()) {
        throw Store.failException;
      }
      v.domain.inMin(store.level, v, (int) min);
    }
  }

  private static void set(long[] mask, int j) {
    mask[j >>> 6] |= 1L << j;
  }

  private static boolean get(long[] mask, int j) {
    return (mask[j >>> 6] & (1L << j)) != 0;
  }

  private static void orInto(long[] into, long[] from) {
    for (int w = 0; w < into.length; w++) {
      into[w] |= from[w];
    }
  }

  private static int bitCount(long[] mask) {
    int c = 0;
    for (long w : mask) {
      c += Long.bitCount(w);
    }
    return c;
  }

  // a call with every arc fixed is never skipped, so the constraint checks a fixed circuit
  private boolean groundArcs() {
    for (IntVar a : arcs) {
      if (!a.singleton()) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (n <= REPLAY_NODES) {
      return false;
    }
    trail.genericReason(entry, out);
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (n <= REPLAY_NODES) {
      return false;
    }
    for (Var v : arguments()) {
      trail.atomsBefore(v, trail.size(), out);
    }
    return true;
  }

  @Override
  public boolean satisfied() {
    for (Var v : arguments()) {
      if (!v.singleton()) {
        return false;
      }
    }
    long total = 0;
    int i = start;
    for (int k = 0; k < n; k++) {
      int j = pred ? successorOf(i) : arcs[i].value() - offset;
      if (j < 0 || j >= n || k < n - 1 && j == start) {
        return false;
      }
      int tr = travel[i][j];
      if (tr != NONE
          && in[j] != null
          && out[i] != null
          && in[j].value() < out[i].value() + travelAt(i, j, out[i].value())) {
        return false;
      }
      total += arcCost(i, j);
      i = j;
    }
    if (i != start) {
      return false;
    }
    for (int j = 0; j < n; j++) {
      if (delta[j] != NONE
          && in[j] != null
          && out[j] != null
          && out[j].value() < (long) in[j].value() + delta[j]) {
        return false;
      }
    }
    return cost == null || cost.value() >= total + costOffset;
  }

  // the successor of i given by predecessor variables, or -1
  private int successorOf(int i) {
    for (int j = 0; j < n; j++) {
      if (arcs[j].value() - offset == i) {
        return j;
      }
    }
    return -1;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : SequenceMdd([");
    appendArrayToString(result, arcs);
    result.append("], ").append(pred ? "pred" : "succ").append(", offset ").append(offset);
    result.append(", start ").append(start).append(", width ").append(width);
    if (cost != null) {
      result.append(", cost ").append(cost).append(" + ").append(costOffset);
    }
    result.append(")");
    return result.toString();
  }

  @Override
  public SequenceMdd copy(VarMap map) {
    return new SequenceMdd(
        map.get(arcs),
        pred,
        offset,
        mapNullable(map, in),
        mapNullable(map, out),
        travel,
        delta,
        start,
        width,
        costs,
        cost == null ? null : map.get(cost),
        costOffset,
        stepTravel,
        stepLength);
  }

  private static IntVar[] mapNullable(VarMap map, IntVar[] vars) {
    IntVar[] r = new IntVar[vars.length];
    for (int i = 0; i < vars.length; i++) {
      r[i] = vars[i] == null ? null : map.get(vars[i]);
    }
    return r;
  }
}
