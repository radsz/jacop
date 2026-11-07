/*
 * DisjunctiveSchedule.java
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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.SplittableRandom;

/**
 * Tabu search over the machine sequences of a disjunctive scheduling model, the scheduling
 * abstraction of Comet's constraint-based local search (P. Van Hentenryck, L. Michel, "Scheduling
 * abstractions for local search", CPAIOR 2004, LNCS 3011, 319-334).
 *
 * <p>The model is a disjunctive graph: tasks with fixed durations, precedence arcs with time lags
 * (rows {@code s[a] + lag <= s[b]}), and machines, each a resource on which no two of its tasks may
 * overlap. A state is one sequence per machine. Every task starts as early as the arcs of the
 * sequences and the precedences allow (a semi-active schedule), and the makespan is the length of
 * the longest path. The moves reorder operations of the blocks of one critical path (maximal runs
 * of consecutive operations of the path on one machine):
 *
 * <ul>
 *   <li>{@link #N1}: swap two adjacent operations of a block (P. J. M. van Laarhoven, E. H. L.
 *       Aarts, J. K. Lenstra, "Job shop scheduling by simulated annealing", Operations Research
 *       40(1), 1992, 113-125);
 *   <li>{@link #NS}: swap only the first two and the last two operations of each block, except the
 *       first two of the first block and the last two of the last (E. Nowicki, C. Smutnicki, "A
 *       fast taboo search algorithm for the job shop problem", Management Science 42(6), 1996,
 *       797-813);
 *   <li>{@link #N4}: move an operation of a block to the front or to the back of its block (M.
 *       Dell'Amico, M. Trubian, "Applying tabu search to the job-shop scheduling problem", Annals
 *       of Operations Research 41, 1993, 231-252).
 * </ul>
 *
 * <p>Swaps are ranked by the estimate of Taillard (E. D. Taillard, "Parallel taboo search
 * techniques for the job shop scheduling problem", ORSA Journal on Computing 6(2), 1994, 108-117)
 * from the heads and tails of the two operations, insertions by the exact makespan. The move chosen
 * is the best one that is not tabu; a tabu move is taken when it gives a makespan better than the
 * best one found (aspiration). A move forbids, for a few iterations, the arcs it reversed. After a
 * number of iterations without a better makespan, the search goes back to the best sequences and
 * perturbs them with a few random swaps.
 *
 * <p>The search only proposes schedules; the local search checks each better one in the store.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class DisjunctiveSchedule {

  /** Swap the first two and last two operations of each critical block (Nowicki-Smutnicki). */
  static final int NS = 1;

  /** Swap any two adjacent operations of a critical block (van Laarhoven, Aarts, Lenstra). */
  static final int N1 = 2;

  /**
   * Move an operation of a critical block to the front or back of the block (Dell'Amico-Trubian).
   */
  static final int N4 = 4;

  /** What the search is told about the schedules it found. */
  interface Listener {

    /**
     * Checks a schedule better than the bound.
     *
     * @param start the start of each task.
     * @param makespan its makespan.
     * @return false when the schedule cannot be used, so the search should stop.
     */
    boolean report(int[] start, int makespan);

    /**
     * The largest makespan worth reporting.
     *
     * @return the bound.
     */
    long bound();

    /**
     * Whether the search must stop.
     *
     * @return true to stop.
     */
    boolean stop();
  }

  private static final int NONE = Integer.MIN_VALUE / 4;
  // iterations without a better makespan before going back to the best sequences
  private static final int STALL = 4000;

  final int n;
  // the local-search variable of each task's start, its duration, release and deadline
  final int[] aVar;
  final int[] dur;
  private final int[] release;
  private final int[] deadline;
  // precedence arcs: successors and predecessors with their time lags
  private final int[][] succ;
  private final int[][] succLag;
  private final int[][] pred;
  private final int[][] predLag;
  // the machines of each task and its position in their sequences
  private final int[][] machinesOf;
  private final int[][] posOf;
  final int[][] seq;
  private final int kinds;
  private final SplittableRandom random;

  // heads (earliest starts), tails (longest path from a start to the end), a topological order
  private final int[] head;
  private final int[] tail;
  private final int[] topo;
  private final int[] indeg;
  private int makespan;

  // the critical path and the machine of the arc leaving each of its tasks (-1: precedence or end)
  private final int[] path;
  private final int[] pathMachine;
  private int pathLength;

  private final Map<Long, Long> tabu = new HashMap<>();
  private long iteration;
  private long applied;

  DisjunctiveSchedule(
      int[] aVar,
      int[] dur,
      int[] release,
      int[] deadline,
      List<int[]> arcs,
      List<int[]> machines,
      int kinds,
      SplittableRandom random) {
    this.n = aVar.length;
    this.aVar = aVar;
    this.dur = dur;
    this.release = release;
    this.deadline = deadline;
    this.kinds = kinds;
    this.random = random;
    int[] out = new int[n];
    int[] in = new int[n];
    for (int[] a : arcs) {
      out[a[0]]++;
      in[a[1]]++;
    }
    succ = new int[n][];
    succLag = new int[n][];
    pred = new int[n][];
    predLag = new int[n][];
    for (int t = 0; t < n; t++) {
      succ[t] = new int[out[t]];
      succLag[t] = new int[out[t]];
      pred[t] = new int[in[t]];
      predLag[t] = new int[in[t]];
    }
    Arrays.fill(out, 0);
    Arrays.fill(in, 0);
    for (int[] a : arcs) {
      succ[a[0]][out[a[0]]] = a[1];
      succLag[a[0]][out[a[0]]++] = a[2];
      pred[a[1]][in[a[1]]] = a[0];
      predLag[a[1]][in[a[1]]++] = a[2];
    }
    seq = machines.toArray(new int[0][]);
    int[] count = new int[n];
    for (int[] s : seq) {
      for (int t : s) {
        count[t]++;
      }
    }
    machinesOf = new int[n][];
    posOf = new int[n][];
    for (int t = 0; t < n; t++) {
      machinesOf[t] = new int[count[t]];
      posOf[t] = new int[count[t]];
    }
    Arrays.fill(count, 0);
    for (int m = 0; m < seq.length; m++) {
      for (int t : seq[m]) {
        machinesOf[t][count[t]++] = m;
      }
    }
    head = new int[n];
    tail = new int[n];
    topo = new int[n];
    indeg = new int[n];
    path = new int[n + 1];
    pathMachine = new int[n + 1];
  }

  /** The number of machines. */
  int machines() {
    return seq.length;
  }

  /** The tabu search iterations made. */
  long iterations() {
    return iteration;
  }

  /** The moves applied. */
  long moves() {
    return applied;
  }

  /** The makespan of the current sequences, or NONE when they have a cycle or miss a deadline. */
  int makespan() {
    return makespan;
  }

  /** The start of each task in the current schedule. */
  int[] starts() {
    return head.clone();
  }

  /**
   * Orders the tasks of every machine by list scheduling: repeatedly the task whose predecessors
   * are all scheduled and whose priority (then earliest start) is smallest is appended to its
   * machines. The sequences are then free of cycles.
   *
   * @param priority the priority of each task, such as the start a local search gave it.
   * @return false when the precedences alone have a cycle.
   */
  boolean initialise(int[] priority) {
    int[] waiting = new int[n];
    int[] ready = new int[n];
    int[] machineEnd = new int[seq.length];
    int[] fill = new int[seq.length];
    Arrays.fill(machineEnd, Integer.MIN_VALUE);
    int[] early = release.clone();
    boolean[] done = new boolean[n];
    for (int t = 0; t < n; t++) {
      waiting[t] = pred[t].length;
    }
    for (int scheduled = 0; scheduled < n; scheduled++) {
      int best = -1;
      long bestKey = Long.MAX_VALUE;
      for (int t = 0; t < n; t++) {
        if (done[t] || waiting[t] > 0) {
          continue;
        }
        int e = early[t];
        for (int m : machinesOf[t]) {
          e = Math.max(e, machineEnd[m]);
        }
        ready[t] = e;
        long key = ((long) priority[t] << 32) + e;
        if (key < bestKey) {
          bestKey = key;
          best = t;
        }
      }
      if (best < 0) {
        return false;
      }
      done[best] = true;
      for (int k = 0; k < machinesOf[best].length; k++) {
        int m = machinesOf[best][k];
        posOf[best][k] = fill[m];
        seq[m][fill[m]++] = best;
        machineEnd[m] = ready[best] + dur[best];
      }
      for (int k = 0; k < succ[best].length; k++) {
        int s = succ[best][k];
        waiting[s]--;
        early[s] = Math.max(early[s], ready[best] + succLag[best][k]);
      }
    }
    evaluate();
    return true;
  }

  // ---------------------------------------------------------------- evaluation

  private int machinePos(int t, int m) {
    int[] ms = machinesOf[t];
    for (int k = 0; k < ms.length; k++) {
      if (ms[k] == m) {
        return posOf[t][k];
      }
    }
    return -1;
  }

  /**
   * Computes heads, tails and the makespan of the current sequences.
   *
   * @return the makespan, or NONE when the sequences have a cycle or a task misses its deadline.
   */
  int evaluate() {
    for (int t = 0; t < n; t++) {
      int d = pred[t].length;
      for (int k = 0; k < machinesOf[t].length; k++) {
        if (posOf[t][k] > 0) {
          d++;
        }
      }
      indeg[t] = d;
      head[t] = release[t];
    }
    int top = 0;
    for (int t = 0; t < n; t++) {
      if (indeg[t] == 0) {
        topo[top++] = t;
      }
    }
    int length = 0;
    for (int k = 0; k < top; k++) {
      int t = topo[k];
      int h = head[t];
      if (h > deadline[t]) {
        makespan = NONE;
        return NONE;
      }
      length = Math.max(length, h + dur[t]);
      for (int j = 0; j < succ[t].length; j++) {
        int s = succ[t][j];
        head[s] = Math.max(head[s], h + succLag[t][j]);
        if (--indeg[s] == 0) {
          topo[top++] = s;
        }
      }
      for (int j = 0; j < machinesOf[t].length; j++) {
        int[] s = seq[machinesOf[t][j]];
        int p = posOf[t][j] + 1;
        if (p < s.length) {
          int x = s[p];
          head[x] = Math.max(head[x], h + dur[t]);
          if (--indeg[x] == 0) {
            topo[top++] = x;
          }
        }
      }
    }
    if (top < n) {
      makespan = NONE;
      return NONE;
    }
    for (int k = n - 1; k >= 0; k--) {
      int t = topo[k];
      int q = dur[t];
      for (int j = 0; j < succ[t].length; j++) {
        q = Math.max(q, succLag[t][j] + tail[succ[t][j]]);
      }
      for (int j = 0; j < machinesOf[t].length; j++) {
        int[] s = seq[machinesOf[t][j]];
        int p = posOf[t][j] + 1;
        if (p < s.length) {
          q = Math.max(q, dur[t] + tail[s[p]]);
        }
      }
      tail[t] = q;
    }
    makespan = length;
    return length;
  }

  // the earliest start of t from everything but its arc into machine m
  private int headWithout(int t, int m) {
    int h = release[t];
    for (int j = 0; j < pred[t].length; j++) {
      h = Math.max(h, head[pred[t][j]] + predLag[t][j]);
    }
    for (int j = 0; j < machinesOf[t].length; j++) {
      int p = posOf[t][j] - 1;
      if (machinesOf[t][j] != m && p >= 0) {
        int x = seq[machinesOf[t][j]][p];
        h = Math.max(h, head[x] + dur[x]);
      }
    }
    return h;
  }

  // the tail of t from everything but its arc out of machine m
  private int tailWithout(int t, int m) {
    int q = dur[t];
    for (int j = 0; j < succ[t].length; j++) {
      q = Math.max(q, succLag[t][j] + tail[succ[t][j]]);
    }
    for (int j = 0; j < machinesOf[t].length; j++) {
      int[] s = seq[machinesOf[t][j]];
      int p = posOf[t][j] + 1;
      if (machinesOf[t][j] != m && p < s.length) {
        q = Math.max(q, dur[t] + tail[s[p]]);
      }
    }
    return q;
  }

  // the operations of a machine segment in their order after a move, and their new heads
  private int[] segment = new int[16];
  private int[] segmentHead = new int[16];

  /**
   * An estimate of the makespan after moving the operation at position from of machine m to
   * position to: the longest path through the operations between the two positions, from their new
   * order on m, the heads of their other predecessors and the tails of their other successors. For
   * a swap of adjacent operations it is Taillard's estimate; for an insertion, the estimate of
   * Dell'Amico and Trubian along the block.
   */
  private int estimate(int m, int from, int to) {
    int[] s = seq[m];
    int lo = Math.min(from, to);
    int hi = Math.max(from, to);
    int len = hi - lo + 1;
    if (segment.length < len) {
      segment = new int[2 * len];
      segmentHead = new int[2 * len];
    }
    if (from < to) {
      System.arraycopy(s, from + 1, segment, 0, to - from);
      segment[len - 1] = s[from];
    } else {
      segment[0] = s[from];
      System.arraycopy(s, to, segment, 1, from - to);
    }
    int r = lo > 0 ? head[s[lo - 1]] + dur[s[lo - 1]] : NONE;
    for (int k = 0; k < len; k++) {
      int x = segment[k];
      r = Math.max(headWithout(x, m), r);
      segmentHead[k] = r;
      r += dur[x];
    }
    int q = hi + 1 < s.length ? tail[s[hi + 1]] : NONE;
    int value = 0;
    for (int k = len - 1; k >= 0; k--) {
      int x = segment[k];
      q = Math.max(tailWithout(x, m), q == NONE ? NONE : dur[x] + q);
      value = Math.max(value, segmentHead[k] + q);
    }
    return value;
  }

  // ---------------------------------------------------------------- moves

  // moves the operation at position from of machine m to position to, shifting those between
  private void shift(int m, int from, int to) {
    int[] s = seq[m];
    int t = s[from];
    if (from < to) {
      System.arraycopy(s, from + 1, s, from, to - from);
    } else {
      System.arraycopy(s, to, s, to + 1, from - to);
    }
    s[to] = t;
    for (int p = Math.min(from, to); p <= Math.max(from, to); p++) {
      setPos(s[p], m, p);
    }
  }

  private void setPos(int t, int m, int p) {
    int[] ms = machinesOf[t];
    for (int k = 0; k < ms.length; k++) {
      if (ms[k] == m) {
        posOf[t][k] = p;
        return;
      }
    }
  }

  private static long arc(int a, int b) {
    return ((long) a << 32) | (b & 0xffffffffL);
  }

  // whether moving from -> to on machine m puts back an arc that is tabu
  private boolean isTabu(int m, int from, int to) {
    int[] s = seq[m];
    int t = s[from];
    if (from < to) {
      for (int p = from + 1; p <= to; p++) {
        if (tabuArc(s[p], t)) {
          return true;
        }
      }
    } else {
      for (int p = to; p < from; p++) {
        if (tabuArc(t, s[p])) {
          return true;
        }
      }
    }
    return false;
  }

  private boolean tabuArc(int a, int b) {
    Long until = tabu.get(arc(a, b));
    return until != null && until > iteration;
  }

  // forbids for a while the arcs that moving from -> to on machine m reverses
  private void makeTabu(int m, int from, int to) {
    int[] s = seq[m];
    int t = s[from];
    long until = iteration + 6 + random.nextInt(8) + Math.min(8, n / Math.max(1, 4 * seq.length));
    if (from < to) {
      for (int p = from + 1; p <= to; p++) {
        tabu.put(arc(t, s[p]), until);
      }
    } else {
      for (int p = to; p < from; p++) {
        tabu.put(arc(s[p], t), until);
      }
    }
    if (tabu.size() > 64 * n) {
      tabu.values().removeIf(u -> u <= iteration);
    }
  }

  /**
   * Finds one critical path of the current schedule, from a task that ends at the makespan back to
   * a task that starts at its release, preferring at random among the tight predecessors.
   */
  private void criticalPath() {
    int end = -1;
    int ties = 0;
    for (int t = 0; t < n; t++) {
      if (head[t] + dur[t] == makespan && random.nextInt(++ties) == 0) {
        end = t;
      }
    }
    int k = 0;
    int t = end;
    int[] tight = new int[8];
    int[] tightMachine = new int[8];
    while (t >= 0 && k < n) {
      path[k++] = t;
      int nt = 0;
      for (int j = 0; j < pred[t].length; j++) {
        if (head[pred[t][j]] + predLag[t][j] == head[t]) {
          if (nt == tight.length) {
            tight = Arrays.copyOf(tight, 2 * nt);
            tightMachine = Arrays.copyOf(tightMachine, 2 * nt);
          }
          tight[nt] = pred[t][j];
          tightMachine[nt++] = -1;
        }
      }
      for (int j = 0; j < machinesOf[t].length; j++) {
        int p = posOf[t][j] - 1;
        if (p >= 0) {
          int x = seq[machinesOf[t][j]][p];
          if (head[x] + dur[x] == head[t]) {
            if (nt == tight.length) {
              tight = Arrays.copyOf(tight, 2 * nt);
              tightMachine = Arrays.copyOf(tightMachine, 2 * nt);
            }
            tight[nt] = x;
            tightMachine[nt++] = machinesOf[t][j];
          }
        }
      }
      if (nt == 0) {
        break;
      }
      int pick = random.nextInt(nt);
      t = tight[pick];
      // the machine of the arc from the next task of the path (in reverse) to the one just added
      pathMachine[k] = tightMachine[pick];
    }
    // reverse into forward order; pathMachine[i] is the machine of the arc path[i] -> path[i + 1]
    pathLength = k;
    int[] machine = new int[k];
    for (int i = 1; i < k; i++) {
      machine[k - 1 - i] = pathMachine[i];
    }
    for (int i = 0; i < k / 2; i++) {
      int x = path[i];
      path[i] = path[k - 1 - i];
      path[k - 1 - i] = x;
    }
    System.arraycopy(machine, 0, pathMachine, 0, k);
    if (k > 0) {
      pathMachine[k - 1] = -1;
    }
  }

  // the moves of one iteration: machine, from, to
  private int[] moveMachine = new int[64];
  private int[] moveFrom = new int[64];
  private int[] moveTo = new int[64];
  private int moveCount;

  private void addMove(int m, int from, int to) {
    for (int k = 0; k < moveCount; k++) {
      if (moveMachine[k] == m && moveFrom[k] == from && moveTo[k] == to) {
        return;
      }
    }
    if (moveCount == moveMachine.length) {
      moveMachine = Arrays.copyOf(moveMachine, 2 * moveCount);
      moveFrom = Arrays.copyOf(moveFrom, 2 * moveCount);
      moveTo = Arrays.copyOf(moveTo, 2 * moveCount);
    }
    moveMachine[moveCount] = m;
    moveFrom[moveCount] = from;
    moveTo[moveCount++] = to;
  }

  // the moves of the neighbourhoods over the blocks of the critical path
  private void collectMoves() {
    moveCount = 0;
    List<int[]> blocks = new ArrayList<>();
    int i = 0;
    while (i < pathLength - 1) {
      int m = pathMachine[i];
      if (m < 0) {
        i++;
        continue;
      }
      int j = i;
      while (j < pathLength - 1 && pathMachine[j] == m) {
        j++;
      }
      // tasks path[i..j] are consecutive on machine m
      blocks.add(new int[] {m, machinePos(path[i], m), machinePos(path[j], m)});
      i = j;
    }
    for (int b = 0; b < blocks.size(); b++) {
      int m = blocks.get(b)[0];
      int first = blocks.get(b)[1];
      int last = blocks.get(b)[2];
      if ((kinds & N1) != 0) {
        for (int p = first; p < last; p++) {
          addMove(m, p, p + 1);
        }
      }
      if ((kinds & NS) != 0) {
        if (b > 0 || blocks.size() == 1) {
          addMove(m, first, first + 1);
        }
        if (b < blocks.size() - 1 || blocks.size() == 1) {
          addMove(m, last - 1, last);
        }
      }
      if ((kinds & N4) != 0 && last - first >= 2) {
        for (int p = first + 1; p < last; p++) {
          addMove(m, p, first);
          addMove(m, p, last);
        }
        addMove(m, first, last);
        addMove(m, last, first);
      }
    }
  }

  /**
   * Runs the tabu search until the listener says to stop or rejects a schedule.
   *
   * @param listener receives every schedule better than its bound.
   * @return false when the listener rejected a schedule.
   */
  boolean run(Listener listener) {
    if (evaluate() == NONE) {
      return true;
    }
    int best = makespan;
    int[][] bestSeq = copy(seq);
    if (makespan <= listener.bound() && !listener.report(head.clone(), makespan)) {
      return false;
    }
    long lastImprovement = iteration;
    while (!listener.stop()) {
      iteration++;
      criticalPath();
      collectMoves();
      int chosen = -1;
      int chosenValue = Integer.MAX_VALUE;
      int ties = 0;
      for (int k = 0; k < moveCount; k++) {
        int m = moveMachine[k];
        int from = moveFrom[k];
        int to = moveTo[k];
        int value = estimate(m, from, to);
        if (isTabu(m, from, to) && value >= best) {
          continue;
        }
        if (value < chosenValue) {
          chosenValue = value;
          chosen = k;
          ties = 1;
        } else if (value == chosenValue && random.nextInt(++ties) == 0) {
          chosen = k;
        }
      }
      if (chosen < 0 && moveCount > 0) {
        // every move is tabu: take one at random
        chosen = random.nextInt(moveCount);
      }
      if (chosen >= 0) {
        apply(chosen);
      }
      if (makespan < best) {
        best = makespan;
        bestSeq = copy(seq);
        lastImprovement = iteration;
        if (makespan <= listener.bound() && !listener.report(head.clone(), makespan)) {
          return false;
        }
      } else if (moveCount == 0 || iteration - lastImprovement > STALL) {
        restore(bestSeq);
        perturb();
        tabu.clear();
        lastImprovement = iteration;
      }
    }
    return true;
  }

  // applies move k; false (and undone) when it gives a cycle or misses a deadline
  private boolean apply(int k) {
    int m = moveMachine[k];
    int from = moveFrom[k];
    int to = moveTo[k];
    makeTabu(m, from, to);
    shift(m, from, to);
    if (evaluate() == NONE) {
      shift(m, to, from);
      evaluate();
      return false;
    }
    applied++;
    return true;
  }

  // a few random swaps of adjacent operations that keep the sequences free of cycles
  private void perturb() {
    int changes = 2 + random.nextInt(Math.max(1, Math.min(8, n / 10)));
    for (int c = 0; c < changes; c++) {
      criticalPath();
      collectBlocksForPerturb();
      if (moveCount == 0) {
        return;
      }
      int k = random.nextInt(moveCount);
      shift(moveMachine[k], moveFrom[k], moveTo[k]);
      if (evaluate() == NONE) {
        shift(moveMachine[k], moveTo[k], moveFrom[k]);
        evaluate();
      }
    }
  }

  private void collectBlocksForPerturb() {
    moveCount = 0;
    for (int i = 0; i < pathLength - 1; i++) {
      int m = pathMachine[i];
      if (m >= 0) {
        int p = machinePos(path[i], m);
        addMove(m, p, p + 1);
      }
    }
  }

  private void restore(int[][] from) {
    for (int m = 0; m < seq.length; m++) {
      System.arraycopy(from[m], 0, seq[m], 0, seq[m].length);
      for (int p = 0; p < seq[m].length; p++) {
        setPos(seq[m][p], m, p);
      }
    }
    evaluate();
  }

  private static int[][] copy(int[][] a) {
    int[][] c = new int[a.length][];
    for (int k = 0; k < a.length; k++) {
      c[k] = a[k].clone();
    }
    return c;
  }
}
