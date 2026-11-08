/*
 * UnaryEarlinessTardiness.java
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
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Earliness and tardiness costs of tasks on unary machines: the tasks of each machine do not
 * overlap (task i occupies [s[i], s[i] + p[i]) with a fixed duration p[i] &gt; 0), and sum(i)
 * f[i](s[i]) &lt;= cost, where f[i] is a sum of terms e * max(0, b - s[i]) + t * max(0, s[i] - b)
 * with e, t &gt;= 0, as in {@link PrecedenceCost}. The constraint propagates the lower bound of the
 * cost; the machines themselves need their own resource constraints.
 *
 * <p>The bound is the assignment bound of Sourd and Kedad-Sidhoum (2003): each task is split into
 * p[i] unit operations that may go into any unit time slot of its window [min s[i], max s[i] +
 * p[i]), at most one operation per slot. A unit in slot u costs c[i](u), chosen so that the
 * operations of any non-preempted schedule of the task cost at most f[i]: sum(u in [s, s + p))
 * c[i](u) &lt;= f[i](s) for every s. The minimum cost of the assignment (a transportation problem)
 * is then a lower bound of the cost of every schedule of the machine. Here c[i](u) is (1 / p[i])
 * times the hinge e * max(0, D - w - u) + t * max(0, u - D - w), with D = b + (p[i] - 1) / 2 the
 * position of the due date in unit slots: with w = 0 the sum is exactly f[i](s) for a task wholly
 * early or wholly late, and the flat part 2w, the smallest that keeps the inequality for the tasks
 * that straddle the due date, is found once per duration and cost ratio. Each machine counts the
 * costs of the tasks whose costs it owns, so a task on several machines is counted once; a task on
 * no machine contributes the exact minimum of f[i] over its bounds.
 *
 * <p>For speed the slots of a machine are grouped into at most a fixed number of blocks of equal
 * length (property {@code org.jacop.unaryEarlinessTardiness.blocks}, 64 by default), each with the
 * capacity of its length, and an operation in a block costs the least c[i] over the slots of the
 * block in its window; this is a relaxation of the slot problem, so the bound stays valid. The
 * transportation problem is solved by successive shortest paths with node potentials; the bound
 * used is the value of its dual, sum(i) p[i] * u[i] - sum(k) capacity[k] * w[k] with w[k] = max(0,
 * max(i) u[i] - c[i][k]), which is a lower bound for any u, so the pruning is sound even if the
 * flow were not optimal. Costs are scaled by 4096 and rounded down, so they stay integral.
 *
 * <p>A machine is not solved again while its last flow stays optimal (the flow still fits and its
 * arcs cost the same, no other arc got cheaper). Otherwise the dual of its last solve, with w
 * recomputed for the current costs, is still a valid bound, and the last flow moved greedily into
 * the current windows gives an upper bound of the optimum; the machines are solved exactly only
 * when that upper bound exceeds the maximum of the cost, so that the exact bound could fail. When a
 * round of 500 such solves failed nothing, only one in 16 is done until one fails, and a forced
 * solve is skipped while the solves took more than 1000 steps of work per propagation of the store
 * (a deterministic budget, so the bound costs a bounded share of the search). A machine owning
 * fewer than two costs, or whose bound did not beat the exact minima of its tasks in its first 200
 * solves, counts those minima instead.
 *
 * <p>Under lazy clause generation the reason of the bound is the windows of the tasks, each
 * weakened over the blocks where the dual stays feasible (u[i] - c[i][k] &lt;= w[k] for the whole
 * block), and for a task on no machine the bound of its start its minimum depends on.
 *
 * <p>References: F. Sourd and S. Kedad-Sidhoum, The one-machine problem with earliness and
 * tardiness penalties, Journal of Scheduling 6(6), 533-549, 2003; F. Sourd, New exact algorithms
 * for one-machine earliness-tardiness scheduling, INFORMS Journal on Computing 21(1), 167-175,
 * 2009.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class UnaryEarlinessTardiness extends Constraint
    implements SatisfiedPresent, Explainable, Copyable<UnaryEarlinessTardiness> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The scale of the slot costs. */
  public static final long SCALE = 4096;

  private static final long INF = Long.MAX_VALUE / 4;

  // the largest number of blocks of a machine
  static final int MAX_BLOCKS =
      Math.max(1, Integer.getInteger("org.jacop.unaryEarlinessTardiness.blocks", 64));

  final IntVar[] starts;
  final int[] durations;
  final int[][] machines;
  final int[] owner;
  final int[][] terms;
  final IntVar cost;

  private final int n;
  // the terms of each task: due date, earliness and tardiness weights, and the flat part 2w
  private final long[][] termB;
  private final long[][] termE;
  private final long[][] termT;
  private final long[][] termW2;
  // an integer minimum of f[i], and of the slot cost of task i
  private final long[] bestStart;
  private final long[] bestSlot;
  private final boolean[] hasCost;

  private final Map<IntVar, Integer> index = new IdentityHashMap<>();

  // the tasks owning costs but on no machine
  private final int[] outside;

  // solves of a machine after which it is turned off if its bound never beat the exact minima
  static final int TRIAL = Integer.getInteger("org.jacop.unaryEarlinessTardiness.trial", 200);

  // whether a solve counts towards turning a machine off (not in explanations and tests)
  private boolean adaptive;

  // solves forced in search by a repaired flow above the maximum: after a round of this many
  // without a failure only one in SPARSE is done, until one of those fails
  static final int FORCED_ROUND =
      Integer.getInteger("org.jacop.unaryEarlinessTardiness.forcedRound", 500);

  static final int SPARSE = 16;

  // the work (inner steps of the solver, about a nanosecond each) the solves in propagation may
  // take per propagation of the store, so that the bound costs a bounded share of the search
  static final long WORK =
      Long.getLong("org.jacop.unaryEarlinessTardiness.workPerPropagation", 1000);

  // the work of the solves in propagation so far, and the store's propagations at this one
  private long work;
  private long propagations;

  // the solves forced in this round, how many of them failed, whether this propagation forced one,
  // the propagations that could force one, and the stride between forced solves
  private int forcedSolves;
  private int forcedFails;
  private boolean forcedSolve;
  private long eligible;
  private int stride = 1;

  // per machine
  private final Machine[] machine;

  // the solver workspace, sized for the largest machine
  private final long[] pot;
  private final long[] dist;
  private final int[] parent;
  private final boolean[] done;

  // the current box of the starts
  private final long[] lo;
  private final long[] hi;

  // the certificate of the last bound of propagation: the weakest start bounds it holds for
  private final long[] needLo;
  private final long[] needHi;
  private long certifiedBound = Long.MIN_VALUE;
  private boolean certificateValid;

  /** One unary machine: its tasks, its blocks of slots, and the flow of its last solve. */
  private static final class Machine {
    final int[] task;
    final int jobs;
    final long first;
    final long length;
    final int blocks;
    final long[] capacity;
    // costs (INF when the block is not in the window), flow and supply of the last solve
    final long[] c;
    // the costs of the current box
    final long[] cur;
    final long[] flow;
    final long[] used;
    final long[] rem;
    final long[] u;
    final long[] w;
    long value;
    // valid: the flow is optimal for the costs c; dual: u holds the dual of a solve
    boolean valid;
    boolean dual;
    boolean feasible;
    // the tasks whose costs this machine counts
    int[] owned;
    // whether the last bound used the exact minima of the owned tasks instead of the assignment
    boolean trivial;
    long trivialValue;
    // the lower bound of the last bound, and whether it came from the dual of an older solve
    long lower;
    boolean approximate;
    // solves, and solves whose bound beat the exact minima of the owned tasks; off when the
    // assignment did not beat them in the first solves, or the machine owns fewer than two costs
    int solves;
    int wins;
    boolean off;

    Machine(int[] task, long first, long last) {
      this.task = task;
      this.jobs = task.length;
      this.first = first;
      long span = Math.max(1, last - first);
      int b = (int) Math.min(MAX_BLOCKS, span);
      this.length = (span + b - 1) / b;
      this.blocks = (int) ((span + length - 1) / length);
      this.capacity = new long[blocks];
      for (int k = 0; k < blocks; k++) {
        capacity[k] = Math.min(length, span - k * length);
      }
      this.c = new long[jobs * blocks];
      this.cur = new long[jobs * blocks];
      this.flow = new long[jobs * blocks];
      this.used = new long[blocks];
      this.rem = new long[jobs];
      this.u = new long[jobs];
      this.w = new long[blocks];
    }

    long start(int k) {
      return first + k * length;
    }

    long end(int k) {
      return first + k * length + capacity[k];
    }
  }

  /**
   * It constructs the constraint on one machine holding all the tasks, each with one due date for
   * its start.
   *
   * @param starts the start times.
   * @param durations the durations, at least 1.
   * @param due the due date of each start.
   * @param earliness the earliness cost of each task per unit, at least 0.
   * @param tardiness the tardiness cost of each task per unit, at least 0.
   * @param cost the bound on the total cost.
   */
  public UnaryEarlinessTardiness(
      IntVar[] starts, int[] durations, int[] due, int[] earliness, int[] tardiness, IntVar cost) {
    this(
        starts,
        durations,
        new int[][] {all(starts)},
        new int[starts == null ? 0 : starts.length],
        termsOf(starts, due, earliness, tardiness),
        cost);
  }

  /**
   * It constructs the constraint on several machines.
   *
   * @param starts the start times.
   * @param durations the durations, at least 1.
   * @param machines the tasks of each machine, as indices of starts; a task may be on several.
   * @param owner the machine that counts the costs of each task, or -1 for none.
   * @param terms quadruples {i, b, e, t}: e * max(0, b - s[i]) + t * max(0, s[i] - b), e, t &gt;=
   *     0.
   * @param cost the bound on the total cost.
   */
  public UnaryEarlinessTardiness(
      IntVar[] starts, int[] durations, int[][] machines, int[] owner, int[][] terms, IntVar cost) {
    checkInputForNullness(new String[] {"starts", "cost"}, starts, new Object[] {cost});
    this.n = starts.length;
    if (durations == null
        || machines == null
        || owner == null
        || terms == null
        || durations.length != n
        || owner.length != n) {
      throw new IllegalArgumentException(
          "UnaryEarlinessTardiness needs a duration and an owner per task, machines and terms.");
    }
    this.numberId = idNumber.incrementAndGet();
    this.starts = Arrays.copyOf(starts, n);
    this.durations = durations.clone();
    this.cost = cost;
    for (int i = 0; i < n; i++) {
      if (index.put(starts[i], i) != null || starts[i] == cost) {
        throw new IllegalArgumentException(
            "UnaryEarlinessTardiness needs distinct start variables, other than the cost.");
      }
      if (durations[i] <= 0) {
        throw new IllegalArgumentException("UnaryEarlinessTardiness needs positive durations.");
      }
      if (owner[i] < -1 || owner[i] >= machines.length) {
        throw new IllegalArgumentException("UnaryEarlinessTardiness: owner out of range.");
      }
    }
    this.machines = new int[machines.length][];
    for (int m = 0; m < machines.length; m++) {
      if (machines[m] == null) {
        throw new IllegalArgumentException("UnaryEarlinessTardiness: null machine.");
      }
      this.machines[m] = machines[m].clone();
      boolean[] seen = new boolean[n];
      for (int i : machines[m]) {
        if (i < 0 || i >= n || seen[i]) {
          throw new IllegalArgumentException(
              "UnaryEarlinessTardiness needs machines of distinct task indices.");
        }
        seen[i] = true;
      }
    }
    this.owner = owner.clone();
    for (int i = 0; i < n; i++) {
      final int task = i;
      if (owner[i] >= 0 && Arrays.stream(machines[owner[i]]).noneMatch(v -> v == task)) {
        throw new IllegalArgumentException(
            "UnaryEarlinessTardiness: a task is owned by a machine it is not on.");
      }
    }

    this.terms = new int[terms.length][];
    int[] count = new int[n];
    for (int k = 0; k < terms.length; k++) {
      int[] r = terms[k];
      if (r == null || r.length != 4 || r[0] < 0 || r[0] >= n || r[2] < 0 || r[3] < 0) {
        throw new IllegalArgumentException(
            "UnaryEarlinessTardiness needs terms {i, b, e, t} with e, t >= 0.");
      }
      this.terms[k] = r.clone();
      count[r[0]]++;
    }
    termB = new long[n][];
    termE = new long[n][];
    termT = new long[n][];
    termW2 = new long[n][];
    for (int i = 0; i < n; i++) {
      termB[i] = new long[count[i]];
      termE[i] = new long[count[i]];
      termT[i] = new long[count[i]];
      termW2[i] = new long[count[i]];
      count[i] = 0;
    }
    Map<Long, Long> flats = new HashMap<>();
    for (int[] r : terms) {
      int i = r[0];
      int k = count[i]++;
      termB[i][k] = r[1];
      termE[i][k] = r[2];
      termT[i][k] = r[3];
      termW2[i][k] = flat(durations[i], r[2], r[3], flats);
    }
    hasCost = new boolean[n];
    bestStart = new long[n];
    bestSlot = new long[n];
    int outsideCount = 0;
    for (int i = 0; i < n; i++) {
      for (int k = 0; k < termB[i].length; k++) {
        hasCost[i] |= termE[i][k] + termT[i][k] > 0;
      }
      bestStart[i] = minimizer(i, false);
      bestSlot[i] = minimizer(i, true);
      if (hasCost[i] && owner[i] < 0) {
        outsideCount++;
      }
    }
    outside = new int[outsideCount];
    outsideCount = 0;
    for (int i = 0; i < n; i++) {
      if (hasCost[i] && owner[i] < 0) {
        outside[outsideCount++] = i;
      }
    }

    machine = new Machine[machines.length];
    int nodes = 0;
    for (int m = 0; m < machines.length; m++) {
      long first = Long.MAX_VALUE;
      long last = Long.MIN_VALUE;
      for (int i : machines[m]) {
        first = Math.min(first, starts[i].min());
        last = Math.max(last, (long) starts[i].max() + durations[i]);
      }
      if (machines[m].length == 0) {
        first = 0;
        last = 1;
      }
      machine[m] = new Machine(this.machines[m], first, last);
      final int mm = m;
      machine[m].owned =
          Arrays.stream(this.machines[m]).filter(i -> owner[i] == mm && hasCost[i]).toArray();
      machine[m].off = machine[m].owned.length < 2;
      nodes = Math.max(nodes, machine[m].jobs + machine[m].blocks + 2);
    }
    pot = new long[nodes];
    dist = new long[nodes];
    parent = new int[nodes];
    done = new boolean[nodes];
    iter = new int[nodes];
    onPath = new boolean[nodes];
    lo = new long[n];
    hi = new long[n];
    needLo = new long[n];
    needHi = new long[n];

    this.queueIndex = 3;
    setScope(Stream.concat(Arrays.stream(starts), Stream.of(cost)));
  }

  private static int[] all(IntVar[] starts) {
    int[] a = new int[starts == null ? 0 : starts.length];
    for (int i = 0; i < a.length; i++) {
      a[i] = i;
    }
    return a;
  }

  private static int[][] termsOf(IntVar[] starts, int[] due, int[] earliness, int[] tardiness) {
    if (starts == null
        || due == null
        || earliness == null
        || tardiness == null
        || due.length != starts.length
        || earliness.length != starts.length
        || tardiness.length != starts.length) {
      throw new IllegalArgumentException(
          "UnaryEarlinessTardiness needs one due date, earliness and tardiness cost per task.");
    }
    int[][] t = new int[starts.length][];
    for (int i = 0; i < starts.length; i++) {
      t[i] = new int[] {i, due[i], earliness[i], tardiness[i]};
    }
    return t;
  }

  // ---------------------------------------------------------------- the unit costs

  /**
   * The doubled hinge of one term at doubled slot position x2 = 2 * (u - b), for a duration p and a
   * flat part w2 (doubled): e * max(0, p - 1 - w2 - x2) + t * max(0, x2 - (p - 1) - w2). Divided by
   * 2p it is the cost of a unit in slot u.
   */
  public static long hinge2(long p, long e, long t, long w2, long x2) {
    long left = p - 1 - w2 - x2;
    long right = x2 - (p - 1) - w2;
    return (left > 0 ? e * left : 0) + (right > 0 ? t * right : 0);
  }

  /**
   * The smallest doubled flat part w2 in [0, p - 1] such that the units of a task of duration p
   * with one term (due date 0) cost at most its cost at every start: sum(u in [s, s + p))
   * hinge2(2u) &lt;= 2p * (e * max(0, -s) + t * max(0, s)). w2 = p - 1 always holds, and the check
   * is monotone in w2.
   */
  public static long flat(long p, long e, long t, Map<Long, Long> cache) {
    if (e + t == 0 || p == 1) {
      return 0;
    }
    long key = (p * 1_000_003L + e) * 1_000_033L + t;
    Long known = cache == null ? null : cache.get(key);
    if (known != null) {
      return known;
    }
    long low = 0;
    long high = p - 1;
    while (low < high) {
      long mid = (low + high) >>> 1;
      if (valid(p, e, t, mid)) {
        high = mid;
      } else {
        low = mid + 1;
      }
    }
    if (cache != null) {
      cache.put(key, low);
    }
    return low;
  }

  // whether the flat part w2 keeps the units of every start s in [-p, p] within the cost; outside
  // the window lies on one linear piece, where the sum is the cost minus a constant
  static boolean valid(long p, long e, long t, long w2) {
    long sum = 0;
    for (long u = -p; u < 0; u++) {
      sum += hinge2(p, e, t, w2, 2 * u);
    }
    for (long s = -p; s <= p; s++) {
      long f = e * Math.max(0, -s) + t * Math.max(0, s);
      if (sum > 2 * p * f) {
        return false;
      }
      sum += hinge2(p, e, t, w2, 2 * (s + p)) - hinge2(p, e, t, w2, 2 * s);
    }
    return true;
  }

  /**
   * The cost of a unit of task i in slot u, scaled by SCALE and rounded down.
   *
   * @param i the task.
   * @param u the slot.
   * @return floor(SCALE * c[i](u)).
   */
  long slotCost(int i, long u) {
    long p = durations[i];
    long s = 0;
    for (int k = 0; k < termB[i].length; k++) {
      s += hinge2(p, termE[i][k], termT[i][k], termW2[i][k], 2 * (u - termB[i][k]));
    }
    return Math.floorDiv(SCALE * s, 2 * p);
  }

  /**
   * It returns the cost of a task at a start time.
   *
   * @param i the task.
   * @param s the start time.
   * @return f[i](s).
   */
  public long taskCost(int i, long s) {
    long v = 0;
    for (int k = 0; k < termB[i].length; k++) {
      long b = termB[i][k];
      v += s < b ? termE[i][k] * (b - s) : termT[i][k] * (s - b);
    }
    return v;
  }

  // an integer minimizer of f[i] (or of the slot cost), among the integers next to its kinks
  private long minimizer(int i, boolean slot) {
    long best = 0;
    long bestValue = Long.MAX_VALUE;
    long p = durations[i];
    for (int k = 0; k < termB[i].length; k++) {
      long[] candidates;
      if (slot) {
        long b = termB[i][k];
        long w2 = termW2[i][k];
        // kinks at u = b + (p - 1 -+ w2) / 2
        long a = 2 * b + p - 1 - w2;
        long z = 2 * b + p - 1 + w2;
        candidates =
            new long[] {
              Math.floorDiv(a, 2),
              Math.floorDiv(a + 1, 2),
              Math.floorDiv(z, 2),
              Math.floorDiv(z + 1, 2)
            };
      } else {
        candidates = new long[] {termB[i][k]};
      }
      for (long x : candidates) {
        long v = slot ? slotCost(i, x) : taskCost(i, x);
        if (v < bestValue) {
          bestValue = v;
          best = x;
        }
      }
    }
    return best;
  }

  // the least slot cost of task i over the slots [a, z]
  private long leastSlotCost(int i, long a, long z) {
    return slotCost(i, Math.max(a, Math.min(z, bestSlot[i])));
  }

  // ---------------------------------------------------------------- the transportation problem

  /**
   * It fills the costs of a machine for the box lo, hi. A task that does not own its costs here
   * costs nothing.
   */
  private void fillCosts(int m) {
    Machine mc = machine[m];
    int blocks = mc.blocks;
    for (int j = 0; j < mc.jobs; j++) {
      int i = mc.task[j];
      long wl = lo[i];
      long wh = hi[i] + durations[i] - 1;
      boolean counted = owner[i] == m && hasCost[i];
      for (int k = 0; k < blocks; k++) {
        long a = Math.max(mc.start(k), wl);
        long z = Math.min(mc.end(k) - 1, wh);
        mc.cur[j * blocks + k] = a > z ? INF : counted ? leastSlotCost(i, a, z) : 0;
      }
    }
  }

  // whether the flow of the last solve of a machine is still feasible and costs the same, while no
  // other arc got cheaper, so it is optimal for the current box
  private boolean stillOptimal(Machine mc) {
    if (!mc.valid) {
      return false;
    }
    for (int a = 0; a < mc.c.length; a++) {
      if (mc.flow[a] > 0 ? mc.cur[a] != mc.c[a] : mc.cur[a] < mc.c[a]) {
        return false;
      }
    }
    return true;
  }

  // the value of the dual of the last solve under the current costs, with w recomputed so it stays
  // feasible: a lower bound of the scaled cost of the machine
  private long dualUnderCurrent(Machine mc) {
    int blocks = mc.blocks;
    long value = 0;
    for (int j = 0; j < mc.jobs; j++) {
      value += durations[mc.task[j]] * mc.u[j];
    }
    for (int k = 0; k < blocks; k++) {
      long wk = 0;
      for (int j = 0; j < mc.jobs; j++) {
        long c = mc.cur[j * blocks + k];
        if (c < INF) {
          wk = Math.max(wk, mc.u[j] - c);
        }
      }
      mc.w[k] = wk;
      value -= mc.capacity[k] * wk;
    }
    return value;
  }

  /**
   * It moves the units of the flow that left the windows to the cheapest blocks with room, and
   * returns the cost of the flow under the current costs (an upper bound of the optimum), or INF
   * when the units do not fit that way.
   */
  private long repairedCost(Machine mc) {
    int blocks = mc.blocks;
    for (int j = 0; j < mc.jobs; j++) {
      int base = j * blocks;
      for (int k = 0; k < blocks; k++) {
        long f = mc.flow[base + k];
        if (f > 0 && mc.cur[base + k] >= INF) {
          mc.flow[base + k] = 0;
          mc.used[k] -= f;
          mc.rem[j] += f;
        }
      }
    }
    long total = 0;
    for (int j = 0; j < mc.jobs; j++) {
      int base = j * blocks;
      while (mc.rem[j] > 0) {
        int best = -1;
        for (int k = 0; k < blocks; k++) {
          if (mc.used[k] < mc.capacity[k]
              && mc.cur[base + k] < INF
              && (best < 0 || mc.cur[base + k] < mc.cur[base + best])) {
            best = k;
          }
        }
        if (best < 0) {
          return INF;
        }
        long f = Math.min(mc.rem[j], mc.capacity[best] - mc.used[best]);
        mc.flow[base + best] += f;
        mc.used[best] += f;
        mc.rem[j] -= f;
      }
      for (int k = 0; k < blocks; k++) {
        if (mc.flow[base + k] > 0) {
          total += mc.flow[base + k] * mc.cur[base + k];
        }
      }
    }
    return total;
  }

  /**
   * It solves the transportation problem of a machine with the costs filled in, and sets its dual
   * value; false when the supply does not fit (the machine is overloaded even with preemption).
   */
  private boolean solve(int m) {
    Machine mc = machine[m];
    int jobs = mc.jobs;
    int blocks = mc.blocks;
    System.arraycopy(mc.cur, 0, mc.c, 0, mc.c.length);
    Arrays.fill(mc.flow, 0);
    Arrays.fill(mc.used, 0);
    long supply = 0;
    for (int j = 0; j < jobs; j++) {
      mc.rem[j] = durations[mc.task[j]];
      supply += mc.rem[j];
    }
    // nodes: jobs 0..jobs-1, blocks jobs..jobs+blocks-1, sink t, source s
    int t = jobs + blocks;
    int s = t + 1;
    int nodes = s + 1;
    Arrays.fill(pot, 0, nodes, 0);
    while (supply > 0) {
      Arrays.fill(dist, 0, nodes, INF);
      Arrays.fill(done, 0, nodes, false);
      Arrays.fill(parent, 0, nodes, -1);
      dist[s] = 0;
      while (true) {
        int v = -1;
        long best = INF;
        for (int x = 0; x < nodes; x++) {
          if (!done[x] && dist[x] < best) {
            best = dist[x];
            v = x;
          }
        }
        if (v < 0 || v == t) {
          break;
        }
        done[v] = true;
        long dv = dist[v] + pot[v];
        if (v == s) {
          for (int j = 0; j < jobs; j++) {
            if (mc.rem[j] > 0) {
              relax(v, j, dv - pot[j]);
            }
          }
        } else if (v < jobs) {
          int base = v * blocks;
          for (int k = 0; k < blocks; k++) {
            long c = mc.c[base + k];
            if (c < INF) {
              relax(v, jobs + k, dv + c - pot[jobs + k]);
            }
          }
        } else {
          int k = v - jobs;
          for (int j = 0; j < jobs; j++) {
            if (mc.flow[j * blocks + k] > 0) {
              relax(v, j, dv - mc.c[j * blocks + k] - pot[j]);
            }
          }
          if (mc.used[k] < mc.capacity[k]) {
            relax(v, t, dv - pot[t]);
          }
        }
      }
      if (adaptive) {
        work += (long) nodes * nodes + 2L * jobs * blocks;
      }
      if (dist[t] >= INF) {
        mc.feasible = false;
        mc.valid = false;
        mc.dual = false;
        return false;
      }
      long dt = dist[t];
      for (int x = 0; x < nodes; x++) {
        pot[x] += Math.min(dist[x], dt);
      }
      // a blocking flow over the arcs of reduced cost 0, which hold every shortest path
      solving = mc;
      Arrays.fill(iter, 0, nodes, 0);
      Arrays.fill(done, 0, nodes, false);
      Arrays.fill(onPath, 0, nodes, false);
      long pushed = augment(s, supply);
      while (pushed > 0) {
        supply -= pushed;
        pushed = supply > 0 ? augment(s, supply) : 0;
      }
    }
    // the dual: u[j] = pot[t] - pot[j], and w[k] the least that keeps it feasible
    long value = 0;
    for (int j = 0; j < jobs; j++) {
      mc.u[j] = pot[t] - pot[j];
      value += durations[mc.task[j]] * mc.u[j];
    }
    for (int k = 0; k < blocks; k++) {
      long wk = 0;
      for (int j = 0; j < jobs; j++) {
        long c = mc.c[j * blocks + k];
        if (c < INF) {
          wk = Math.max(wk, mc.u[j] - c);
        }
      }
      mc.w[k] = wk;
      value -= mc.capacity[k] * wk;
    }
    mc.value = value;
    mc.feasible = true;
    mc.valid = true;
    mc.dual = true;
    return true;
  }

  // the machine being solved, its next arc per node, and the nodes of the current path
  private Machine solving;
  private final int[] iter;
  private final boolean[] onPath;

  /**
   * It sends up to limit units from node v to the sink along arcs of reduced cost 0 with residual
   * capacity, and returns how many it sent; nodes that cannot reach the sink are marked done.
   */
  private long augment(int v, long limit) {
    Machine mc = solving;
    int jobs = mc.jobs;
    int blocks = mc.blocks;
    int t = jobs + blocks;
    int s = t + 1;
    if (v == t) {
      return limit;
    }
    onPath[v] = true;
    int degree = v == s ? jobs : v < jobs ? blocks : jobs + 1;
    for (; iter[v] < degree; iter[v]++) {
      int x = iter[v];
      int to;
      long cap;
      long c;
      if (v == s) {
        to = x;
        cap = mc.rem[x];
        c = 0;
      } else if (v < jobs) {
        to = jobs + x;
        c = mc.c[v * blocks + x];
        cap = c < INF ? INF : 0;
      } else if (x < jobs) {
        to = x;
        cap = mc.flow[x * blocks + (v - jobs)];
        c = -mc.c[x * blocks + (v - jobs)];
      } else {
        to = t;
        cap = mc.capacity[v - jobs] - mc.used[v - jobs];
        c = 0;
      }
      if (cap <= 0 || done[to] || onPath[to] || c + pot[v] - pot[to] != 0) {
        continue;
      }
      long sent = augment(to, Math.min(limit, cap));
      if (sent > 0) {
        if (v == s) {
          mc.rem[x] -= sent;
        } else if (v < jobs) {
          mc.flow[v * blocks + x] += sent;
        } else if (x < jobs) {
          mc.flow[x * blocks + (v - jobs)] -= sent;
        } else {
          mc.used[v - jobs] += sent;
        }
        onPath[v] = false;
        return sent;
      }
    }
    done[v] = true;
    onPath[v] = false;
    return 0;
  }

  private void relax(int from, int to, long d) {
    if (!done[to] && d < dist[to]) {
      dist[to] = d;
      parent[to] = from;
    }
  }

  /**
   * It returns the primal cost of the flow of the last solve of a machine, scaled by {@link
   * #SCALE}; at an optimum it equals {@link #dualValue}.
   *
   * @param m the machine.
   * @return the cost of the flow.
   */
  public long primalValue(int m) {
    Machine mc = machine[m];
    long v = 0;
    for (int a = 0; a < mc.flow.length; a++) {
      if (mc.flow[a] > 0) {
        v += mc.flow[a] * mc.c[a];
      }
    }
    return v;
  }

  /**
   * It returns the dual value of the last solve of a machine, scaled by {@link #SCALE}.
   *
   * @param m the machine.
   * @return the dual value, a lower bound of the scaled cost of the machine.
   */
  public long dualValue(int m) {
    return machine[m].value;
  }

  // the least cost of task i (on no machine) over its bounds
  private long outsideCost(int i) {
    return taskCost(i, Math.max(lo[i], Math.min(hi[i], bestStart[i])));
  }

  /**
   * The bound of the cost for the box lo, hi, reusing the flows still optimal; Long.MAX_VALUE when
   * a machine is overloaded. It fills the certificate when certify is true.
   */
  private long bound(boolean reuse, boolean certify) {
    return bound(reuse, certify, Long.MIN_VALUE);
  }

  /**
   * The bound for the box lo, hi. With reuse, a machine whose last flow is no longer optimal is
   * first bounded by its last dual under the current costs, and solved again only when the flow
   * repaired into the windows costs so much that the exact bounds could exceed max (so they could
   * fail); max Long.MIN_VALUE solves always.
   */
  private long bound(boolean reuse, boolean certify, long max) {
    boolean approximate = false;
    long upper = 0;
    for (int m = 0; m < machine.length; m++) {
      Machine mc = machine[m];
      if (mc.off) {
        mc.trivialValue = trivialScaled(mc);
        upper = add(upper, mc.trivialValue);
        continue;
      }
      fillCosts(m);
      mc.trivialValue = trivialScaled(mc);
      if (reuse && stillOptimal(mc)) {
        mc.lower = mc.value;
        mc.approximate = false;
        upper = add(upper, Math.max(mc.value, mc.trivialValue));
      } else if (reuse && mc.dual && max != Long.MIN_VALUE) {
        mc.valid = false;
        mc.lower = dualUnderCurrent(mc);
        mc.approximate = true;
        approximate = true;
        upper = add(upper, Math.max(repairedCost(mc), mc.trivialValue));
      } else {
        if (!exact(mc, m)) {
          return Long.MAX_VALUE;
        }
        upper = add(upper, Math.max(mc.value, mc.trivialValue));
      }
    }
    long outsideTotal = 0;
    for (int i : outside) {
      outsideTotal += outsideCost(i);
    }
    if (approximate
        && (upper >= INF || ceilScaled(upper) + outsideTotal > max)
        && (!adaptive || (eligible++ % stride == 0 && withinBudget()))) {
      // the bound could exceed the maximum: solve the machines exactly
      for (int m = 0; m < machine.length; m++) {
        Machine mc = machine[m];
        if (!mc.off && mc.approximate && !exact(mc, m)) {
          forcedSolve = adaptive;
          return Long.MAX_VALUE;
        }
      }
      if (adaptive) {
        forcedSolves++;
        forcedSolve = true;
      }
    }
    long scaled = 0;
    for (Machine mc : machine) {
      if (mc.off) {
        mc.trivial = true;
        scaled += mc.trivialValue;
      } else {
        mc.trivial = mc.lower <= mc.trivialValue;
        scaled += Math.max(mc.lower, mc.trivialValue);
      }
    }
    long total = ceilScaled(scaled) + outsideTotal;
    if (certify) {
      certify();
    }
    return total;
  }

  // whether the solves so far took less than their share of the work (always without a budget)
  private boolean withinBudget() {
    return WORK <= 0 || work <= WORK * propagations;
  }

  private static long add(long a, long b) {
    return a >= INF || b >= INF ? INF : a + b;
  }

  private static long ceilScaled(long scaled) {
    return scaled <= 0 ? 0 : (scaled + SCALE - 1) / SCALE;
  }

  // the exact minima of the tasks a machine owns, scaled
  private long trivialScaled(Machine mc) {
    long trivial = 0;
    for (int i : mc.owned) {
      trivial += SCALE * outsideCost(i);
    }
    return trivial;
  }

  // it solves a machine with the current costs; false when it is overloaded
  private boolean exact(Machine mc, int m) {
    if (!solve(m)) {
      return false;
    }
    mc.lower = mc.value;
    mc.approximate = false;
    if (adaptive) {
      mc.solves++;
      if (mc.value > mc.trivialValue) {
        mc.wins++;
      } else if (mc.solves >= TRIAL && mc.wins == 0) {
        // the assignment never beat the exact minima of the tasks
        mc.off = true;
      }
    }
    return true;
  }

  /**
   * The bound of the cost for the starts within [lo, hi] (inclusive). It solves every machine. For
   * tests.
   *
   * @param low the lower bounds of the starts.
   * @param high the upper bounds of the starts.
   * @return the bound, or Long.MAX_VALUE when a machine cannot hold its tasks even with preemption.
   */
  public long boundFor(long[] low, long[] high) {
    System.arraycopy(low, 0, lo, 0, n);
    System.arraycopy(high, 0, hi, 0, n);
    certificateValid = false;
    for (Machine mc : machine) {
      mc.valid = false;
    }
    return bound(false, false);
  }

  // the weakest bounds of the starts that keep the duals of the last solves feasible
  private void certify() {
    for (int i = 0; i < n; i++) {
      needLo[i] = Long.MIN_VALUE;
      needHi[i] = Long.MAX_VALUE;
    }
    for (int m = 0; m < machine.length; m++) {
      Machine mc = machine[m];
      if (mc.trivial) {
        for (int i : mc.owned) {
          exactNeed(i);
        }
        continue;
      }
      for (int j = 0; j < mc.jobs; j++) {
        int i = mc.task[j];
        long p = durations[i];
        boolean counted = owner[i] == m && hasCost[i];
        long wl = lo[i];
        long wh = hi[i] + p - 1;
        // down from the block of the first slot of the window
        int k = (int) ((wl - mc.first) / mc.length);
        long reach = wl;
        while (k >= 0 && fits(mc, j, i, k, counted)) {
          reach = mc.start(k);
          k--;
        }
        long need = k < 0 ? Long.MIN_VALUE : reach;
        needLo[i] = Math.max(needLo[i], need);
        k = (int) ((wh - mc.first) / mc.length);
        reach = wh;
        while (k < mc.blocks && fits(mc, j, i, k, counted)) {
          reach = mc.end(k) - 1;
          k++;
        }
        need = k >= mc.blocks ? Long.MAX_VALUE : reach - p + 1;
        needHi[i] = Math.min(needHi[i], need);
      }
    }
    for (int i : outside) {
      exactNeed(i);
    }
  }

  // the bound of the start that the exact minimum of task i over its bounds depends on
  private void exactNeed(int i) {
    if (bestStart[i] < lo[i]) {
      needLo[i] = Math.max(needLo[i], lo[i]);
    }
    if (bestStart[i] > hi[i]) {
      needHi[i] = Math.min(needHi[i], hi[i]);
    }
  }

  // whether the dual stays feasible with all of block k in the window of job j
  private boolean fits(Machine mc, int j, int i, int k, boolean counted) {
    long c = counted ? leastSlotCost(i, mc.start(k), mc.end(k) - 1) : 0;
    return mc.u[j] - c <= mc.w[k];
  }

  // ---------------------------------------------------------------- propagation

  @Override
  public void consistency(Store store) {
    boolean ground = true;
    for (int i = 0; i < n; i++) {
      lo[i] = starts[i].min();
      hi[i] = starts[i].max();
      ground &= lo[i] == hi[i];
    }
    if (ground) {
      long total = groundCost();
      if (total > cost.max()) {
        throw Store.failException;
      }
      if (total > cost.min()) {
        certificateValid = false;
        cost.domain.inMin(store.level, cost, (int) total);
      }
      return;
    }
    adaptive = TRIAL > 0;
    forcedSolve = false;
    propagations = store.numberConsistencyCalls;
    long bound = bound(true, true, cost.max());
    adaptive = false;
    if (forcedSolve && bound > cost.max()) {
      forcedFails++;
      stride = 1;
    }
    if (forcedSolves >= FORCED_ROUND) {
      // a round without a failure makes the forced solves sparse
      stride = forcedFails == 0 ? SPARSE : 1;
      forcedSolves = 0;
      forcedFails = 0;
    }
    if (bound > cost.max()) {
      certificateValid = bound != Long.MAX_VALUE;
      certifiedBound = bound;
      throw Store.failException;
    }
    certificateValid = true;
    certifiedBound = bound;
    if (bound > cost.min()) {
      cost.domain.inMin(store.level, cost, (int) bound);
    }
  }

  // the exact cost of a ground schedule; fails if two tasks of a machine overlap
  private long groundCost() {
    for (int[] tasks : machines) {
      Integer[] order = new Integer[tasks.length];
      for (int k = 0; k < tasks.length; k++) {
        order[k] = tasks[k];
      }
      Arrays.sort(order, (a, b) -> Long.compare(lo[a], lo[b]));
      for (int k = 1; k < order.length; k++) {
        if (lo[order[k - 1]] + durations[order[k - 1]] > lo[order[k]]) {
          throw Store.failException;
        }
      }
    }
    long total = 0;
    for (int i = 0; i < n; i++) {
      total += taskCost(i, lo[i]);
    }
    return total;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    for (int i = 0; i < n; i++) {
      if (!starts[i].singleton()) {
        return false;
      }
      lo[i] = starts[i].value();
      hi[i] = lo[i];
    }
    try {
      return groundCost() <= cost.min();
    } catch (org.jacop.core.FailException e) {
      return false;
    }
  }

  // ---------------------------------------------------------------- explanations

  // whether the certificate's bounds held before a position
  private boolean certificateHolds(AtomicTrail trail, int position) {
    for (int i = 0; i < n; i++) {
      if ((needLo[i] != Long.MIN_VALUE && trail.minBefore(starts[i], position) < needLo[i])
          || (needHi[i] != Long.MAX_VALUE && trail.maxBefore(starts[i], position) > needHi[i])) {
        return false;
      }
    }
    return true;
  }

  private void addCertificate(AtomicTrail trail, int position, EntryList reason) {
    for (int i = 0; i < n; i++) {
      if (needLo[i] != Long.MIN_VALUE) {
        trail.addBoundReaching(starts[i], position, true, needLo[i], reason);
      }
      if (needHi[i] != Long.MAX_VALUE) {
        trail.addBoundReaching(starts[i], position, false, needHi[i], reason);
      }
    }
  }

  // a certificate for the bounds before a position, solving again; the bound it proves
  private long recertify(AtomicTrail trail, int position) {
    for (int i = 0; i < n; i++) {
      lo[i] = trail.minBefore(starts[i], position);
      hi[i] = trail.maxBefore(starts[i], position);
    }
    for (Machine mc : machine) {
      mc.valid = false;
    }
    long b = bound(false, true);
    // the flows are now of an older box; the next propagation solves again
    for (Machine mc : machine) {
      mc.valid = false;
    }
    certificateValid = b != Long.MAX_VALUE;
    certifiedBound = b;
    return b;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList reason) {
    if (trail.kind(entry) != AtomicTrail.GE || trail.variable(entry) != cost) {
      return false;
    }
    int value = trail.skippedBound(entry);
    if (!(certificateValid && certifiedBound >= value && certificateHolds(trail, entry))) {
      long b = recertify(trail, entry);
      if (b == Long.MAX_VALUE || b < value || !certificateHolds(trail, entry)) {
        return false;
      }
    }
    trail.addSkippedHoles(entry, value, reason);
    addCertificate(trail, entry, reason);
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList reason) {
    int now = trail.size();
    long max = trail.maxBefore(cost, now);
    if (!(certificateValid && certifiedBound > max && certificateHolds(trail, now))) {
      long b = recertify(trail, now);
      if (b == Long.MAX_VALUE || b <= max || !certificateHolds(trail, now)) {
        return false;
      }
    }
    long room = certifiedBound - max - 1;
    trail.addBoundWithin(cost, now, false, room, reason);
    addCertificate(trail, now, reason);
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : UnaryEarlinessTardiness([");
    for (int i = 0; i < n; i++) {
      result.append(starts[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(Arrays.toString(durations));
    result.append(", ").append(Arrays.deepToString(machines));
    result.append(", ").append(Arrays.toString(owner));
    result.append(", ").append(Arrays.deepToString(terms));
    result.append(", ").append(cost).append(")");
    return result.toString();
  }

  @Override
  public UnaryEarlinessTardiness copy(VarMap map) {
    return new UnaryEarlinessTardiness(
        map.get(starts), durations, machines, owner, terms, map.get(cost));
  }
}
