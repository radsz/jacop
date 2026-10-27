/*
 * UnaryTransition.java
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

package org.jacop.constraints.cumulative;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * UnaryTransition is a unary resource (disjunctive constraint) with sequence-dependent transition
 * (setup) times: the tasks run one at a time, and between a task of family f and the next task of
 * family g the resource is idle for at least {@code transitions[f][g]}. For every two tasks i and j
 * it holds that
 *
 * <pre>
 *   s[i] + d[i] + transitions[family[i]][family[j]] &lt;= s[j]
 *   \/ s[j] + d[j] + transitions[family[j]][family[i]] &lt;= s[i],
 * </pre>
 *
 * also for tasks of zero duration, which are visits of the resource that need their transitions
 * too. Two tasks of the same family f are separated by {@code transitions[f][f]}, usually zero.
 *
 * <p>Propagation, after Dejemeppe, Van Cauwelaert and Schaus, "The Unary Resource with Transition
 * Times", CP 2015, and Van Cauwelaert, Dejemeppe and Schaus, "An Efficient Filtering Algorithm for
 * the Unary Resource Constraint with Transition Times and Optional Activities", Journal of
 * Scheduling 23, 2020:
 *
 * <ul>
 *   <li>each pair of tasks: a task that cannot precede the other follows it, with the transition;
 *   <li>the overload check, detectable precedences, not-last and edge finding of Vilím on both
 *       views, in O(n log n log f) with f families (see {@link TransitionReasoning}). Their
 *       earliest completion times count {@code tt(k)}, a lower bound of the total transition time
 *       of any k distinct families: exact (by dynamic programming over subsets) for at most 13
 *       families, otherwise the larger of the lightest forest of k - 1 edges and the shortest walk
 *       of k - 1 transitions.
 * </ul>
 *
 * <p>The transitions need not satisfy the triangle inequality: the bounds use only that the time
 * between two tasks is at least the transition time of some path between their families.
 *
 * <p>When only a transition matrix between tasks is given, tasks with the same transitions to and
 * from all other tasks and no transition between themselves form one family, since the bounds are
 * stronger with fewer families.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class UnaryTransition extends Constraint
    implements Copyable<UnaryTransition>, SatisfiedPresent {

  private static final AtomicInteger idNumber = new AtomicInteger(0);

  // the largest number of families with exact bounds tt(k)
  static final int EXACT_FAMILIES = 13;

  // the largest number of families for the shortest walk bound, which costs f^3
  private static final int WALK_FAMILIES = 200;

  // the largest number of families for the forest bound, which sorts f^2 edges
  private static final int FOREST_FAMILIES = 2000;

  final IntVar[] starts;
  final IntVar[] durations;
  final int[] family;
  final int[][] transitions;

  // the rules on the trees, for tests
  static final int OVERLOAD = 1;
  static final int DETECTABLE = 2;
  static final int NOT_LAST = 4;
  static final int EDGE_FIND = 8;
  int rules = OVERLOAD | DETECTABLE | NOT_LAST | EDGE_FIND;

  // the presence of each task (0 or 1), or null when every task is present
  final IntVar[] optional;

  private final int n;
  // the family of each task among the families used, numbered from 0
  private final int[] famOfTask;
  // the rules on the present tasks; position k of a view holds task taskAt[k]
  private final TransitionReasoning normal;
  private final TransitionReasoning reversed;
  private final int[] taskAt;
  private int loaded;
  private boolean changedByRules;
  // the rules on the present and the optional tasks, normal view only
  private final TransitionReasoning withOptional;
  private final int[] optionalTaskAt;

  /**
   * It creates a unary resource with transition times between families of tasks.
   *
   * @param starts the starts of the tasks.
   * @param durations the durations of the tasks, not negative.
   * @param family the family of each task, from 0 to the number of families minus one.
   * @param transitions the transition time from each family to each family, not negative.
   */
  public UnaryTransition(IntVar[] starts, IntVar[] durations, int[] family, int[][] transitions) {
    this(starts, durations, family, transitions, null);
  }

  /**
   * It creates a unary resource with transition times between families of optional tasks: the
   * transitions hold between every two present tasks; an absent task does not use the resource.
   *
   * @param starts the starts of the tasks.
   * @param durations the durations of the tasks, not negative.
   * @param family the family of each task, from 0 to the number of families minus one.
   * @param transitions the transition time from each family to each family, not negative.
   * @param optional the presence of each task, 0 or 1; null when every task is present.
   */
  public UnaryTransition(
      IntVar[] starts, IntVar[] durations, int[] family, int[][] transitions, IntVar[] optional) {
    checkInputForNullness(
        new String[] {"starts", "durations", "family", "transitions"},
        starts,
        durations,
        new Object[] {family},
        new Object[] {transitions});
    checkInput(durations, d -> d.min() >= 0, "durations cannot allow negative values");
    if (starts.length != durations.length || starts.length != family.length) {
      throw new IllegalArgumentException(
          "UnaryTransition needs starts, durations and families of the same length.");
    }
    int f = transitions.length;
    for (int[] row : transitions) {
      if (row == null || row.length != f) {
        throw new IllegalArgumentException("UnaryTransition needs a square transition matrix.");
      }
      for (int t : row) {
        if (t < 0) {
          throw new IllegalArgumentException("UnaryTransition needs non-negative transitions.");
        }
      }
    }
    for (int g : family) {
      if (g < 0 || g >= f) {
        throw new IllegalArgumentException(
            "UnaryTransition family " + g + " is not an index of the transition matrix.");
      }
    }
    for (int i = 0; i < starts.length; i++) {
      Math.addExact(Math.addExact(starts[i].max(), durations[i].max()), maxEntry(transitions));
    }

    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 2;
    this.starts = starts.clone();
    this.durations = durations.clone();
    this.family = family.clone();
    this.transitions = new int[f][];
    for (int g = 0; g < f; g++) {
      this.transitions[g] = transitions[g].clone();
    }
    this.n = starts.length;
    if (optional != null) {
      this.optional = ProfileOptional.checkOptional(optional, n, "UnaryTransition");
    } else {
      this.optional = null;
    }

    // the families used by the tasks, renumbered, so that the bounds count only those
    int[] used = new int[f];
    Arrays.fill(used, -1);
    int k = 0;
    int[] fam = new int[n];
    for (int i = 0; i < n; i++) {
      if (used[family[i]] < 0) {
        used[family[i]] = k++;
      }
      fam[i] = used[family[i]];
    }
    int[][] tt = new int[k][k];
    int[][] ttReversed = new int[k][k];
    for (int a = 0; a < f; a++) {
      for (int b = 0; b < f; b++) {
        if (used[a] >= 0 && used[b] >= 0) {
          tt[used[a]][used[b]] = transitions[a][b];
          ttReversed[used[b]][used[a]] = transitions[a][b];
        }
      }
    }
    long[] ttk = familyBounds(tt);
    famOfTask = fam;
    normal = new TransitionReasoning(n, tt, ttk);
    reversed = new TransitionReasoning(n, ttReversed, ttk);
    taskAt = new int[n];
    if (this.optional != null) {
      withOptional = new TransitionReasoning(n, tt, ttk);
      optionalTaskAt = new int[n];
      setScope(
          Stream.concat(
              Stream.concat(Arrays.stream(starts), Arrays.stream(durations)),
              Arrays.stream(this.optional)));
    } else {
      withOptional = null;
      optionalTaskAt = null;
      setScope(Stream.concat(Arrays.stream(starts), Arrays.stream(durations)));
    }
  }

  /**
   * It creates a unary resource with transition times between tasks. Tasks with equal transitions
   * to and from all other tasks and zero transitions between themselves are grouped in a family.
   *
   * @param starts the starts of the tasks.
   * @param durations the durations of the tasks, not negative.
   * @param transitions the transition time from each task to each task, not negative; the diagonal
   *     is not used.
   */
  public UnaryTransition(IntVar[] starts, IntVar[] durations, int[][] transitions) {
    this(starts, durations, families(transitions), familyMatrix(transitions));
  }

  /**
   * It creates a unary resource with transition times between families of tasks.
   *
   * @param starts the starts of the tasks.
   * @param durations the durations of the tasks, not negative.
   * @param family the family of each task, from 0 to the number of families minus one.
   * @param transitions the transition time from each family to each family, not negative.
   */
  public UnaryTransition(
      List<? extends IntVar> starts,
      List<? extends IntVar> durations,
      int[] family,
      int[][] transitions) {
    this(starts.toArray(IntVar[]::new), durations.toArray(IntVar[]::new), family, transitions);
  }

  private static int maxEntry(int[][] m) {
    int max = 0;
    for (int[] row : m) {
      for (int t : row) {
        max = Math.max(max, t);
      }
    }
    return max;
  }

  /**
   * It groups tasks into families: two tasks are in one family when there is no transition between
   * them and their transitions to and from every other task are equal.
   *
   * @param tt the transitions between tasks.
   * @return the family of each task.
   */
  static int[] families(int[][] tt) {
    int n = tt.length;
    for (int[] row : tt) {
      if (row == null || row.length != n) {
        throw new IllegalArgumentException("UnaryTransition needs a square transition matrix.");
      }
    }
    int[] fam = new int[n];
    Arrays.fill(fam, -1);
    int k = 0;
    for (int i = 0; i < n; i++) {
      if (fam[i] >= 0) {
        continue;
      }
      fam[i] = k;
      for (int j = i + 1; j < n; j++) {
        if (fam[j] < 0 && sameFamily(tt, i, j)) {
          fam[j] = k;
        }
      }
      k++;
    }
    return fam;
  }

  private static boolean sameFamily(int[][] tt, int i, int j) {
    if (tt[i][j] != 0 || tt[j][i] != 0) {
      return false;
    }
    for (int x = 0; x < tt.length; x++) {
      if (x != i && x != j && (tt[i][x] != tt[j][x] || tt[x][i] != tt[x][j])) {
        return false;
      }
    }
    return true;
  }

  private static int[][] familyMatrix(int[][] tt) {
    int[] fam = families(tt);
    int k = 0;
    for (int f : fam) {
      k = Math.max(k, f + 1);
    }
    int[] representative = new int[k];
    Arrays.fill(representative, -1);
    for (int i = 0; i < fam.length; i++) {
      if (representative[fam[i]] < 0) {
        representative[fam[i]] = i;
      }
    }
    int[][] m = new int[k][k];
    for (int a = 0; a < k; a++) {
      for (int b = 0; b < k; b++) {
        // two tasks of one family have no transition
        m[a][b] = a == b ? 0 : tt[representative[a]][representative[b]];
      }
    }
    return m;
  }

  /**
   * It computes tt(k), a lower bound of the total transition time of a sequence of tasks of k
   * distinct families, for k from 0 to f + 1. The bound is superadditive, tt(a + b - 1) &gt;= tt(a)
   * + tt(b), as the trees require.
   *
   * @param tt the transitions between families.
   * @return the bounds.
   */
  static long[] familyBounds(int[][] tt) {
    int f = tt.length;
    long[] bound = new long[f + 2];
    if (f <= 1) {
      return bound;
    }
    if (f <= EXACT_FAMILIES) {
      exactBounds(tt, bound);
    } else {
      long[] forest = f <= FOREST_FAMILIES ? forestBounds(tt) : new long[f + 1];
      long[] walk = f <= WALK_FAMILIES ? walkBounds(tt) : new long[f + 1];
      // one of them, not their maximum, which need not be superadditive
      long[] best = sum(walk) > sum(forest) ? walk : forest;
      System.arraycopy(best, 0, bound, 0, f + 1);
    }
    bound[f + 1] = bound[f];
    return bound;
  }

  private static long sum(long[] a) {
    long s = 0;
    for (long x : a) {
      s += x;
    }
    return s;
  }

  // the cheapest path visiting k distinct families, over the shortest paths between families
  private static void exactBounds(int[][] tt, long[] bound) {
    int f = tt.length;
    long[][] dist = new long[f][f];
    for (int a = 0; a < f; a++) {
      for (int b = 0; b < f; b++) {
        dist[a][b] = tt[a][b];
      }
    }
    for (int c = 0; c < f; c++) {
      for (int a = 0; a < f; a++) {
        for (int b = 0; b < f; b++) {
          dist[a][b] = Math.min(dist[a][b], dist[a][c] + dist[c][b]);
        }
      }
    }
    long inf = Long.MAX_VALUE / 4;
    long[][] path = new long[1 << f][f];
    for (long[] row : path) {
      Arrays.fill(row, inf);
    }
    Arrays.fill(bound, inf);
    for (int a = 0; a < f; a++) {
      path[1 << a][a] = 0;
    }
    for (int mask = 1; mask < 1 << f; mask++) {
      int k = Integer.bitCount(mask);
      for (int a = 0; a < f; a++) {
        long p = path[mask][a];
        if (p >= inf) {
          continue;
        }
        bound[k] = Math.min(bound[k], p);
        for (int b = 0; b < f; b++) {
          if ((mask & (1 << b)) == 0) {
            int next = mask | (1 << b);
            path[next][b] = Math.min(path[next][b], p + dist[a][b]);
          }
        }
      }
    }
    bound[0] = 0;
  }

  // the lightest forest of k - 1 edges, by Kruskal, with the lighter direction of each pair
  static long[] forestBounds(int[][] tt) {
    int f = tt.length;
    long[] edges = new long[f * (f - 1) / 2];
    int m = 0;
    for (int a = 0; a < f; a++) {
      for (int b = a + 1; b < f; b++) {
        long w = Math.min(tt[a][b], tt[b][a]);
        edges[m++] = (w << 32) | ((long) a << 16) | b;
      }
    }
    Arrays.sort(edges);
    int[] parent = new int[f];
    for (int a = 0; a < f; a++) {
      parent[a] = a;
    }
    long[] bound = new long[f + 1];
    int k = 1;
    for (int e = 0; e < m && k < f; e++) {
      int a = root(parent, (int) ((edges[e] >>> 16) & 0xFFFF));
      int b = root(parent, (int) (edges[e] & 0xFFFF));
      if (a != b) {
        parent[a] = b;
        bound[k + 1] = bound[k] + (edges[e] >>> 32);
        k++;
      }
    }
    return bound;
  }

  private static int root(int[] parent, int a) {
    while (parent[a] != a) {
      parent[a] = parent[parent[a]];
      a = parent[a];
    }
    return a;
  }

  // the shortest walk of k - 1 transitions between different families
  static long[] walkBounds(int[][] tt) {
    int f = tt.length;
    long[] bound = new long[f + 1];
    long[] walk = new long[f];
    long[] next = new long[f];
    for (int k = 2; k <= f; k++) {
      long best = Long.MAX_VALUE;
      for (int b = 0; b < f; b++) {
        long w = Long.MAX_VALUE;
        for (int a = 0; a < f; a++) {
          if (a != b) {
            w = Math.min(w, walk[a] + tt[a][b]);
          }
        }
        next[b] = w;
        best = Math.min(best, w);
      }
      long[] swap = walk;
      walk = next;
      next = swap;
      bound[k] = best;
    }
    return bound;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {
    if (n < 2) {
      return;
    }
    super.impose(store);
  }

  @Override
  public void consistency(Store store) {
    boolean changed = store.propagationHasOccurred;
    do {
      store.propagationHasOccurred = false;
      pairs(store);
      rules(store);
      changed |= store.propagationHasOccurred;
    } while (store.propagationHasOccurred);
    store.propagationHasOccurred = changed;
  }

  private int transition(int i, int j) {
    return transitions[family[i]][family[j]];
  }

  /**
   * Each pair of tasks: a task that cannot precede the other follows it.
   *
   * @param store the constraint store.
   */
  void pairs(Store store) {
    for (int i = 0; i < n; i++) {
      if (!possible(i)) {
        continue;
      }
      for (int j = i + 1; j < n; j++) {
        if (!possible(j)) {
          continue;
        }
        IntVar si = starts[i];
        IntVar sj = starts[j];
        boolean iFirst = (long) si.min() + durations[i].min() + transition(i, j) <= sj.max();
        boolean jFirst = (long) sj.min() + durations[j].min() + transition(j, i) <= si.max();
        if (iFirst && jFirst) {
          continue;
        }
        boolean pi = present(i);
        boolean pj = present(j);
        if (!pi || !pj) {
          // one of the two is optional: with no order left, it is absent if the other is present
          if (!iFirst && !jFirst) {
            if (pi) {
              optional[j].domain.inMax(store.level, optional[j], 0);
            } else if (pj) {
              optional[i].domain.inMax(store.level, optional[i], 0);
            }
          }
          continue;
        }
        if (!iFirst && !jFirst) {
          throw Store.failException;
        }
        if (!iFirst) {
          precede(store, j, i);
        } else {
          precede(store, i, j);
        }
      }
    }
  }

  private boolean present(int i) {
    return optional == null || optional[i].min() == 1;
  }

  private boolean possible(int i) {
    return optional == null || optional[i].max() == 1;
  }

  // task a precedes task b
  private void precede(Store store, int a, int b) {
    int t = transition(a, b);
    IntVar sa = starts[a];
    IntVar sb = starts[b];
    IntVar da = durations[a];
    sb.domain.inMin(store.level, sb, sa.min() + da.min() + t);
    sa.domain.inMax(store.level, sa, sb.max() - da.min() - t);
    da.domain.inMax(store.level, da, sb.max() - sa.min() - t);
  }

  private void rules(Store store) {
    if (store.propagationHasOccurred || rules == 0) {
      return;
    }
    if (optional != null && optionalRules(store)) {
      return;
    }
    load();
    if (loaded == 0) {
      return;
    }
    changedByRules = false;
    if ((rules & OVERLOAD) != 0) {
      normal.overload();
    }
    if ((rules & DETECTABLE) != 0) {
      normal.detectable();
      applyEst(store, normal);
      reloadIfChanged(store);
      reversed.detectable();
      applyReversedEst(store);
      reloadIfChanged(store);
    }
    if ((rules & NOT_LAST) != 0) {
      normal.notLast();
      applyLct(store, normal);
      reloadIfChanged(store);
      reversed.notLast();
      applyReversedLct(store);
      reloadIfChanged(store);
    }
    if ((rules & EDGE_FIND) != 0) {
      normal.edgeFind();
      applyEst(store, normal);
      reloadIfChanged(store);
      reversed.edgeFind();
      applyReversedEst(store);
    }
    // the pairs and the rules run again after any change
    store.propagationHasOccurred |= changedByRules;
  }

  // each rule sees the bounds of the rules before it
  private void reloadIfChanged(Store store) {
    if (store.propagationHasOccurred) {
      store.propagationHasOccurred = false;
      changedByRules = true;
      load();
    }
  }

  // loads the present tasks into both views
  private void load() {
    TransitionReasoning a = normal;
    TransitionReasoning b = reversed;
    int k = 0;
    for (int i = 0; i < n; i++) {
      if (!present(i)) {
        continue;
      }
      taskAt[k] = i;
      int sMin = starts[i].min();
      int sMax = starts[i].max();
      int dMin = durations[i].min();
      a.fam[k] = famOfTask[i];
      a.est[k] = sMin;
      a.lst[k] = sMax;
      a.lct[k] = sMax + durations[i].max();
      a.ect[k] = sMin + dMin;
      a.dur[k] = dMin;
      // the reversed task runs from -(sMax + dMax) to -sMin
      b.fam[k] = famOfTask[i];
      b.est[k] = -a.lct[k];
      b.lct[k] = -sMin;
      b.dur[k] = dMin;
      b.lst[k] = b.lct[k] - dMin;
      b.ect[k] = b.est[k] + dMin;
      k++;
    }
    loaded = k;
    a.sort(k);
    b.sort(k);
  }

  /**
   * The overload check and edge finding with the optional tasks that may still be present: an
   * optional task that would overload the present ones, or would have to start after its latest
   * start, is absent.
   *
   * @param store the constraint store.
   * @return true if some domain changed.
   */
  private boolean optionalRules(Store store) {
    TransitionReasoning o = withOptional;
    int k = 0;
    boolean undecided = false;
    for (int i = 0; i < n; i++) {
      if (!possible(i)) {
        continue;
      }
      optionalTaskAt[k] = i;
      int sMin = starts[i].min();
      int sMax = starts[i].max();
      int dMin = durations[i].min();
      o.gray[k] = !present(i);
      undecided |= o.gray[k];
      o.fam[k] = famOfTask[i];
      o.est[k] = sMin;
      o.lst[k] = sMax;
      o.lct[k] = sMax + durations[i].max();
      o.ect[k] = sMin + dMin;
      o.dur[k] = dMin;
      k++;
    }
    if (!undecided) {
      return false;
    }
    o.sort(k);
    if ((rules & OVERLOAD) != 0) {
      o.optionalOverload();
      markAbsent(store, o, k);
      if (store.propagationHasOccurred) {
        return true;
      }
    }
    if ((rules & EDGE_FIND) != 0) {
      o.edgeFind();
      markAbsent(store, o, k);
      for (int p = 0; p < k; p++) {
        int i = optionalTaskAt[p];
        if (!o.gray[p] && o.update[p] > starts[i].min()) {
          starts[i].domain.inMin(store.level, starts[i], clamp(o.update[p]));
        }
      }
    }
    return store.propagationHasOccurred;
  }

  private void markAbsent(Store store, TransitionReasoning o, int k) {
    for (int p = 0; p < k; p++) {
      if (o.absent[p]) {
        IntVar b = optional[optionalTaskAt[p]];
        b.domain.inMax(store.level, b, 0);
      }
    }
  }

  private static int clamp(long v) {
    return (int) Math.max(IntDomain.MIN_INT, Math.min(IntDomain.MAX_INT, v));
  }

  private void applyEst(Store store, TransitionReasoning view) {
    for (int k = 0; k < loaded; k++) {
      IntVar s = starts[taskAt[k]];
      if (view.update[k] > s.min()) {
        s.domain.inMin(store.level, s, clamp(view.update[k]));
      }
    }
  }

  private void applyLct(Store store, TransitionReasoning view) {
    for (int k = 0; k < loaded; k++) {
      int i = taskAt[k];
      long max = view.update[k] - durations[i].min();
      if (max < starts[i].max()) {
        starts[i].domain.inMax(store.level, starts[i], clamp(max));
      }
    }
  }

  // an est of the reversed view is a latest completion of the normal view
  private void applyReversedEst(Store store) {
    for (int k = 0; k < loaded; k++) {
      int i = taskAt[k];
      long max = -reversed.update[k] - durations[i].min();
      if (max < starts[i].max()) {
        starts[i].domain.inMax(store.level, starts[i], clamp(max));
      }
    }
  }

  // an lct of the reversed view is an earliest start of the normal view
  private void applyReversedLct(Store store) {
    for (int k = 0; k < loaded; k++) {
      int i = taskAt[k];
      long min = -reversed.update[k];
      if (min > starts[i].min()) {
        starts[i].domain.inMin(store.level, starts[i], clamp(min));
      }
    }
  }

  @Override
  public boolean satisfied() {
    for (int i = 0; i < n; i++) {
      if (!starts[i].singleton()
          || !durations[i].singleton()
          || optional != null && !optional[i].singleton()) {
        return false;
      }
    }
    for (int i = 0; i < n; i++) {
      if (!present(i)) {
        continue;
      }
      for (int j = i + 1; j < n; j++) {
        if (!present(j)) {
          continue;
        }
        long si = starts[i].value();
        long sj = starts[j].value();
        if (si + durations[i].value() + transition(i, j) > sj
            && sj + durations[j].value() + transition(j, i) > si) {
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : unaryTransition([");
    for (int i = 0; i < n; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result
          .append("[")
          .append(starts[i])
          .append(", ")
          .append(durations[i])
          .append(", ")
          .append(family[i]);
      if (optional != null) {
        result.append(", ").append(optional[i]);
      }
      result.append("]");
    }
    result.append("], transitions = ").append(Arrays.deepToString(transitions)).append(")");
    return result.toString();
  }

  @Override
  public UnaryTransition copy(VarMap map) {
    IntVar[] s = new IntVar[n];
    IntVar[] d = new IntVar[n];
    for (int i = 0; i < n; i++) {
      s[i] = map.get(starts[i]);
      d[i] = map.get(durations[i]);
    }
    IntVar[] o = null;
    if (optional != null) {
      o = new IntVar[n];
      for (int i = 0; i < n; i++) {
        o[i] = map.get(optional[i]);
      }
    }
    return new UnaryTransition(s, d, family, transitions, o);
  }
}
