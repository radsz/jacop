/*
 * MaxCliqueBound.java
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
 * The coloring bound of maximum clique on {@code sum <= x[0] + ... + x[n-1]} for 0/1 variables of
 * which no two in conflict can both be 1 ({@code x[i] + x[j] <= 1} for every conflict). The
 * constraint holds when the sum is at most the number of ones and no two ones are in conflict. Its
 * propagation sets to 0 the vertices in conflict with a 1, as the pairwise constraints do, and
 * bounds the sum from above; it is meant as a redundant constraint next to those pairwise
 * constraints and to the definition of the sum. The variables that can still be 1 form a graph
 * whose edges join the vertices not in conflict; any proper coloring of it splits them into classes
 * of vertices pairwise in conflict, at most one of which is 1, so the number of classes bounds the
 * sum. The classes come from a greedy sequential coloring over bit sets, vertices in decreasing
 * degree order, as in the branch and bound of maximum clique algorithms: E. Tomita and T. Seki, An
 * efficient branch-and-bound algorithm for finding a maximum clique, DMTCS 2003, LNCS 2731 (MCQ);
 * E. Tomita, Y. Sutani, T. Higashi, S. Takahashi and M. Wakatsuki, A simple and faster
 * branch-and-bound algorithm for finding a maximum clique, WALCOM 2010, LNCS 5942 (MCS); P. San
 * Segundo, D. Rodríguez-Losada and A. Jiménez, An exact bit-parallel algorithm for the maximum
 * clique problem, Computers &amp; Operations Research 38(2), 2011 (BBMC). J.-C. Régin, Using
 * constraint programming to solve the maximum clique problem, CP 2003, LNCS 2833, posts the same
 * bound as a constraint.
 *
 * <p>The bound depends only on the variables that are 0, since every class holds at most one 1
 * whatever the other variables are. Its reason for lazy clause generation is the set of those
 * variables at 0 that the coloring needs: a variable at 0 that is in conflict with every member of
 * some class joins it, and then its 0 is not cited. A variable at 1 stands for the zeros of all the
 * vertices in conflict with it, so the zeros it covers are cited through it, as the current clique
 * of a branch and bound stands for the vertices it excludes.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class MaxCliqueBound extends Constraint
    implements Copyable<MaxCliqueBound>, Explainable, SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The 0/1 variables, one per vertex. */
  public final IntVar[] x;

  /** The variable at least the sum of x. */
  public final IntVar sum;

  // the conflicts of each vertex, as given
  private final int[][] conflicts;

  // the vertices in decreasing degree order of the graph of the non-conflicts
  private final int[] order;

  // position of each vertex in order: bit p of the sets below is vertex order[p]
  private final int[] position;

  // per position: the positions of the vertices NOT in conflict with it (the graph edges)
  private final long[][] compatible;

  private final int words;

  // scratch sets: the vertices left to color, the candidates of the class being built
  private final long[] left;
  private final long[] candidates;

  // the zeros a reason needs, as positions
  private final long[] needed;

  // the members of each class of the last coloring, as positions
  private long[][] classes;

  /**
   * It creates the bound.
   *
   * @param x the 0/1 variables, one per vertex
   * @param conflicts conflicts[i] lists the vertices j such that x[i] and x[j] cannot both be 1
   * @param sum a variable at least x[0] + ... + x[n-1], such as the maximized objective
   */
  public MaxCliqueBound(IntVar[] x, int[][] conflicts, IntVar sum) {
    checkInputForNullness(new String[] {"x", "sum"}, new Object[][] {x, {sum}});
    if (conflicts.length != x.length) {
      throw new IllegalArgumentException("MaxCliqueBound needs the conflicts of each variable");
    }
    for (IntVar v : x) {
      if (v.min() < 0 || v.max() > 1) {
        throw new IllegalArgumentException("MaxCliqueBound needs 0/1 variables: " + v);
      }
      if (v == sum) {
        throw new IllegalArgumentException("MaxCliqueBound: the sum cannot be a vertex");
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.x = Arrays.copyOf(x, x.length);
    this.sum = sum;
    int n = x.length;
    this.conflicts = new int[n][];
    this.words = (n + 63) >>> 6;
    // conflict[i]: the vertices in conflict with i, by vertex
    long[][] conflict = new long[n][words];
    for (int i = 0; i < n; i++) {
      for (int j : conflicts[i]) {
        if (j < 0 || j >= n) {
          throw new IllegalArgumentException("MaxCliqueBound: no vertex " + j);
        }
        if (j != i) {
          conflict[i][j >>> 6] |= 1L << j;
          conflict[j][i >>> 6] |= 1L << i;
        }
      }
    }
    int[] degree = new int[n];
    for (int i = 0; i < n; i++) {
      int[] list = new int[cardinality(conflict[i])];
      int c = 0;
      for (int w = 0; w < words; w++) {
        for (long bits = conflict[i][w]; bits != 0; bits &= bits - 1) {
          list[c++] = (w << 6) | Long.numberOfTrailingZeros(bits);
        }
      }
      this.conflicts[i] = list;
      degree[i] = n - 1 - list.length;
    }
    Integer[] sorted = new Integer[n];
    for (int i = 0; i < n; i++) {
      sorted[i] = i;
    }
    Arrays.sort(sorted, (a, b) -> degree[a] != degree[b] ? degree[b] - degree[a] : a - b);
    this.order = new int[n];
    this.position = new int[n];
    for (int p = 0; p < n; p++) {
      order[p] = sorted[p];
      position[sorted[p]] = p;
    }
    this.compatible = new long[n][words];
    for (int p = 0; p < n; p++) {
      long[] c = conflict[order[p]];
      for (int q = 0; q < n; q++) {
        if (q != p && (c[order[q] >>> 6] & (1L << order[q])) == 0) {
          compatible[p][q >>> 6] |= 1L << q;
        }
      }
    }
    this.left = new long[words];
    this.candidates = new long[words];
    this.needed = new long[words];
    this.classes = new long[8][words];
    setScope(Stream.concat(Arrays.stream(this.x), Stream.of(sum)));
  }

  private static boolean empty(long[] set) {
    for (long w : set) {
      if (w != 0) {
        return false;
      }
    }
    return true;
  }

  private static int cardinality(long[] set) {
    int c = 0;
    for (long w : set) {
      c += Long.bitCount(w);
    }
    return c;
  }

  /**
   * Colors the vertices of {@code left} greedily, one class at a time: each class takes the first
   * vertex left, then the next vertices left in conflict with all its members. It clears left.
   *
   * @return the number of classes
   */
  private int color() {
    int k = 0;
    while (true) {
      int first = -1;
      for (int w = 0; w < words; w++) {
        if (left[w] != 0) {
          first = w;
          break;
        }
      }
      if (first < 0) {
        return k;
      }
      if (k == classes.length) {
        classes = Arrays.copyOf(classes, 2 * k);
        for (int c = k; c < classes.length; c++) {
          classes[c] = new long[words];
        }
      }
      long[] members = classes[k];
      Arrays.fill(members, 0L);
      System.arraycopy(left, 0, candidates, 0, words);
      for (int w = first; w < words; w++) {
        while (candidates[w] != 0) {
          int b = Long.numberOfTrailingZeros(candidates[w]);
          int p = (w << 6) | b;
          long bit = 1L << b;
          members[w] |= bit;
          left[w] &= ~bit;
          candidates[w] &= ~bit;
          long[] c = compatible[p];
          for (int u = w; u < words; u++) {
            candidates[u] &= ~c[u];
          }
        }
      }
      k++;
    }
  }

  // the number of classes over the vertices that can be 1 now
  private int boundNow() {
    Arrays.fill(left, 0L);
    for (int p = 0; p < x.length; p++) {
      if (x[order[p]].max() > 0) {
        left[p >>> 6] |= 1L << p;
      }
    }
    return color();
  }

  @Override
  public void consistency(Store store) {
    for (int i = 0; i < x.length; i++) {
      if (x[i].min() > 0) {
        for (int j : conflicts[i]) {
          x[j].domain.inMax(store.level, x[j], 0);
        }
      }
    }
    int k = boundNow();
    sum.domain.inMax(store.level, sum, k);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    if (!sum.singleton()) {
      return false;
    }
    long s = 0;
    for (int i = 0; i < x.length; i++) {
      if (!x[i].singleton()) {
        return false;
      }
      if (x[i].value() > 0) {
        for (int j : conflicts[i]) {
          if (x[j].value() > 0) {
            return false;
          }
        }
      }
      s += x[i].value();
    }
    return sum.value() <= s;
  }

  // ---- reasons ---------------------------------------------------------------------------

  /**
   * Colors the vertices that could be 1 just before a trail position and adds to {@code out} the
   * zeros of the other vertices that the coloring needs to keep at most {@code limit} classes.
   *
   * @return false when the coloring needs more than limit classes
   */
  private boolean reason(AtomicTrail trail, int at, long limit, EntryList out) {
    int n = x.length;
    Arrays.fill(needed, 0L);
    Arrays.fill(left, 0L);
    for (int p = 0; p < n; p++) {
      if (trail.maxBefore(x[order[p]], at) > 0) {
        left[p >>> 6] |= 1L << p;
      }
    }
    int k = color();
    if (k > limit) {
      return false;
    }
    // a zero in conflict with every member of a class joins it, and is then not needed
    for (int p = 0; p < n; p++) {
      IntVar v = x[order[p]];
      if (trail.maxBefore(v, at) > 0) {
        continue;
      }
      long[] c = compatible[p];
      boolean joined = false;
      for (int j = 0; j < k && !joined; j++) {
        long[] members = classes[j];
        boolean disjoint = true;
        for (int w = 0; w < words && disjoint; w++) {
          disjoint = (members[w] & c[w]) == 0;
        }
        if (disjoint) {
          members[p >>> 6] |= 1L << p;
          joined = true;
        }
      }
      if (!joined) {
        needed[p >>> 6] |= 1L << p;
      }
    }
    // a 1 holds every vertex in conflict with it at 0: cite the ones that cover needed zeros, the
    // vertices first in the order (largest degree) first, then the zeros no 1 covers
    for (int p = 0; p < n && !empty(needed); p++) {
      int i = order[p];
      if (trail.minBefore(x[i], at) <= 0) {
        continue;
      }
      boolean covers = false;
      for (int j : conflicts[i]) {
        int q = position[j];
        long bit = 1L << q;
        if ((needed[q >>> 6] & bit) != 0) {
          needed[q >>> 6] &= ~bit;
          covers = true;
        }
      }
      if (covers) {
        trail.addLowerBound(x[i], at, out);
      }
    }
    for (int w = 0; w < words; w++) {
      for (long bits = needed[w]; bits != 0; bits &= bits - 1) {
        trail.addUpperBound(x[order[(w << 6) | Long.numberOfTrailingZeros(bits)]], at, out);
      }
      needed[w] = 0;
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    if (y != sum) {
      return conflictReason(trail, entry, y, out);
    }
    if (trail.kind(entry) != AtomicTrail.LE) {
      return false;
    }
    int mark = out.size();
    if (!reason(trail, entry, trail.value(entry), out)) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  // the reason of a vertex at 0: a vertex in conflict with it that is 1 before the entry
  private boolean conflictReason(AtomicTrail trail, int entry, IntVar y, EntryList out) {
    if (trail.kind(entry) != AtomicTrail.LE || trail.value(entry) != 0) {
      return false;
    }
    for (int j = 0; j < x.length; j++) {
      if (x[j] == y) {
        for (int i : conflicts[j]) {
          if (trail.minBefore(x[i], entry) > 0) {
            trail.addLowerBound(x[i], entry, out);
            return true;
          }
        }
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int mark = out.size();
    int at = trail.size();
    int least = trail.minBefore(sum, at);
    if (!reason(trail, at, least - 1L, out)) {
      out.truncate(mark);
      return false;
    }
    trail.addLowerBound(sum, at, out);
    out.sortUnique(mark);
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : MaxCliqueBound([");
    for (int i = 0; i < x.length; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append(x[i]);
    }
    result.append("], ").append(sum).append(")");
    return result.toString();
  }

  @Override
  public MaxCliqueBound copy(VarMap map) {
    return new MaxCliqueBound(map.get(x), conflicts, map.get(sum));
  }
}
