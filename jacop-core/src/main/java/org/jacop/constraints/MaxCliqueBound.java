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
 * <p>When the coloring needs more classes than the sum may still gain, that is more than {@code
 * sum.min() - 1}, the vertices of the classes beyond that limit are covered one by one: first by
 * the re-coloring of MCS (a vertex with one compatible member in a class moves in when that member
 * can move to another class), then by MaxSAT reasoning on the classes as soft clauses, a failed
 * literal test of the vertex by unit propagation as in C.-M. Li and Z. Quan, An efficient
 * branch-and-bound algorithm based on MaxSAT for the maximum clique problem, AAAI 2010, and C.-M.
 * Li, Z. Fang and K. Xu, Combining MaxSAT reasoning and incremental upper bound for the maximum
 * clique problem, ICTAI 2013. When every vertex is covered the sum cannot reach its minimum and the
 * constraint fails; when exactly one vertex is left uncovered, every clique large enough holds it,
 * and it is set to 1. The system properties {@code org.jacop.maxClique.renumber}, {@code
 * org.jacop.maxClique.maxsat} and {@code org.jacop.maxClique.force} set to false turn the parts
 * off.
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

  // the members of each class of the last coloring, as positions; after absorb(), the first
  // classCount of them are the soft clauses of the MaxSAT view
  private long[][] classes;

  private int classCount;

  // per class after absorb(): FREE, FAILED, or USED (in an inconsistent subset)
  private int[] state;

  // per class in an inconsistent subset: the vertices its derivation holds false before the class
  // itself is used, so a zero there can join it in a reason
  private long[][] earlierFalse;

  // unit propagation scratch: the false vertices, the sequence of units, the class each unit came
  // from and the place of each class in that sequence (-1 when not a unit)
  private final long[] falsified;
  private int[] unitVertex;
  private int[] unitClass;
  private int[] unitAt;
  private boolean[] inSubset;
  private int[] stack;

  // the vertices of the classes beyond the limit
  private final int[] beyond;

  // the vertex, as a position, absorb() could not cover; -1 when none or more than one
  private int uncovered;

  private static final int FREE = -1;
  private static final int FAILED = -2;
  private static final int USED = 0;

  /** Whether the bound tries to cover the vertices beyond the limit by re-coloring (MCS). */
  public static final boolean RENUMBER =
      Boolean.parseBoolean(System.getProperty("org.jacop.maxClique.renumber", "true"));

  /** Whether the bound tries to cover them by MaxSAT failed-literal reasoning (Li and Quan). */
  public static final boolean MAXSAT =
      Boolean.parseBoolean(System.getProperty("org.jacop.maxClique.maxsat", "true"));

  /**
   * Whether the vertices are colored in the minimum width order of MCS (default) instead of by
   * decreasing degree.
   */
  public static final boolean DEGENERACY =
      Boolean.parseBoolean(System.getProperty("org.jacop.maxClique.degeneracy", "true"));

  /** Whether the one vertex left uncovered is set to 1. */
  public static final boolean FORCE =
      Boolean.parseBoolean(System.getProperty("org.jacop.maxClique.force", "true"));

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
    if (DEGENERACY) {
      degeneracyOrder(sorted, conflict, degree);
    }
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
    this.state = new int[8];
    this.earlierFalse = new long[8][];
    this.falsified = new long[words];
    this.unitVertex = new int[8];
    this.unitClass = new int[8];
    this.unitAt = new int[8];
    this.inSubset = new boolean[8];
    this.stack = new int[8];
    this.beyond = new int[n];
    setScope(Stream.concat(Arrays.stream(this.x), Stream.of(sum)));
  }

  /**
   * Reorders the vertices by the minimum width order of MCS: the vertex of least degree among those
   * left goes last, and its edges are removed, until no vertex is left; ties keep the decreasing
   * degree order.
   */
  private static void degeneracyOrder(Integer[] sorted, long[][] conflict, int[] degree) {
    int n = sorted.length;
    int[] left = degree.clone();
    boolean[] placed = new boolean[n];
    Integer[] out = new Integer[n];
    for (int slot = n - 1; slot >= 0; slot--) {
      int best = -1;
      for (Integer v : sorted) {
        if (!placed[v] && (best < 0 || left[v] < left[best])) {
          best = v;
        }
      }
      placed[best] = true;
      out[slot] = best;
      long[] c = conflict[best];
      for (int u = 0; u < n; u++) {
        if (!placed[u] && u != best && (c[u >>> 6] & (1L << u)) == 0) {
          left[u]--;
        }
      }
    }
    System.arraycopy(out, 0, sorted, 0, n);
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
      ensureClasses(k + 1);
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

  private void ensureClasses(int size) {
    if (size <= classes.length) {
      return;
    }
    int old = classes.length;
    int grown = Math.max(size, 2 * old);
    classes = Arrays.copyOf(classes, grown);
    for (int c = old; c < grown; c++) {
      classes[c] = new long[words];
    }
    state = Arrays.copyOf(state, grown);
    earlierFalse = Arrays.copyOf(earlierFalse, grown);
    unitVertex = Arrays.copyOf(unitVertex, grown);
    unitClass = Arrays.copyOf(unitClass, grown);
    unitAt = Arrays.copyOf(unitAt, grown);
    inSubset = Arrays.copyOf(inSubset, grown);
    stack = Arrays.copyOf(stack, grown);
  }

  /**
   * Tries to cover, after color() made k classes, the vertices of the classes beyond {@code limit}
   * so that the vertices left need only limit classes: each such vertex is moved into one of the
   * first limit classes by the re-coloring of MCS (Tomita et al., WALCOM 2010), or is shown to add
   * nothing to the bound by MaxSAT reasoning on the classes as soft clauses (C.-M. Li and Z. Quan,
   * An efficient branch-and-bound algorithm based on MaxSAT for the maximum clique problem, AAAI
   * 2010; C.-M. Li, Z. Fang and K. Xu, Combining MaxSAT reasoning and incremental upper bound for
   * the maximum clique problem, ICTAI 2013): a unit soft clause of the vertex, propagated over the
   * classes, empties a class, and the clauses of that derivation form an inconsistent subset of
   * which at most all but one hold. Each subset found lowers the bound by one and its clauses are
   * not used again.
   *
   * <p>It stops at the second vertex it cannot cover. It records the one vertex it could not cover
   * in {@code uncovered}, -1 otherwise; that vertex is kept out of every subset, so without it the
   * other vertices need at most limit classes.
   *
   * @return the number of vertices it could not cover, 0, 1 or 2 (meaning at least 2)
   */
  private int absorb(int k, int limit) {
    uncovered = -1;
    int b = 0;
    for (int c = limit; c < k; c++) {
      long[] members = classes[c];
      for (int w = 0; w < words; w++) {
        for (long bits = members[w]; bits != 0; bits &= bits - 1) {
          beyond[b++] = (w << 6) | Long.numberOfTrailingZeros(bits);
        }
      }
    }
    Arrays.sort(beyond, 0, b);
    classCount = limit;
    Arrays.fill(state, 0, limit, FREE);
    int fails = 0;
    for (int i = 0; i < b; i++) {
      int p = beyond[i];
      if (RENUMBER && renumber(p)) {
        continue;
      }
      int r = classCount++;
      ensureClasses(classCount);
      Arrays.fill(classes[r], 0L);
      classes[r][p >>> 6] = 1L << p;
      state[r] = FREE;
      if (MAXSAT && failedLiteral(r, p)) {
        continue;
      }
      state[r] = FAILED;
      fails++;
      if (fails > 1) {
        uncovered = -1;
        return 2;
      }
      uncovered = p;
    }
    return fails;
  }

  // moves p into a free class with no member compatible with it, or with exactly one, q, that can
  // move to another free class with no member compatible with q
  private boolean renumber(int p) {
    long[] c = compatible[p];
    for (int k1 = 0; k1 < classCount; k1++) {
      if (state[k1] != FREE) {
        continue;
      }
      long[] members = classes[k1];
      int count = 0;
      int q = -1;
      for (int w = 0; w < words && count < 2; w++) {
        long both = members[w] & c[w];
        if (both != 0) {
          count += Long.bitCount(both);
          q = (w << 6) | Long.numberOfTrailingZeros(both);
        }
      }
      if (count == 0) {
        members[p >>> 6] |= 1L << p;
        return true;
      }
      if (count > 1) {
        continue;
      }
      long[] cq = compatible[q];
      for (int k2 = 0; k2 < classCount; k2++) {
        if (k2 == k1 || state[k2] != FREE) {
          continue;
        }
        long[] other = classes[k2];
        boolean disjoint = true;
        for (int w = 0; w < words && disjoint; w++) {
          disjoint = (other[w] & cq[w]) == 0;
        }
        if (disjoint) {
          members[q >>> 6] &= ~(1L << q);
          other[q >>> 6] |= 1L << q;
          members[p >>> 6] |= 1L << p;
          return true;
        }
      }
    }
    return false;
  }

  private void addUnit(int count, int c, int u) {
    unitVertex[count] = u;
    unitClass[count] = c;
    unitAt[c] = count;
    long[] cu = compatible[u];
    for (int w = 0; w < words; w++) {
      falsified[w] |= ~cu[w];
    }
    falsified[u >>> 6] &= ~(1L << u);
  }

  // whether vertex u is false through the unit at place j
  private boolean falseBy(int j, int u) {
    int v = unitVertex[j];
    return v != u && (compatible[v][u >>> 6] & (1L << u)) == 0;
  }

  /**
   * Propagates the unit soft clause r = {p} over the free classes. When a class empties, it marks
   * the clauses its derivation uses as USED and returns true.
   */
  private boolean failedLiteral(int r, int p) {
    Arrays.fill(falsified, 0L);
    for (int c = 0; c < classCount; c++) {
      unitAt[c] = -1;
    }
    int units = 0;
    addUnit(units++, r, p);
    int conflict = -1;
    boolean changed = true;
    while (changed && conflict < 0) {
      changed = false;
      for (int c = 0; c < classCount && conflict < 0; c++) {
        if (state[c] != FREE) {
          continue;
        }
        long[] members = classes[c];
        int count = 0;
        int u = -1;
        for (int w = 0; w < words && count < 2; w++) {
          long live = members[w] & ~falsified[w];
          if (live != 0) {
            count += Long.bitCount(live);
            u = (w << 6) | Long.numberOfTrailingZeros(live);
          }
        }
        if (count == 0) {
          conflict = c;
        } else if (count == 1 && unitAt[c] < 0) {
          addUnit(units++, c, u);
          changed = true;
        }
      }
    }
    if (conflict < 0) {
      return false;
    }
    // the clauses the empty class depends on, back through the units that falsified its members
    for (int c = 0; c < classCount; c++) {
      inSubset[c] = false;
    }
    int top = 0;
    inSubset[conflict] = true;
    stack[top++] = conflict;
    while (top > 0) {
      int c = stack[--top];
      int before = unitAt[c] < 0 || c == conflict ? units : unitAt[c];
      int own = unitAt[c] >= 0 && c != conflict ? unitVertex[unitAt[c]] : -1;
      long[] members = classes[c];
      for (int w = 0; w < words; w++) {
        for (long bits = members[w]; bits != 0; bits &= bits - 1) {
          int u = (w << 6) | Long.numberOfTrailingZeros(bits);
          if (u == own) {
            continue;
          }
          int j = 0;
          while (j < before && !falseBy(j, u)) {
            j++;
          }
          assert j < before : "a member of a class in the derivation is not false";
          int d = unitClass[j];
          if (!inSubset[d]) {
            inSubset[d] = true;
            stack[top++] = d;
          }
        }
      }
    }
    for (int c = 0; c < classCount; c++) {
      if (!inSubset[c]) {
        continue;
      }
      state[c] = USED;
      if (earlierFalse[c] == null) {
        earlierFalse[c] = new long[words];
      }
      long[] early = earlierFalse[c];
      Arrays.fill(early, 0L);
      // a zero joining a class that became a unit must be false before it did
      int before = unitAt[c] < 0 ? units : unitAt[c];
      for (int j = 0; j < before; j++) {
        if (inSubset[unitClass[j]]) {
          long[] cu = compatible[unitVertex[j]];
          for (int w = 0; w < words; w++) {
            early[w] |= ~cu[w];
          }
          early[unitVertex[j] >>> 6] &= ~(1L << unitVertex[j]);
        }
      }
    }
    return true;
  }

  /**
   * The vertex to branch on next, as maximum clique algorithms choose it (MCQ, MCS): a vertex not
   * yet fixed of the last class of the coloring of the vertices that can still be 1, the one of
   * smallest degree there. A clique larger than the number of classes before it needs a vertex of
   * that class or a later one.
   *
   * @return the index in x of the vertex, or -1 when every vertex is fixed
   */
  public int branchVertex() {
    int k = boundNow();
    for (int c = k - 1; c >= 0; c--) {
      long[] members = classes[c];
      for (int w = words - 1; w >= 0; w--) {
        for (long bits = members[w]; bits != 0; bits &= ~Long.highestOneBit(bits)) {
          int p = (w << 6) | (63 - Long.numberOfLeadingZeros(bits));
          if (x[order[p]].min() == 0) {
            return order[p];
          }
        }
      }
    }
    return -1;
  }

  /**
   * A large clique of the vertices that can still be 1, by greedy construction from each vertex: it
   * takes the vertex, then every next vertex of the coloring order compatible with all taken ones,
   * and keeps the largest clique over all starting vertices, as the initial heuristic clique of
   * exact maximum clique algorithms (San Segundo et al., C&amp;OR 38(2), 2011). It takes O(n (n/64
   * + k n/64)) word operations for a clique of k vertices.
   *
   * @return the indices in x of the clique's vertices
   */
  public int[] greedyClique() {
    int n = x.length;
    long[] candidates = new long[words];
    long[] all = new long[words];
    for (int p = 0; p < n; p++) {
      if (x[order[p]].max() > 0) {
        all[p >>> 6] |= 1L << p;
      }
    }
    int[] best = new int[0];
    int[] clique = new int[n];
    for (int s = 0; s < n; s++) {
      if ((all[s >>> 6] & (1L << s)) == 0) {
        continue;
      }
      int size = 0;
      clique[size++] = s;
      long[] cs = compatible[s];
      for (int w = 0; w < words; w++) {
        candidates[w] = all[w] & cs[w];
      }
      for (int w = 0; w < words; w++) {
        while (candidates[w] != 0) {
          int p = (w << 6) | Long.numberOfTrailingZeros(candidates[w]);
          clique[size++] = p;
          long[] c = compatible[p];
          for (int u = w; u < words; u++) {
            candidates[u] &= c[u];
          }
        }
      }
      if (size > best.length) {
        best = new int[size];
        for (int i = 0; i < size; i++) {
          best[i] = order[clique[i]];
        }
      }
    }
    // from the first vertices of the order, the candidate with the most compatible candidates
    for (int s = 0, starts = 0; s < n && starts < GREEDY_STARTS; s++) {
      if ((all[s >>> 6] & (1L << s)) == 0) {
        continue;
      }
      starts++;
      int size = 0;
      int p = s;
      for (int w = 0; w < words; w++) {
        candidates[w] = all[w];
      }
      while (p >= 0) {
        clique[size++] = p;
        long[] c = compatible[p];
        for (int w = 0; w < words; w++) {
          candidates[w] &= c[w];
        }
        p = -1;
        int most = -1;
        for (int w = 0; w < words; w++) {
          for (long bits = candidates[w]; bits != 0; bits &= bits - 1) {
            int q = (w << 6) | Long.numberOfTrailingZeros(bits);
            long[] cq = compatible[q];
            int count = 0;
            for (int u = 0; u < words; u++) {
              count += Long.bitCount(candidates[u] & cq[u]);
            }
            if (count > most) {
              most = count;
              p = q;
            }
          }
        }
      }
      if (size > best.length) {
        best = new int[size];
        for (int i = 0; i < size; i++) {
          best[i] = order[clique[i]];
        }
      }
    }
    return best;
  }

  // the starting vertices of the greedy clique that picks the best connected candidate
  private static final int GREEDY_STARTS =
      Integer.getInteger("org.jacop.maxClique.greedyStarts", 100);

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
    boolean again = true;
    while (again) {
      again = false;
      for (int i = 0; i < x.length; i++) {
        if (x[i].min() > 0) {
          for (int j : conflicts[i]) {
            if (x[j].max() > 0) {
              x[j].domain.inMax(store.level, x[j], 0);
            }
          }
        }
      }
      int k = boundNow();
      int least = sum.min();
      if (k >= least && (RENUMBER || MAXSAT || FORCE) && least > 0) {
        int fails = absorb(k, least - 1);
        if (fails == 0) {
          sum.domain.inMax(store.level, sum, least - 1);
        } else if (fails == 1 && FORCE) {
          IntVar v = x[order[uncovered]];
          if (v.min() == 0) {
            v.domain.inMin(store.level, v, 1);
            again = true;
          }
        }
      }
      sum.domain.inMax(store.level, sum, k);
    }
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
    for (IntVar v : x) {
      if (!v.singleton()) {
        return false;
      }
    }
    long s = 0;
    for (int i = 0; i < x.length; i++) {
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
   * Colors the vertices that could be 1 just before a trail position, but for vertex {@code
   * excluded} (a position, or -1), and adds to {@code out} the zeros of the other vertices that the
   * bound needs to keep at most {@code limit} classes. It repeats the computation of consistency,
   * so it finds the same classes and subsets.
   *
   * @return false when the bound is above limit
   */
  private boolean reason(AtomicTrail trail, int at, long limit, int excluded, EntryList out) {
    int n = x.length;
    Arrays.fill(needed, 0L);
    Arrays.fill(left, 0L);
    for (int p = 0; p < n; p++) {
      if (p != excluded && trail.maxBefore(x[order[p]], at) > 0) {
        left[p >>> 6] |= 1L << p;
      }
    }
    int k = color();
    if (k > limit) {
      if (limit < 0 || absorb(k, (int) limit) != 0) {
        return false;
      }
    } else {
      classCount = k;
      Arrays.fill(state, 0, k, FREE);
    }
    // a zero in conflict with every member of a class joins it, and is then not needed; a class of
    // an inconsistent subset takes only zeros its derivation holds false before using it
    for (int p = 0; p < n; p++) {
      IntVar v = x[order[p]];
      if (p == excluded || trail.maxBefore(v, at) > 0) {
        continue;
      }
      long[] c = compatible[p];
      boolean joined = false;
      for (int j = 0; j < classCount && !joined; j++) {
        if (state[j] == FAILED || state[j] == USED && (earlierFalse[j][p >>> 6] & (1L << p)) == 0) {
          continue;
        }
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
      if (trail.kind(entry) == AtomicTrail.GE) {
        return forcedReason(trail, entry, y, out);
      }
      return conflictReason(trail, entry, y, out);
    }
    if (trail.kind(entry) != AtomicTrail.LE) {
      return false;
    }
    int mark = out.size();
    if (!reason(trail, entry, trail.value(entry), -1, out)) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  // the reason of a vertex set to 1: the other vertices need at most sum.min - 1 classes
  private boolean forcedReason(AtomicTrail trail, int entry, IntVar y, EntryList out) {
    if (trail.value(entry) != 1) {
      return false;
    }
    int excluded = -1;
    for (int j = 0; j < x.length; j++) {
      if (x[j] == y) {
        excluded = position[j];
        break;
      }
    }
    int least = trail.minBefore(sum, entry);
    int mark = out.size();
    if (excluded < 0 || !reason(trail, entry, least - 1L, excluded, out)) {
      out.truncate(mark);
      return false;
    }
    trail.addLowerBound(sum, entry, out);
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
    if (!reason(trail, at, least - 1L, -1, out)) {
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
