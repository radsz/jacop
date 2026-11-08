/*
 * ValuesCliques.java
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
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.DomainCover;
import org.jacop.lcg.EntryList;

/**
 * The difference graph of a {@link Values} constraint and a large clique of it, which bound the
 * number of different values from below.
 *
 * <p>Two variables of the list are linked when the other constraints of the model force them to
 * differ: x &ne; y, alldifferent constraints, x = y + t or |x - y| = t with 0 not in the domain of
 * t, x = y + c with c &ne; 0, and linear constraints of those forms. The variables of a clique of
 * this graph take pairwise different values, so a clique K gives count &ge; |K|. This is the lower
 * bound of AtMostNValue from independent sets of the variables' intersection graph (Bessiere,
 * Hebrard, Hnich, Kiziltan and Walsh, "Filtering algorithms for the NValue constraint", Constraints
 * 11(4), 2006), strengthened with the difference constraints as proposed by Fages and
 * Lap&egrave;gue ("Filtering AtMostNValue with difference constraints: application to the shift
 * minimisation personnel task scheduling problem", CP 2013 and Artificial Intelligence 212, 2014).
 * Their filtering is also applied: when count is at most |K|, the clique takes every value, so a
 * variable outside it takes a value of a clique variable it is not linked to.
 *
 * <p>The graph is read once at the root (store level 0), where the domains it reads are facts of
 * the model, and does not change afterwards. A copy of the constraint keeps it, so the graph is
 * part of what the constraint enforces: the clique variables differ. The clique is found by a
 * greedy pass from every variable followed by a branch and bound with a node limit (Tomita and
 * Seki's colouring bound, DMTCS 2003).
 *
 * <p>Property {@code jacop.values.cliques} (default true) switches the graph off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ValuesCliques {

  /** Whether Values reads the difference graph. */
  static final boolean ENABLED =
      Boolean.parseBoolean(System.getProperty("jacop.values.cliques", "true"));

  /** Lists longer than this get no graph (the adjacency is a bit matrix). */
  static final int MAX_VARIABLES = 4096;

  /** The most nodes of the exact clique search. */
  private static final long NODE_LIMIT = 200_000;

  private final int n;

  /** The edges as one bit set per variable. */
  private final long[][] adjacent;

  /** The number of edges. */
  final int edges;

  /** The variables of the clique, by position in the list. */
  final int[] clique;

  private final boolean[] inClique;

  private ValuesCliques(int n, long[][] adjacent, int edges) {
    this.n = n;
    this.adjacent = adjacent;
    this.edges = edges;
    this.clique = new CliqueSearch(n, adjacent).run();
    this.inClique = new boolean[n];
    for (int i : clique) {
      inClique[i] = true;
    }
  }

  /** The size of the clique, a lower bound on the number of different values. */
  int size() {
    return clique.length;
  }

  boolean linked(int i, int j) {
    return (adjacent[i][j >>> 6] & (1L << j)) != 0;
  }

  /**
   * Reads the difference graph of the list from the constraints attached to its variables now.
   *
   * @param list the variables of the Values constraint
   * @param previous the graph read before, or null
   * @return the graph, previous when it has the same number of edges, or null when it has no edge
   *     or the list is too long
   */
  static ValuesCliques read(IntVar[] list, ValuesCliques previous) {
    int n = list.length;
    if (n < 2 || n > MAX_VARIABLES) {
      return previous;
    }
    Map<IntVar, Integer> position = new IdentityHashMap<>();
    for (int i = 0; i < n; i++) {
      // a variable twice in the list is the same value, never linked
      if (position.put(list[i], i) != null) {
        position.put(list[i], -1);
      }
    }
    long[][] adjacent = new long[n][(n + 63) >>> 6];
    int[] edges = new int[1];
    Map<Constraint, Boolean> seen = new IdentityHashMap<>();
    for (IntVar x : list) {
      Domain d = x.dom();
      if (d.modelConstraints == null) {
        continue;
      }
      for (int e = 0; e < d.modelConstraints.length; e++) {
        Constraint[] attached = d.modelConstraints[e];
        if (attached == null) {
          continue;
        }
        for (int j = Math.min(d.modelConstraintsToEvaluate[e], attached.length) - 1; j >= 0; j--) {
          Constraint c = attached[j];
          if (c != null && seen.put(c, Boolean.TRUE) == null) {
            links(c, position, adjacent, edges);
          }
        }
      }
    }
    if (edges[0] == 0) {
      return previous;
    }
    if (previous != null && previous.edges == edges[0]) {
      return previous;
    }
    return new ValuesCliques(n, adjacent, edges[0]);
  }

  // adds the pairs of list variables that constraint c forces to differ
  private static void links(
      Constraint c, Map<IntVar, Integer> position, long[][] adjacent, int[] edges) {
    if (c instanceof XneqY ne) {
      link(position, ne.x, ne.y, adjacent, edges);
    } else if (c instanceof XplusYeqZ s) {
      // z = x + y: z differs from x when y cannot be 0, and from y when x cannot be 0
      if (!s.y.domain.contains(0)) {
        link(position, s.z, s.x, adjacent, edges);
      }
      if (!s.x.domain.contains(0)) {
        link(position, s.z, s.y, adjacent, edges);
      }
    } else if (c instanceof XplusCeqZ s) {
      if (s.c != 0) {
        link(position, s.x, s.z, adjacent, edges);
      }
    } else if (c instanceof Distance s) {
      if (!s.z.domain.contains(0)) {
        link(position, s.x, s.y, adjacent, edges);
      }
    } else if (c instanceof Alldistinct a) {
      clique(position, a.list, adjacent, edges);
    } else if (c instanceof Alldifferent a && !(c instanceof AlldifferentExcept)) {
      clique(position, a.list, adjacent, edges);
    } else if (c instanceof LinearInt s) {
      linear(s, position, adjacent, edges);
    }
  }

  // a1 x + a2 y (+ a3 t) rel b with a2 = -a1: x - y is (b - a3 t) / a1, which is never 0 when
  // rel is != with b = 0, or rel is == and b / a3 is not an integer of t's domain
  private static void linear(
      LinearInt s, Map<IntVar, Integer> position, long[][] adjacent, int[] edges) {
    IntVar[] x = s.x;
    long[] a = s.a;
    if (x.length == 2 && a[0] == -a[1]) {
      if (s.relationType == LinearInt.NE && s.b == 0) {
        link(position, x[0], x[1], adjacent, edges);
      } else if (s.relationType == LinearInt.EQ && s.b != 0) {
        link(position, x[0], x[1], adjacent, edges);
      }
    } else if (x.length == 3 && s.relationType == LinearInt.EQ) {
      for (int t = 0; t < 3; t++) {
        int p = (t + 1) % 3;
        int q = (t + 2) % 3;
        if (a[p] == -a[q] && a[t] != 0 && (s.b % a[t] != 0 || !holds(x[t], s.b / a[t]))) {
          link(position, x[p], x[q], adjacent, edges);
        }
      }
    }
  }

  private static boolean holds(IntVar t, long v) {
    return v >= IntDomain.MIN_INT && v <= IntDomain.MAX_INT && t.domain.contains((int) v);
  }

  private static void clique(
      Map<IntVar, Integer> position, IntVar[] vars, long[][] adjacent, int[] edges) {
    for (int i = 0; i < vars.length; i++) {
      for (int j = i + 1; j < vars.length; j++) {
        link(position, vars[i], vars[j], adjacent, edges);
      }
    }
  }

  private static void link(
      Map<IntVar, Integer> position, IntVar x, IntVar y, long[][] adjacent, int[] edges) {
    Integer i = position.get(x);
    Integer j = position.get(y);
    if (i == null || j == null || i < 0 || j < 0 || i.equals(j)) {
      return;
    }
    long bit = 1L << j;
    if ((adjacent[i][j >>> 6] & bit) == 0) {
      adjacent[i][j >>> 6] |= bit;
      adjacent[j][i >>> 6] |= 1L << i;
      edges[0]++;
    }
  }

  /**
   * Enforces count &ge; |K| and, when count &le; |K|, restricts each variable outside the clique to
   * the values of the clique variables it is not linked to.
   *
   * @param store the store
   * @param list the variables
   * @param count the number of different values
   */
  void propagate(Store store, IntVar[] list, IntVar count) {
    int k = clique.length;
    count.domain.inMin(store.level, count, k);
    if (count.max() > k) {
      return;
    }
    for (int i = 0; i < n; i++) {
      if (inClique[i]) {
        continue;
      }
      IntVar x = list[i];
      IntDomain allowed = allowed(list, i);
      if (!x.domain.isIntersecting(allowed)) {
        throw Store.failException;
      }
      x.domain.in(store.level, x, allowed);
    }
  }

  // the values of the clique variables that variable i is not linked to
  private IntDomain allowed(IntVar[] list, int i) {
    IntDomain allowed = new IntervalDomain();
    for (int j : clique) {
      if (!linked(i, j)) {
        allowed = allowed.union(list[j].dom());
      }
    }
    return allowed;
  }

  /**
   * The reason of a lower bound of count up to |K|: none, the graph is a fact.
   *
   * @param bound the lower bound
   * @return whether the clique explains it
   */
  boolean explainsLowerBound(int bound) {
    return bound <= clique.length;
  }

  /**
   * Adds the reason of an atom of variable i outside the clique: count is at most |K| and no clique
   * variable that i is not linked to has the values the atom removes.
   *
   * @param trail the trail
   * @param list the variables
   * @param count the number of different values
   * @param i the position of the atom's variable
   * @param entry the atom
   * @param out where the reason entries are added
   * @return false when there is no such reason
   */
  boolean explainVariable(
      AtomicTrail trail, IntVar[] list, IntVar count, int i, int entry, EntryList out) {
    if (inClique[i] || trail.maxBefore(count, entry) > clique.length) {
      return false;
    }
    int mark = out.size();
    trail.addUpperBound(count, entry, out);
    if (DomainCover.entry(trail, entry, (v, o) -> notInClique(trail, list, i, v, entry, o), out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  /**
   * Adds the reason of a failure when some variable outside the clique has no value of the clique
   * variables it is not linked to, or count is below |K|.
   *
   * @param trail the trail
   * @param list the variables
   * @param count the number of different values
   * @param out where the reason entries are added
   * @return false when the failure has another cause
   */
  boolean explainFailure(AtomicTrail trail, IntVar[] list, IntVar count, EntryList out) {
    int position = trail.size();
    int max = trail.maxBefore(count, position);
    if (max < clique.length) {
      trail.addUpperBound(count, position, out);
      return true;
    }
    if (max > clique.length) {
      return false;
    }
    int mark = out.size();
    for (int i = 0; i < n; i++) {
      if (inClique[i]) {
        continue;
      }
      trail.addUpperBound(count, position, out);
      int at = i;
      if (DomainCover.domain(
          trail, list[i], position, (v, o) -> notInClique(trail, list, at, v, position, o), out)) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  // whether no clique variable that i is not linked to had v just before position, adding why
  private boolean notInClique(
      AtomicTrail trail, IntVar[] list, int i, int v, int position, EntryList out) {
    int mark = out.size();
    for (int j : clique) {
      if (!linked(i, j) && !trail.excludedBefore(list[j], v, position, out)) {
        out.truncate(mark);
        return false;
      }
    }
    return true;
  }

  /** Greedy cliques from every vertex, then branch and bound with a colouring bound. */
  private static final class CliqueSearch {

    private final int n;
    private final long[][] adjacent;
    private final int words;
    private int[] best = new int[0];
    private final int[] current;
    private long nodes;

    CliqueSearch(int n, long[][] adjacent) {
      this.n = n;
      this.adjacent = adjacent;
      this.words = (n + 63) >>> 6;
      this.current = new int[n];
    }

    int[] run() {
      int[] degree = new int[n];
      for (int i = 0; i < n; i++) {
        degree[i] = cardinality(adjacent[i]);
      }
      for (int v = 0; v < n; v++) {
        if (degree[v] + 1 > best.length) {
          greedy(v, degree);
        }
      }
      long[] all = new long[words];
      for (int v = 0; v < n; v++) {
        if (degree[v] + 1 > best.length) {
          all[v >>> 6] |= 1L << v;
        }
      }
      expand(all, 0);
      int[] result = best.clone();
      Arrays.sort(result);
      return result;
    }

    // adds to {v} the candidate with the most neighbours among the candidates, while any is left
    private void greedy(int v, int[] degree) {
      long[] candidates = adjacent[v].clone();
      int[] members = new int[n];
      int size = 0;
      members[size++] = v;
      while (!isEmpty(candidates)) {
        int pick = -1;
        int pickDegree = -1;
        for (int u = next(candidates, 0); u >= 0; u = next(candidates, u + 1)) {
          int d = intersection(candidates, adjacent[u]);
          if (d > pickDegree || (d == pickDegree && degree[u] > degree[pick])) {
            pick = u;
            pickDegree = d;
          }
        }
        members[size++] = pick;
        and(candidates, adjacent[pick]);
      }
      if (size > best.length) {
        best = Arrays.copyOf(members, size);
      }
    }

    // Tomita and Seki's MCQ: colour the candidates greedily, a colour class adds at most one
    private void expand(long[] candidates, int depth) {
      if (++nodes > NODE_LIMIT) {
        return;
      }
      int size = cardinality(candidates);
      int[] order = new int[size];
      int[] colour = new int[size];
      long[] uncoloured = candidates.clone();
      int coloured = 0;
      int c = 0;
      while (!isEmpty(uncoloured)) {
        c++;
        long[] available = uncoloured.clone();
        while (!isEmpty(available)) {
          int v = next(available, 0);
          available[v >>> 6] &= ~(1L << v);
          andNot(available, adjacent[v]);
          uncoloured[v >>> 6] &= ~(1L << v);
          order[coloured] = v;
          colour[coloured++] = c;
        }
      }
      long[] remaining = candidates.clone();
      for (int k = size - 1; k >= 0; k--) {
        if (depth + colour[k] <= best.length || nodes > NODE_LIMIT) {
          return;
        }
        int v = order[k];
        current[depth] = v;
        long[] next = remaining.clone();
        and(next, adjacent[v]);
        if (isEmpty(next)) {
          if (depth + 1 > best.length) {
            best = Arrays.copyOf(current, depth + 1);
          }
        } else {
          expand(next, depth + 1);
        }
        remaining[v >>> 6] &= ~(1L << v);
      }
    }

    private int next(long[] set, int from) {
      int w = from >>> 6;
      if (w >= words) {
        return -1;
      }
      long word = set[w] & (-1L << from);
      while (true) {
        if (word != 0) {
          return (w << 6) + Long.numberOfTrailingZeros(word);
        }
        if (++w == words) {
          return -1;
        }
        word = set[w];
      }
    }

    private static boolean isEmpty(long[] set) {
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

    private static int intersection(long[] a, long[] b) {
      int c = 0;
      for (int i = 0; i < a.length; i++) {
        c += Long.bitCount(a[i] & b[i]);
      }
      return c;
    }

    private static void and(long[] a, long[] b) {
      for (int i = 0; i < a.length; i++) {
        a[i] &= b[i];
      }
    }

    private static void andNot(long[] a, long[] b) {
      for (int i = 0; i < a.length; i++) {
        a[i] &= ~b[i];
      }
    }
  }
}
