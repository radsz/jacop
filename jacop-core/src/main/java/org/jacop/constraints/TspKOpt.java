/*
 * TspKOpt.java
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
import org.jacop.api.Copyable;
import org.jacop.api.Stateful;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.DomainCover;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * TspKOpt: a dominance rule for a symmetric travelling salesman tour written with successors, x[v]
 * = w + offset for the arc v -&gt; w, whose objective is the sum d[v][x[v]] of the arc lengths and
 * which nothing else constrains. A tour that a 2-opt or 3-opt move shortens is not optimal, so the
 * fixed arcs of an optimal tour admit no such move. The constraint removes the partial tours that
 * do:
 *
 * <ul>
 *   <li>2-opt: in a tour with the arcs a -&gt; b and c -&gt; e, replacing them by a -&gt; c and b
 *       -&gt; e and reversing the path from b to c gives a tour again. So when a -&gt; b is fixed,
 *       every successor e of c with d(a,c) + d(b,e) &lt; d(a,b) + d(c,e) goes (the directed form of
 *       the compatibility of Jonker and Volgenant), whatever the arcs in between.
 *   <li>3-opt: three arcs of one path of fixed arcs are in a known order along the tour, so the
 *       four pure 3-opt reconnections of the two segments between them give a tour again. A path
 *       with an improving reconnection fails (the minimality of the mandatory Hamiltonian paths of
 *       Isoart and Régin), and an arc that joins the ends of two paths goes when the joined path
 *       has an improving reconnection that removes this arc.
 * </ul>
 *
 * <p>The fixed arcs must be part of a tour, so two arcs into one node and a cycle of fixed arcs
 * through fewer than all nodes fail, and a complete tour is checked as a path from a node back to
 * it. Every rule needs a strict improvement, so no optimal tour is removed; the tours that are not
 * optimal can go, as with any dominance rule. Missing arcs must have a length larger than any tour,
 * so that no move uses one. As removing arcs keeps a path minimal, only newly fixed arcs are
 * checked (Proposition 11 of Isoart and Régin): the 3-opt check of a path takes only the moves
 * across one of its new arcs. For lazy clause generation a removal or failure is explained by the
 * fixed arcs it used: the arc a -&gt; b for 2-opt, the arcs of the path between the removed arcs
 * for 3-opt.
 *
 * <p>References: N. Isoart and J.-C. Régin, A k-Opt Based Constraint for the TSP, CP 2021, LIPIcs
 * 210, 30:1-30:16 (the mandatory Hamiltonian path constraint); R. Jonker and T. Volgenant,
 * Nonoptimal edges for the symmetric traveling salesman problem, Operations Research 32(4), 1984
 * (compatible edges); S. Lin, Computer solutions of the traveling salesman problem, Bell System
 * Technical Journal 44(10), 1965 (2-opt and 3-opt).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class TspKOpt extends Constraint implements Stateful, Copyable<TspKOpt>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The successors: x[v] = w + offset for the arc v -&gt; w. */
  public final IntVar[] x;

  /** The value of the successor 0. */
  public final int offset;

  // the symmetric arc lengths
  private final long[][] d;

  private final int n;

  // the store level at which the fixed arc v -> x[v] was checked, or -1
  private final int[] checked;

  // the tour length that switches the rules on, or null
  private final IntVar length;

  // the largest relative distance between the length's bounds at which the rules are on
  private final double gap;

  // the largest lower bound of the length seen at the root
  private int rootMin = Integer.MIN_VALUE;

  // whether a tour within the length's bound has been seen; always true without a length
  private boolean seenTour;

  // the fixed successor of each node, its fixed predecessor, or -1
  private final int[] succ;
  private final int[] pred;

  // a path of fixed arcs, a joined path, and for each node of a joined path whether its out arc is
  // new
  private final int[] path;
  private final int[] joined;
  private final boolean[] fresh;

  // the path each node is on in this call, by its first node, and the paths that changed
  private final int[] firstOf;
  private final boolean[] changed;

  // the arcs (tail, head, tail, head, ...) that a 3-opt removal of an arc t -> j used
  private final int[][][] reason;

  // the first new arc at or after each arc of a path
  private final int[] nextNew;

  // the tails of the arcs that explain the last failure
  private int[] failTails;
  private int[] failHeads;

  /**
   * Creates the constraint.
   *
   * @param x the successors, x[v] = w + offset for the arc v -&gt; w
   * @param offset the value of the successor of node 0
   * @param d the symmetric arc lengths; a missing arc must be longer than any tour
   */
  public TspKOpt(IntVar[] x, int offset, long[][] d) {
    this(x, offset, d, null, 0);
  }

  /**
   * Creates the constraint for a model whose objective is the tour length and which has no other
   * constraint on the tour, so that every tour within the length's bound is a solution. The rules
   * make better tours harder to find, since a tour that a depth-first search completes is rarely
   * locally optimal: before a first tour they can keep a search from finding any, and far from the
   * optimum they slow the improvements. So they remove nothing until the constraint has seen such a
   * tour, and then only at the nodes where the length's bounds are within the relative gap of each
   * other (max - min &le; gap * |max|), where the search is mostly proving.
   *
   * @param x the successors, x[v] = w + offset for the arc v -&gt; w
   * @param offset the value of the successor of node 0
   * @param d the symmetric arc lengths; a missing arc must be longer than any tour
   * @param length the tour length
   * @param gap the relative gap between the length's bounds below which the rules are on
   */
  public TspKOpt(IntVar[] x, int offset, long[][] d, IntVar length, double gap) {
    checkInputForNullness("x", x);
    n = x.length;
    if (n < 4 || d == null || d.length != n) {
      throw new IllegalArgumentException("TspKOpt needs at least 4 nodes and an n x n matrix");
    }
    for (int v = 0; v < n; v++) {
      if (d[v] == null || d[v].length != n) {
        throw new IllegalArgumentException("TspKOpt needs an n x n matrix");
      }
      for (int w = 0; w < v; w++) {
        if (d[v][w] != d[w][v]) {
          throw new IllegalArgumentException("TspKOpt needs symmetric lengths");
        }
      }
    }
    this.x = Arrays.copyOf(x, n);
    this.offset = offset;
    this.d = d;
    this.length = length;
    this.gap = gap;
    this.seenTour = length == null;
    this.numberId = idNumber.incrementAndGet();
    checked = new int[n];
    Arrays.fill(checked, -1);
    succ = new int[n];
    pred = new int[n];
    path = new int[n + 1];
    joined = new int[n];
    fresh = new boolean[n + 1];
    firstOf = new int[n];
    changed = new boolean[n];
    reason = new int[n][n][];
    nextNew = new int[n + 1];
    this.queueIndex = 2;
    if (length == null) {
      setScope(this.x);
    } else {
      IntVar[] scope = Arrays.copyOf(this.x, n + 1);
      scope[n] = length;
      setScope(scope);
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public int getConsistencyPruningEvent(Var var) {
    return var == length ? IntDomain.BOUND : super.getConsistencyPruningEvent(var);
  }

  @Override
  public void removeLevel(int level) {
    for (int v = 0; v < n; v++) {
      if (checked[v] >= level) {
        checked[v] = -1;
      }
    }
  }

  // the fixed successor of v, or -1
  private int fixedSucc(int v) {
    if (!x[v].singleton()) {
      return -1;
    }
    int w = x[v].value() - offset;
    return w >= 0 && w < n && w != v ? w : -1;
  }

  @Override
  public void consistency(Store store) {
    if (length != null && store.level == 0) {
      rootMin = Math.max(rootMin, length.min());
    }
    if (!seenTour) {
      // the first complete tour within the length's bound is a solution: switch on after it
      long sum = 0;
      for (int v = 0; v < n; v++) {
        int w = fixedSucc(v);
        if (w < 0) {
          return;
        }
        sum += d[v][w];
      }
      seenTour = sum <= length.max();
      return;
    }
    if (length != null && length.max() - (double) rootMin > gap * Math.abs((double) length.max())) {
      // the root bound is far from the best tour: no removal, and the arcs are checked once it is
      // near
      return;
    }
    boolean again = true;
    while (again) {
      again = false;
      int fresher = 0;
      for (int v = 0; v < n; v++) {
        succ[v] = fixedSucc(v);
        pred[v] = -1;
      }
      for (int v = 0; v < n; v++) {
        if (succ[v] >= 0) {
          if (pred[succ[v]] >= 0) {
            // two arcs into one node: no tour
            failTails = new int[] {pred[succ[v]], v};
            failHeads = new int[] {succ[v], succ[v]};
            throw Store.failException;
          }
          pred[succ[v]] = v;
          if (checked[v] < 0) {
            fresher++;
          }
        }
      }
      if (fresher == 0) {
        return;
      }
      for (int a = 0; a < n; a++) {
        if (succ[a] >= 0 && checked[a] < 0 && twoOpt(store, a, succ[a])) {
          again = true;
        }
      }
      if (paths(store)) {
        again = true;
      }
      for (int v = 0; v < n; v++) {
        if (succ[v] >= 0 && checked[v] < 0) {
          checked[v] = store.level;
        }
      }
    }
  }

  // the 2-opt rule for the new arc a -> b; true when a successor became fixed
  private boolean twoOpt(Store store, int a, int b) {
    boolean fixed = false;
    long ab = d[a][b];
    for (int c = 0; c < n; c++) {
      if (c == a) {
        continue;
      }
      long[] dc = d[c];
      long ac = d[a][c];
      long[] db = d[b];
      if (succ[c] >= 0) {
        int e = succ[c];
        if (ac + db[e] < ab + dc[e]) {
          failTails = new int[] {a, c};
          failHeads = new int[] {b, e};
          throw Store.failException;
        }
        continue;
      }
      IntDomain dom = x[c].dom();
      for (ValueEnumeration en = dom.valueEnumeration(); en.hasMoreElements(); ) {
        int e = en.nextElement() - offset;
        if (e >= 0 && e < n && e != c && ac + db[e] < ab + dc[e]) {
          x[c].domain.inComplement(store.level, x[c], e + offset);
        }
      }
      fixed |= x[c].singleton();
    }
    return fixed;
  }

  // the 3-opt rules on the paths with a new arc; true when a successor became fixed
  private boolean paths(Store store) {
    Arrays.fill(changed, false);
    for (int v = 0; v < n; v++) {
      firstOf[v] = -1;
    }
    for (int f = 0; f < n; f++) {
      if (pred[f] >= 0 || succ[f] < 0) {
        continue;
      }
      int m = 0;
      boolean anyNew = false;
      for (int v = f; v >= 0; v = succ[v]) {
        firstOf[v] = f;
        path[m] = v;
        fresh[m] = succ[v] >= 0 && checked[v] < 0;
        anyNew |= fresh[m];
        m++;
      }
      if (anyNew) {
        changed[f] = true;
        int[] move = improving(path, fresh, m, -1);
        if (move != null) {
          fail(path, move);
        }
      }
    }
    // the nodes left are on cycles of fixed arcs: a short one fails, a tour is checked as a path
    // from a node back to it
    for (int r = 0; r < n; r++) {
      if (firstOf[r] >= 0 || succ[r] < 0) {
        continue;
      }
      int m = 0;
      boolean anyNew = false;
      for (int v = r; m == 0 || v != r; v = succ[v]) {
        firstOf[v] = r;
        path[m] = v;
        fresh[m] = checked[v] < 0;
        anyNew |= fresh[m];
        m++;
      }
      path[m++] = r;
      if (m <= n) {
        fail(path, new int[] {0, m - 2});
      }
      if (anyNew) {
        int[] move = improving(path, fresh, m, -1);
        if (move != null) {
          fail(path, move);
        }
      }
    }
    for (int v = 0; v < n; v++) {
      if (firstOf[v] < 0) {
        firstOf[v] = v;
      }
    }
    boolean fixed = false;
    // the arcs t -> j from the end of a path to the first node of another, with either path changed
    for (int t = 0; t < n; t++) {
      if (succ[t] >= 0) {
        continue;
      }
      int f1 = firstOf[t];
      IntDomain dom = x[t].dom();
      for (ValueEnumeration en = dom.valueEnumeration(); en.hasMoreElements(); ) {
        int j = en.nextElement() - offset;
        if (j < 0 || j >= n || j == t || pred[j] >= 0 || firstOf[j] == f1) {
          continue;
        }
        if (!changed[f1] && !changed[j]) {
          continue;
        }
        int m = join(f1, j);
        int[] move = improving(joined, fresh, m, length(f1) - 1);
        if (move != null) {
          reason[t][j] = arcs(joined, move);
          x[t].domain.inComplement(store.level, x[t], j + offset);
        }
      }
      fixed |= x[t].singleton();
    }
    return fixed;
  }

  private int length(int f) {
    int m = 0;
    for (int v = f; v >= 0; v = succ[v]) {
      m++;
    }
    return m;
  }

  // the path from f, then the path from j, into joined; fresh marks only the joining arc
  private int join(int f, int j) {
    int m = 0;
    for (int v = f; v >= 0; v = succ[v]) {
      fresh[m] = false;
      joined[m++] = v;
    }
    fresh[m - 1] = true;
    for (int v = j; v >= 0; v = succ[v]) {
      fresh[m] = false;
      joined[m++] = v;
    }
    return m;
  }

  /**
   * Finds a 3-opt reconnection of the path p[0..m-1] that keeps its ends and shortens it, removing
   * the arcs i &lt; j &lt; k (arc i is p[i] -&gt; p[i + 1]). When must &ge; 0, the move removes arc
   * must; otherwise it crosses an arc marked in fresh (an arc i with fresh[i] and i in [i, k]).
   *
   * @return {i, k}, the first and last removed arc, or null
   */
  private int[] improving(int[] p, boolean[] isNew, int m, int must) {
    int arcs = m - 1;
    if (arcs < 3) {
      return null;
    }
    // the first new arc at or after each arc
    nextNew[arcs] = Integer.MAX_VALUE;
    for (int i = arcs - 1; i >= 0; i--) {
      nextNew[i] = (must < 0 ? isNew[i] : i == must) ? i : nextNew[i + 1];
    }
    for (int i = 0; i < arcs - 2; i++) {
      int a = p[i];
      int b = p[i + 1];
      long[] da = d[a];
      long[] db = d[b];
      long ab = da[b];
      int kFrom = Math.max(i + 2, nextNew[i]);
      for (int k = kFrom; k < arcs; k++) {
        int e = p[k];
        int f = p[k + 1];
        long ef = d[e][f];
        for (int j = i + 1; j < k; j++) {
          if (must >= 0 && i != must && j != must && k != must) {
            continue;
          }
          int c = p[j];
          int g = p[j + 1];
          long before = ab + d[c][g] + ef;
          // a b..c g..e f: pure exchange a g..e b..c f, and the reversals
          if (da[g] + d[e][b] + d[c][f] < before
              || da[g] + d[e][c] + db[f] < before
              || da[e] + d[g][b] + d[c][f] < before
              || da[c] + db[e] + d[g][f] < before) {
            return new int[] {i, k};
          }
        }
      }
    }
    return null;
  }

  // the arcs i..k of p as (tail, head) pairs, without the arc marked fresh
  private int[] arcs(int[] p, int[] move) {
    int count = 0;
    for (int i = move[0]; i <= move[1]; i++) {
      if (!fresh[i]) {
        count++;
      }
    }
    int[] pairs = new int[2 * count];
    int c = 0;
    for (int i = move[0]; i <= move[1]; i++) {
      if (!fresh[i]) {
        pairs[c++] = p[i];
        pairs[c++] = p[i + 1];
      }
    }
    return pairs;
  }

  private void fail(int[] p, int[] move) {
    int count = move[1] - move[0] + 1;
    failTails = new int[count];
    failHeads = new int[count];
    for (int i = 0; i < count; i++) {
      failTails[i] = p[move[0] + i];
      failHeads[i] = p[move[0] + i + 1];
    }
    throw Store.failException;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    int c = -1;
    for (int v = 0; v < n; v++) {
      if (x[v] == y) {
        c = v;
        break;
      }
    }
    if (c < 0) {
      return false;
    }
    int t = c;
    return DomainCover.entry(trail, entry, (u, o) -> ruledOut(trail, t, u - offset, entry, o), out);
  }

  // the reason that t -> j was ruled out just before a trail position
  private boolean ruledOut(AtomicTrail trail, int t, int j, int position, EntryList out) {
    if (j < 0 || j >= n || j == t) {
      return false;
    }
    // 2-opt: a fixed arc a -> b with d(a,t) + d(b,j) < d(a,b) + d(t,j)
    for (int a = 0; a < n; a++) {
      if (a == t) {
        continue;
      }
      int b = fixedBefore(trail, a, position);
      if (b >= 0 && d[a][t] + d[b][j] < d[a][b] + d[t][j]) {
        addArc(trail, a, position, out);
        return true;
      }
    }
    int[] pairs = reason[t][j];
    if (pairs == null) {
      return false;
    }
    int mark = out.size();
    for (int i = 0; i < pairs.length; i += 2) {
      if (fixedBefore(trail, pairs[i], position) != pairs[i + 1]) {
        out.truncate(mark);
        return false;
      }
      addArc(trail, pairs[i], position, out);
    }
    return true;
  }

  // the successor a was fixed to just before a trail position, or -1
  private int fixedBefore(AtomicTrail trail, int a, int position) {
    int lo = trail.minBefore(x[a], position);
    if (lo != trail.maxBefore(x[a], position)) {
      return -1;
    }
    int b = lo - offset;
    return b >= 0 && b < n && b != a ? b : -1;
  }

  private void addArc(AtomicTrail trail, int a, int position, EntryList out) {
    trail.addLowerBound(x[a], position, out);
    trail.addUpperBound(x[a], position, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int now = trail.size();
    if (failTails == null) {
      return false;
    }
    int mark = out.size();
    for (int i = 0; i < failTails.length; i++) {
      if (fixedBefore(trail, failTails[i], now) != failHeads[i]) {
        out.truncate(mark);
        return false;
      }
      addArc(trail, failTails[i], now, out);
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : TspKOpt([");
    appendArrayToString(result, x);
    result.append("], ").append(offset).append(", ").append(n).append(" x ").append(n).append(')');
    return result.toString();
  }

  @Override
  public TspKOpt copy(VarMap map) {
    // the rules hold for any tour, so a copy removes from the start
    return new TspKOpt(map.get(x), offset, d);
  }
}
