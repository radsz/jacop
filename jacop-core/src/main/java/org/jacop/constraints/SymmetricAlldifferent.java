/*
 * SymmetricAlldifferent.java
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
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Symmetric all different: x[i] = j + offset if and only if x[j] = i + offset, with indexes from 0,
 * so x is an involution of offset..offset + n - 1 (x[i] = i + offset is allowed). It is the same as
 * inverse(x, x).
 *
 * <p>The propagator is domain consistent (Régin, The symmetric alldiff constraint, IJCAI 1999): a
 * solution is a perfect matching of the graph whose edges are the pairs of variables that may take
 * each other's index, so a value is kept when its edge is in some perfect matching. Channeling x[i]
 * = j with x[j] = i, as Assignment does, misses odd cycles: three variables each of which may take
 * either of the other two have no solution. The matchings are found with Edmonds' blossom
 * algorithm, {@link SymmetricMatching}.
 *
 * <p>Explanations for lazy clause generation use Tutte's theorem: a value is removed because the
 * graph without its two endpoints has a set S whose removal leaves more than |S| odd components, so
 * the reason is the missing edges that separate those components.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class SymmetricAlldifferent extends Constraint
    implements SatisfiedPresent, Copyable<SymmetricAlldifferent>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The most removed values of one atom explained one by one. */
  private static final int REMOVED_LIMIT = 256;

  /** The variables. */
  final IntVar[] list;

  /** The value of index 0. */
  final int offset;

  private final int n;
  private final boolean duplicates;
  private final boolean domainConsistent;
  private final SymmetricMatching graph;
  private final boolean[] edge;
  private final boolean[] allowed;

  /**
   * It constructs a domain consistent symmetric all different constraint.
   *
   * @param list the variables
   * @param offset the value that stands for the first variable
   */
  public SymmetricAlldifferent(IntVar[] list, int offset) {
    this(list, offset, true);
  }

  /**
   * It constructs a symmetric all different constraint.
   *
   * @param list the variables
   * @param offset the value that stands for the first variable
   * @param domainConsistent whether every value without a support is removed (one matching search
   *     per variable at each call); otherwise only the values that the other variable does not
   *     allow back (x[i] = j while x[j] cannot be i) are removed and the constraint fails when the
   *     graph has no perfect matching, as with an odd number of variables and no fixed point
   */
  public SymmetricAlldifferent(IntVar[] list, int offset, boolean domainConsistent) {
    checkInputForNullness("list", list);
    this.domainConsistent = domainConsistent;
    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.offset = offset;
    this.n = list.length;
    this.queueIndex = 2;
    this.duplicates = Arrays.stream(list).distinct().count() < n;
    this.graph = new SymmetricMatching(n);
    this.edge = new boolean[n * n];
    this.allowed = new boolean[n * n];
    setScope(list);
  }

  /**
   * It constructs a symmetric all different constraint whose values start at 1.
   *
   * @param list the variables
   */
  public SymmetricAlldifferent(IntVar[] list) {
    this(list, 1);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {
    if (duplicates && n > 1) {
      throw Store.failException;
    }
    for (IntVar x : list) {
      x.domain.in(store.level, x, offset, offset + n - 1);
    }
    Arrays.fill(edge, false);
    for (int i = 0; i < n; i++) {
      for (ValueEnumeration e = list[i].domain.valueEnumeration(); e.hasMoreElements(); ) {
        edge[i * n + e.nextElement() - offset] = true;
      }
    }
    graph.build(edge);
    if (graph.maximum() >= 0) {
      throw Store.failException;
    }
    Arrays.fill(allowed, false);
    markAllowed(graph.mate);
    // the edges of i to j >= i not in the matching: one search decides all of them; those of i to
    // j < i were decided by the search of j
    for (int i = 0; i < n; i++) {
      if (!domainConsistent) {
        for (int j = i; j < n; j++) {
          allowed[i * n + j] = allowed[j * n + i] = edge[i * n + j] && edge[j * n + i];
        }
      } else if (undecided(i)) {
        graph.searchWithout(i);
        for (int j = i; j < n; j++) {
          int w = i == j ? graph.copyOf[i] : j;
          if (w >= 0 && edge[i * n + j] && edge[j * n + i] && graph.outer(w)) {
            allowed[i * n + j] = true;
            allowed[j * n + i] = true;
          }
        }
      }
    }
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      for (int j = 0; j < n; j++) {
        if (edge[i * n + j] && !allowed[i * n + j]) {
          x.domain.inComplement(store.level, x, j + offset);
        }
      }
    }
  }

  // whether i has an edge to some j >= i that the matching does not show allowed
  private boolean undecided(int i) {
    for (int j = i; j < n; j++) {
      if (!allowed[i * n + j]
          && edge[i * n + j]
          && edge[j * n + i]
          && (j != i || graph.copyOf[i] >= 0)) {
        return true;
      }
    }
    return false;
  }

  private void markAllowed(int[] mate) {
    for (int i = 0; i < n; i++) {
      int w = mate[i];
      if (w >= 0 && w < n) {
        allowed[i * n + w] = true;
      } else if (w >= n && graph.original[w] == i) {
        allowed[i * n + i] = true;
      }
    }
  }

  @Override
  public boolean satisfied() {
    for (int i = 0; i < n; i++) {
      if (!list[i].singleton()) {
        return false;
      }
    }
    for (int i = 0; i < n; i++) {
      int j = list[i].value() - offset;
      if (j < 0 || j >= n || list[j].value() != i + offset) {
        return false;
      }
    }
    return !duplicates || n <= 1;
  }

  /**
   * Explains a value removed from x[i]: it was out of x[i] or out of the channel (x[j] had lost i),
   * or no perfect matching holds the edge {i, j}, which a Tutte barrier of the graph without i and
   * j shows.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != SymmetricAlldifferent.class || duplicates) {
      return false;
    }
    IntVar x = trail.variable(entry);
    int i = indexOf(x);
    if (i < 0) {
      return false;
    }
    int lo = Math.max(trail.removedMin(entry), offset);
    int hi = Math.min(trail.removedMax(entry), offset + n - 1);
    if (hi - lo + 1 > REMOVED_LIMIT) {
      return false;
    }
    int mark = out.size();
    boolean built = false;
    for (int v = lo; v <= hi; v++) {
      if (!trail.rootDomain(x).contains(v) || trail.excludedBefore(x, v, entry, out)) {
        continue;
      }
      int j = v - offset;
      if (j != i && trail.excludedBefore(list[j], i + offset, entry, out)) {
        continue;
      }
      if (!built) {
        buildBefore(trail, entry);
        built = true;
        int free = graph.maximum();
        if (free >= 0) {
          graph.barrier(free);
          if (addBarrier(trail, entry, -1, -1, out)) {
            out.sortUnique(mark);
            return true;
          }
          out.truncate(mark);
          return false;
        }
      }
      int w = j == i ? graph.copyOf[i] : j;
      if (w < 0) {
        // x[i] = i was out of the graph before the entry, so it was excluded above
        out.truncate(mark);
        return false;
      }
      if (graph.withEdge(i, w) != null || !addBarrier(trail, entry, i, w, out)) {
        out.truncate(mark);
        return false;
      }
    }
    out.sortUnique(mark);
    return true;
  }

  /** Explains a failure: the graph has no perfect matching, which a Tutte barrier shows. */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != SymmetricAlldifferent.class || duplicates) {
      return false;
    }
    int now = trail.size();
    buildBefore(trail, now);
    int free = graph.maximum();
    if (free < 0) {
      return false;
    }
    graph.barrier(free);
    int mark = out.size();
    if (!addBarrier(trail, now, -1, -1, out)) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  private int indexOf(IntVar x) {
    for (int i = 0; i < n; i++) {
      if (list[i] == x) {
        return i;
      }
    }
    return -1;
  }

  // the graph of the domains just before a trail position
  private void buildBefore(AtomicTrail trail, int position) {
    EntryList scratch = new EntryList();
    Arrays.fill(edge, false);
    for (int i = 0; i < n; i++) {
      IntDomain root = trail.rootDomain(list[i]);
      int min = Math.max(trail.minBefore(list[i], position), offset);
      int max = Math.min(trail.maxBefore(list[i], position), offset + n - 1);
      for (int v = min; v <= max; v++) {
        if (root.contains(v)) {
          scratch.clear();
          edge[i * n + v - offset] = !trail.excludedBefore(list[i], v, position, scratch);
        }
      }
    }
    graph.build(edge);
  }

  /**
   * Adds the atoms that remove the edges the last failed search needs missing: between an outer
   * vertex and a vertex that is neither inner, nor in its blossom, nor u or w. The graph gives a
   * copy only to the variables that may be fixed points, so the others need their own value removed
   * as well.
   */
  private boolean addBarrier(AtomicTrail trail, int position, int u, int w, EntryList out) {
    for (int a = 0; a < n; a++) {
      if (graph.copyOf[a] < 0
          && a != u
          && a != w
          && !trail.excludedBefore(list[a], a + offset, position, out)) {
        return false;
      }
    }
    for (int a = 0; a < graph.vertices; a++) {
      if (!graph.outer(a)) {
        continue;
      }
      if (a < n) {
        for (int b = 0; b < n; b++) {
          if (b != a && graph.separated(a, b, u, w) && !missing(trail, position, a, b, out)) {
            return false;
          }
        }
        int c = graph.copyOf[a];
        if (c >= 0
            && graph.separated(a, c, u, w)
            && !trail.excludedBefore(list[a], a + offset, position, out)) {
          return false;
        }
      } else {
        int o = graph.original[a];
        if (o >= 0
            && graph.separated(a, o, u, w)
            && !trail.excludedBefore(list[o], o + offset, position, out)) {
          return false;
        }
      }
    }
    return true;
  }

  // the atom that removed edge {a, b}: x[a] lost b or x[b] lost a
  private boolean missing(AtomicTrail trail, int position, int a, int b, EntryList out) {
    return trail.excludedBefore(list[a], b + offset, position, out)
        || trail.excludedBefore(list[b], a + offset, position, out);
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : SymmetricAlldifferent([");
    appendArrayToString(result, list);
    result.append("]");
    if (offset != 1) {
      result.append(", ").append(offset);
    }
    result.append(')');
    return result.toString();
  }

  @Override
  public SymmetricAlldifferent copy(VarMap map) {
    return new SymmetricAlldifferent(map.get(list), offset, domainConsistent);
  }
}
