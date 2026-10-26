/*
 * LayeredGraphExplanation.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints.regular;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of a layered graph constraint by cuts. With the domains just before an entry, F is
 * the set of nodes reachable from level 0 up to the entry's level i and B the set of nodes from
 * which the last level is reachable down from level i + 1. A value v is gone from the i-th variable
 * when no edge of level i labelled v leads from F to B, and the reason is the removal of the labels
 * of the edges leaving F before level i and entering B after it. A failure is the last level
 * unreachable, explained by the edges leaving the reachable nodes.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class LayeredGraphExplanation {

  /** The edges of a graph, ordered by level. */
  static final class Graph {
    final int levels;
    final int[] levelNodes;
    final int[] levelStart;
    final int[] source;
    final int[] value;
    final int[] target;

    Graph(LayeredGraphConstraint.LayeredGraphDescription description) {
      int[] nodes = description.levelNodes;
      levels = nodes.length - 1;
      levelNodes = nodes.clone();
      int size = description.size;
      int[] e = description.edges;
      levelStart = new int[levels + 1];
      for (int k = 0; k < size; k++) {
        levelStart[e[4 * k] + 1]++;
      }
      for (int l = 0; l < levels; l++) {
        levelStart[l + 1] += levelStart[l];
      }
      int[] next = levelStart.clone();
      source = new int[size];
      value = new int[size];
      target = new int[size];
      for (int k = 0; k < size; k++) {
        int at = next[e[4 * k]]++;
        source[at] = e[4 * k + 1];
        value[at] = e[4 * k + 2];
        target[at] = e[4 * k + 3];
      }
    }
  }

  /** A variable's domain just before the position, from its atoms. */
  private static final class Before {
    final IntDomain root;
    final int min;
    final int max;
    final int lower;
    final int upper;
    final Map<Integer, Integer> holes = new HashMap<>();

    Before(AtomicTrail trail, IntVar x, int position) {
      root = trail.rootDomain(x);
      EntryList atoms = new EntryList();
      trail.atomsBefore(x, position, atoms);
      int ge = -1;
      int le = -1;
      for (int k = 0; k < atoms.size(); k++) {
        int f = atoms.get(k);
        switch (trail.kind(f)) {
          case AtomicTrail.GE -> ge = f;
          case AtomicTrail.LE -> le = f;
          default -> holes.put(trail.value(f), f);
        }
      }
      lower = ge;
      upper = le;
      min = trail.minBefore(x, position);
      max = trail.maxBefore(x, position);
    }

    boolean contains(int v) {
      return v >= min && v <= max && root.contains(v) && !holes.containsKey(v);
    }

    // the entry that removed v (none when v was never in the root domain)
    void addRemoval(int v, EntryList out) {
      if (!root.contains(v)) {
        return;
      }
      if (v < min) {
        out.add(lower);
      } else if (v > max) {
        out.add(upper);
      } else {
        out.add(holes.get(v));
      }
    }
  }

  private final AtomicTrail trail;
  private final IntVar[] list;
  private final Graph graph;
  private final int position;
  private final Map<IntVar, Before> domains = new HashMap<>();

  LayeredGraphExplanation(AtomicTrail trail, IntVar[] list, Graph graph, int position) {
    this.trail = trail;
    this.list = list;
    this.graph = graph;
    this.position = position;
  }

  /**
   * Adds to {@code out} the reason of an entry of one of the variables.
   *
   * @param entry the entry
   * @param out where the reason entries are added
   * @return false when some removed value still has a path
   */
  boolean explain(int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    int mark = out.size();
    for (int i = 0; i < list.length; i++) {
      if (list[i] == y && explainAt(i, y, lo, hi, out)) {
        out.sortUnique(mark);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  private boolean explainAt(int i, IntVar y, int lo, int hi, EntryList out) {
    Before own = before(y);
    if (lo < own.min) {
      if (own.lower >= 0) {
        out.add(own.lower);
      }
      lo = own.min;
    }
    if (hi > own.max) {
      if (own.upper >= 0) {
        out.add(own.upper);
      }
      hi = own.max;
    }
    boolean[][] forward = forward(i);
    boolean[][] backward = backward(i + 1);
    // every edge of level i with a removed value that is still in y's domain is cut
    for (int k = graph.levelStart[i]; k < graph.levelStart[i + 1]; k++) {
      int v = graph.value[k];
      if (v >= lo
          && v <= hi
          && own.contains(v)
          && forward[i][graph.source[k]]
          && backward[i + 1][graph.target[k]]) {
        return false;
      }
    }
    // removed values of y that were holes before
    for (Map.Entry<Integer, Integer> h : own.holes.entrySet()) {
      if (h.getKey() >= lo && h.getKey() <= hi) {
        out.add(h.getValue());
      }
    }
    addForwardCut(forward, i, out);
    addBackwardCut(backward, i + 1, out);
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure: no path from level 0 to the last level.
   *
   * @param out where the reason entries are added
   * @return false when there is such a path
   */
  boolean explainFailure(EntryList out) {
    boolean[][] forward = forward(graph.levels);
    for (boolean reached : forward[graph.levels]) {
      if (reached) {
        return false;
      }
    }
    int mark = out.size();
    addForwardCut(forward, graph.levels, out);
    out.sortUnique(mark);
    return true;
  }

  private Before before(IntVar x) {
    return domains.computeIfAbsent(x, z -> new Before(trail, z, position));
  }

  // the nodes of levels 0 to upTo reachable from level 0 along edges with values in the domains
  private boolean[][] forward(int upTo) {
    boolean[][] reached = new boolean[graph.levels + 1][];
    reached[0] = new boolean[graph.levelNodes[0]];
    Arrays.fill(reached[0], true);
    for (int l = 0; l < upTo; l++) {
      reached[l + 1] = new boolean[graph.levelNodes[l + 1]];
      Before d = before(list[l]);
      for (int k = graph.levelStart[l]; k < graph.levelStart[l + 1]; k++) {
        if (reached[l][graph.source[k]] && d.contains(graph.value[k])) {
          reached[l + 1][graph.target[k]] = true;
        }
      }
    }
    return reached;
  }

  // the nodes of levels from down to the last from which the last level is reachable
  private boolean[][] backward(int from) {
    boolean[][] reached = new boolean[graph.levels + 1][];
    reached[graph.levels] = new boolean[graph.levelNodes[graph.levels]];
    Arrays.fill(reached[graph.levels], true);
    for (int l = graph.levels - 1; l >= from; l--) {
      reached[l] = new boolean[graph.levelNodes[l]];
      Before d = before(list[l]);
      for (int k = graph.levelStart[l]; k < graph.levelStart[l + 1]; k++) {
        if (reached[l + 1][graph.target[k]] && d.contains(graph.value[k])) {
          reached[l][graph.source[k]] = true;
        }
      }
    }
    return reached;
  }

  // the removals of the labels of edges leaving the reached nodes before level upTo
  private void addForwardCut(boolean[][] reached, int upTo, EntryList out) {
    for (int l = 0; l < upTo; l++) {
      Before d = before(list[l]);
      for (int k = graph.levelStart[l]; k < graph.levelStart[l + 1]; k++) {
        if (reached[l][graph.source[k]] && !reached[l + 1][graph.target[k]]) {
          d.addRemoval(graph.value[k], out);
        }
      }
    }
  }

  // the removals of the labels of edges entering the reached nodes from level from on
  private void addBackwardCut(boolean[][] reached, int from, EntryList out) {
    for (int l = from; l < graph.levels; l++) {
      Before d = before(list[l]);
      for (int k = graph.levelStart[l]; k < graph.levelStart[l + 1]; k++) {
        if (!reached[l][graph.source[k]] && reached[l + 1][graph.target[k]]) {
          d.addRemoval(graph.value[k], out);
        }
      }
    }
  }
}
