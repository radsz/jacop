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
 * when no edge of level i labelled v leads from F to B: each such edge has its source outside F or
 * its target outside B. The reason keeps those sources unreachable by the nearest cut: walking back
 * from them, an edge into a node that must stay unreachable is cut by the removal of its label when
 * its label is gone, and otherwise its source must stay unreachable too. The targets are kept away
 * from the last level the same way, walking forward. Only the edges that lead to the explained ones
 * are cited, not every edge leaving F (Gange, Stuckey and Szymanek, MDD propagators with
 * explanation, Constraints 2011). The cut nearest to level i is not always the smallest: the walk
 * may also go on through nodes that are unreachable anyway, to cut nearer level 0 (or the last
 * level). Those two walks and the two ways to cut an edge cut on both sides give four reasons, and
 * the shortest is kept. A failure is the last level unreachable, explained the same way from the
 * last level back or from level 0 forward.
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
    EntryList[] reasons = new EntryList[4];
    for (int c = 0; c < 4; c++) {
      reasons[c] = new EntryList();
      addCut(forward, backward, i, lo, hi, own, c < 2, (c & 1) == 0, reasons[c]);
    }
    addShortest(reasons, out);
    return true;
  }

  // adds the one of the reasons with the fewest distinct entries
  private static void addShortest(EntryList[] reasons, EntryList out) {
    EntryList shortest = null;
    for (EntryList r : reasons) {
      r.sortUnique(0);
      if (shortest == null || r.size() < shortest.size()) {
        shortest = r;
      }
    }
    for (int k = 0; k < shortest.size(); k++) {
      out.add(shortest.get(k));
    }
  }

  // the cuts that keep each edge of level i with a value in [lo, hi] off every path, by its source
  // when that is unreachable (preferred when both are, if viaSource) or by its target; the cuts
  // nearest to level i, or else those nearest to the ends
  private void addCut(
      boolean[][] forward,
      boolean[][] backward,
      int i,
      int lo,
      int hi,
      Before own,
      boolean viaSource,
      boolean nearest,
      EntryList out) {
    boolean[] unreachable = new boolean[graph.levelNodes[i]];
    boolean[] deadEnd = new boolean[graph.levelNodes[i + 1]];
    for (int k = graph.levelStart[i]; k < graph.levelStart[i + 1]; k++) {
      int v = graph.value[k];
      if (v >= lo && v <= hi && own.contains(v)) {
        boolean bySource = !forward[i][graph.source[k]];
        if (bySource && (viaSource || backward[i + 1][graph.target[k]])) {
          unreachable[graph.source[k]] = true;
        } else {
          deadEnd[graph.target[k]] = true;
        }
      }
    }
    addForwardCut(unreachable, i, nearest ? null : forward, out);
    addBackwardCut(deadEnd, i + 1, nearest ? null : backward, out);
  }

  // the removals that keep the nodes of a level marked unreachable from level 0: walking back, an
  // edge into a marked node is cut by its label's removal, or else its source is marked; with the
  // forward reachability given, a source that is unreachable is marked even when the label is gone
  private void addForwardCut(boolean[] unreachable, int level, boolean[][] forward, EntryList out) {
    boolean[] marked = unreachable;
    for (int l = level - 1; l >= 0; l--) {
      boolean[] sources = new boolean[graph.levelNodes[l]];
      boolean any = false;
      Before d = before(list[l]);
      for (int k = graph.levelStart[l]; k < graph.levelStart[l + 1]; k++) {
        if (marked[graph.target[k]]) {
          if (d.contains(graph.value[k]) || forward != null && !forward[l][graph.source[k]]) {
            sources[graph.source[k]] = true;
            any = true;
          } else {
            d.addRemoval(graph.value[k], out);
          }
        }
      }
      if (!any) {
        return;
      }
      marked = sources;
    }
  }

  // the removals that keep the nodes of a level marked away from the last level: walking forward,
  // an edge out of a marked node is cut by its label's removal, or else its target is marked; with
  // the backward reachability given, a target that is a dead end is marked even when the label is
  // gone
  private void addBackwardCut(boolean[] deadEnd, int level, boolean[][] backward, EntryList out) {
    boolean[] marked = deadEnd;
    for (int l = level; l < graph.levels; l++) {
      boolean[] targets = new boolean[graph.levelNodes[l + 1]];
      boolean any = false;
      Before d = before(list[l]);
      for (int k = graph.levelStart[l]; k < graph.levelStart[l + 1]; k++) {
        if (marked[graph.source[k]]) {
          if (d.contains(graph.value[k]) || backward != null && !backward[l + 1][graph.target[k]]) {
            targets[graph.target[k]] = true;
            any = true;
          } else {
            d.addRemoval(graph.value[k], out);
          }
        }
      }
      if (!any) {
        return;
      }
      marked = targets;
    }
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
    boolean[][] backward = backward(0);
    boolean[] last = new boolean[graph.levelNodes[graph.levels]];
    Arrays.fill(last, true);
    boolean[] first = new boolean[graph.levelNodes[0]];
    Arrays.fill(first, true);
    EntryList[] reasons = new EntryList[4];
    for (int c = 0; c < 4; c++) {
      reasons[c] = new EntryList();
    }
    addForwardCut(last, graph.levels, null, reasons[0]);
    addForwardCut(last, graph.levels, forward, reasons[1]);
    addBackwardCut(first, 0, null, reasons[2]);
    addBackwardCut(first, 0, backward, reasons[3]);
    addShortest(reasons, out);
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
}
