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
    // the first node of each level in a numbering of all nodes, level by level
    final int[] nodeBase;
    // the edges into each node (inEdge[inStart[u] .. inStart[u + 1]]) and out of it
    final int[] inStart;
    final int[] inEdge;
    final int[] outStart;
    final int[] outEdge;

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
      nodeBase = new int[levels + 2];
      for (int l = 0; l <= levels; l++) {
        nodeBase[l + 1] = nodeBase[l] + levelNodes[l];
      }
      inStart = new int[nodeBase[levels + 1] + 1];
      outStart = new int[nodeBase[levels + 1] + 1];
      for (int l = 0; l < levels; l++) {
        for (int k = levelStart[l]; k < levelStart[l + 1]; k++) {
          inStart[nodeBase[l + 1] + target[k] + 1]++;
          outStart[nodeBase[l] + source[k] + 1]++;
        }
      }
      for (int u = 0; u < nodeBase[levels + 1]; u++) {
        inStart[u + 1] += inStart[u];
        outStart[u + 1] += outStart[u];
      }
      inEdge = new int[size];
      outEdge = new int[size];
      int[] in = inStart.clone();
      int[] out = outStart.clone();
      for (int l = 0; l < levels; l++) {
        for (int k = levelStart[l]; k < levelStart[l + 1]; k++) {
          inEdge[in[nodeBase[l + 1] + target[k]]++] = k;
          outEdge[out[nodeBase[l] + source[k]]++] = k;
        }
      }
    }
  }

  /** A variable's domain just before the position, from its atoms. */
  private static final class Before {
    // the widest range of a domain whose holes are looked up in an array, not by binary search
    private static final int DENSE = 1 << 16;

    final IntDomain root;
    final int min;
    final int max;
    final int lower;
    final int upper;
    // the holes in increasing order, and the entry that made each
    final int[] holeValue;
    final int[] holeEntry;
    // for a domain of at most DENSE values: per value of [min, max], 1 + the entry of its hole, or
    // 0
    private final int[] dense;
    // per value of [min, max] (and the two bounds) the cut that last cited its removal, so that a
    // cut cites each removal once
    private final int[] cited;
    private int lowerCited;
    private int upperCited;

    Before(AtomicTrail trail, IntVar x, int position) {
      root = trail.rootDomain(x);
      EntryList atoms = new EntryList();
      trail.atomsBefore(x, position, atoms);
      int ge = -1;
      int le = -1;
      int[] hv = new int[atoms.size()];
      int[] he = new int[atoms.size()];
      int holes = 0;
      for (int k = 0; k < atoms.size(); k++) {
        int f = atoms.get(k);
        switch (trail.kind(f)) {
          case AtomicTrail.GE -> ge = f;
          case AtomicTrail.LE -> le = f;
          default -> {
            hv[holes] = trail.value(f);
            he[holes++] = f;
          }
        }
      }
      lower = ge;
      upper = le;
      min = trail.minBefore(x, position);
      max = trail.maxBefore(x, position);
      long[] sorted = new long[holes];
      for (int k = 0; k < holes; k++) {
        sorted[k] = ((long) hv[k] << 32) | (he[k] & 0xFFFFFFFFL);
      }
      Arrays.sort(sorted);
      holeValue = new int[holes];
      holeEntry = new int[holes];
      for (int k = 0; k < holes; k++) {
        holeValue[k] = (int) (sorted[k] >> 32);
        holeEntry[k] = (int) sorted[k];
      }
      if (min <= max && (long) max - min < DENSE) {
        dense = new int[max - min + 1];
        cited = new int[max - min + 1];
        for (int k = 0; k < holes; k++) {
          if (holeValue[k] >= min && holeValue[k] <= max) {
            dense[holeValue[k] - min] = holeEntry[k] + 1;
          }
        }
      } else {
        dense = null;
        cited = null;
      }
    }

    // the entry of the hole at v, or -1
    private int hole(int v) {
      if (dense != null) {
        return dense[v - min] - 1;
      }
      int k = Arrays.binarySearch(holeValue, v);
      return k >= 0 ? holeEntry[k] : -1;
    }

    boolean contains(int v) {
      return v >= min && v <= max && hole(v) < 0 && root.contains(v);
    }

    // the entry that removed v (none when v was never in the root domain), unless cut already
    // cited it
    void addRemoval(int v, int cut, EntryList out) {
      if (v < min) {
        if (lowerCited != cut && root.contains(v)) {
          lowerCited = cut;
          out.add(lower);
        }
      } else if (v > max) {
        if (upperCited != cut && root.contains(v)) {
          upperCited = cut;
          out.add(upper);
        }
      } else if (cited == null) {
        if (root.contains(v)) {
          out.add(hole(v));
        }
      } else if (cited[v - min] != cut && root.contains(v)) {
        cited[v - min] = cut;
        out.add(dense[v - min] - 1);
      }
    }
  }

  private final AtomicTrail trail;
  private final IntVar[] list;
  private final Graph graph;
  private final int position;
  // the domain of each level's variable just before the position, filled on first use
  private final Before[] levelDomain;
  // the number of cuts made so far, which tells the removals each one cited
  private int cuts;

  LayeredGraphExplanation(AtomicTrail trail, IntVar[] list, Graph graph, int position) {
    this.trail = trail;
    this.list = list;
    this.graph = graph;
    this.position = position;
    this.levelDomain = new Before[list.length];
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
      if (list[i] == y && explainAt(i, lo, hi, out)) {
        out.sortUnique(mark);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  private boolean explainAt(int i, int lo, int hi, EntryList out) {
    Before own = level(i);
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
    for (int k = 0; k < own.holeValue.length; k++) {
      if (own.holeValue[k] >= lo && own.holeValue[k] <= hi) {
        out.add(own.holeEntry[k]);
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
    int cut = ++cuts;
    int[] marked = markedNodes(unreachable);
    int count = marked.length;
    for (int l = level - 1; l >= 0 && count > 0; l--) {
      boolean[] isSource = new boolean[graph.levelNodes[l]];
      int[] sources = new int[graph.levelNodes[l]];
      int sourceCount = 0;
      Before d = level(l);
      for (int m = 0; m < count; m++) {
        int u = graph.nodeBase[l + 1] + marked[m];
        for (int a = graph.inStart[u]; a < graph.inStart[u + 1]; a++) {
          int k = graph.inEdge[a];
          int s = graph.source[k];
          if (d.contains(graph.value[k]) || forward != null && !forward[l][s]) {
            if (!isSource[s]) {
              isSource[s] = true;
              sources[sourceCount++] = s;
            }
          } else {
            d.addRemoval(graph.value[k], cut, out);
          }
        }
      }
      marked = sources;
      count = sourceCount;
    }
  }

  // the nodes of a level that are marked
  private static int[] markedNodes(boolean[] marked) {
    int count = 0;
    for (boolean m : marked) {
      if (m) {
        count++;
      }
    }
    int[] nodes = new int[count];
    count = 0;
    for (int u = 0; u < marked.length; u++) {
      if (marked[u]) {
        nodes[count++] = u;
      }
    }
    return nodes;
  }

  // the removals that keep the nodes of a level marked away from the last level: walking forward,
  // an edge out of a marked node is cut by its label's removal, or else its target is marked; with
  // the backward reachability given, a target that is a dead end is marked even when the label is
  // gone
  private void addBackwardCut(boolean[] deadEnd, int level, boolean[][] backward, EntryList out) {
    int cut = ++cuts;
    int[] marked = markedNodes(deadEnd);
    int count = marked.length;
    for (int l = level; l < graph.levels && count > 0; l++) {
      boolean[] isTarget = new boolean[graph.levelNodes[l + 1]];
      int[] targets = new int[graph.levelNodes[l + 1]];
      int targetCount = 0;
      Before d = level(l);
      for (int m = 0; m < count; m++) {
        int u = graph.nodeBase[l] + marked[m];
        for (int a = graph.outStart[u]; a < graph.outStart[u + 1]; a++) {
          int k = graph.outEdge[a];
          int t = graph.target[k];
          if (d.contains(graph.value[k]) || backward != null && !backward[l + 1][t]) {
            if (!isTarget[t]) {
              isTarget[t] = true;
              targets[targetCount++] = t;
            }
          } else {
            d.addRemoval(graph.value[k], cut, out);
          }
        }
      }
      marked = targets;
      count = targetCount;
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

  private Before level(int l) {
    Before d = levelDomain[l];
    if (d == null) {
      d = new Before(trail, list[l], position);
      levelDomain[l] = d;
    }
    return d;
  }

  // the nodes of levels 0 to upTo reachable from level 0 along edges with values in the domains
  private boolean[][] forward(int upTo) {
    boolean[][] reached = new boolean[graph.levels + 1][];
    reached[0] = new boolean[graph.levelNodes[0]];
    Arrays.fill(reached[0], true);
    for (int l = 0; l < upTo; l++) {
      reached[l + 1] = new boolean[graph.levelNodes[l + 1]];
      Before d = level(l);
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
      Before d = level(l);
      for (int k = graph.levelStart[l]; k < graph.levelStart[l + 1]; k++) {
        if (reached[l + 1][graph.target[k]] && d.contains(graph.value[k])) {
          reached[l][graph.source[k]] = true;
        }
      }
    }
    return reached;
  }
}
