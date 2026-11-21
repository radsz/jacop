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
 * last level back or from level 0 forward. The four reasons are found in one walk back and one walk
 * forward, with a bit per reason on each node, so that each edge is looked at once, and the labels
 * of a level are looked up per block of its edges, not in the domains.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class LayeredGraphExplanation {

  // no entry: a value that was never in the root domain
  private static final int NO_ENTRY = Integer.MIN_VALUE;
  // the cuts of an explanation, as bits of a node's flags: the nearest and the far cut that prefer
  // the source of an edge cut on both sides (0 and 1) and the two that prefer its target (2, 3)
  private static final int SOURCE_FIRST = 0b0011;
  private static final int TARGET_FIRST = 0b1100;
  private static final int ALL = 0b1111;
  private static final int FAR = 0b1010;
  // reachability follows the edges of the reached nodes when they are fewer than this share of
  // their level (1 / FOLLOW_SHARE), and scans the edges of each value otherwise
  private static final int FOLLOW_SHARE = 8;
  // the nodes of a graph whose cuts are also found from the other side (far cuts) and from the
  // labels of each node (failures): on the regular and MDD constraints of the wide set, smaller
  // graphs are walked faster; the property is read when a graph is built (tests set it to 0)
  private static final String LARGE_PROPERTY = "jacop.lcg.graphCutsLargeNodes";
  private static final int LARGE = 4096;

  /** The edges of a graph, ordered by level and within a level by value. */
  static final class Graph {
    final int levels;
    final int[] levelNodes;
    final int[] levelStart;
    final int[] source;
    final int[] value;
    final int[] target;
    // the edges of a level by value: the blocks of level l are levelBlock[l] to levelBlock[l + 1] -
    // 1, block b holds the edges blockStart[b] to blockStart[b + 1] - 1, all labelled
    // blockValue[b]; a pass over the graph skips the blocks of removed values (three of the four
    // letters at most levels deep in the search of WordDesign2-words-mdd, XCSP 2023)
    final int[] levelBlock;
    final int[] blockStart;
    final int[] blockValue;
    // the first node of each level in a numbering of all nodes, level by level
    final int[] nodeBase;
    // the edges into each node, inStart[u] to inStart[u + 1] - 1, by the source and the block of
    // each, and the edges out of each node by the target and the block of each
    final int[] inStart;
    final int[] inSource;
    final int[] inBlock;
    final int[] outStart;
    final int[] outTarget;
    final int[] outBlock;
    // per position of those lists, the end of the run of positions of the same block (the edges
    // of a node are listed block by block)
    final int[] inRunEnd;
    final int[] outRunEnd;
    // per node, the blocks of its level (bit b for the b-th block of the level) of the edges into
    // it and out of it; null when a level has more than 64 blocks or the graph has fewer than
    // LARGE nodes, whose cuts are walked
    final long[] inMask;
    final long[] outMask;
    // the arrays of the explanations made by a thread, kept between them
    final ThreadLocal<Scratch> scratch = ThreadLocal.withInitial(() -> new Scratch(this));

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
      int[] byLevel = new int[size];
      for (int k = 0; k < size; k++) {
        byLevel[next[e[4 * k]]++] = k;
      }
      levelBlock = new int[levels + 1];
      int[][] blocks = orderByValue(e, byLevel);
      blockStart = blocks[0];
      blockValue = blocks[1];
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
      inSource = new int[size];
      inBlock = new int[size];
      outTarget = new int[size];
      outBlock = new int[size];
      int[] in = inStart.clone();
      int[] out = outStart.clone();
      for (int l = 0; l < levels; l++) {
        for (int b = levelBlock[l]; b < levelBlock[l + 1]; b++) {
          for (int k = blockStart[b]; k < blockStart[b + 1]; k++) {
            int at = in[nodeBase[l + 1] + target[k]]++;
            inSource[at] = source[k];
            inBlock[at] = b;
            at = out[nodeBase[l] + source[k]]++;
            outTarget[at] = target[k];
            outBlock[at] = b;
          }
        }
      }
      inRunEnd = runEnds(inStart, inBlock);
      outRunEnd = runEnds(outStart, outBlock);
      boolean narrow = true;
      for (int l = 0; l < levels; l++) {
        narrow &= levelBlock[l + 1] - levelBlock[l] <= Long.SIZE;
      }
      if (narrow && nodeBase[levels + 1] >= Integer.getInteger(LARGE_PROPERTY, LARGE)) {
        inMask = new long[nodeBase[levels + 1]];
        outMask = new long[nodeBase[levels + 1]];
        for (int l = 0; l < levels; l++) {
          for (int b = levelBlock[l]; b < levelBlock[l + 1]; b++) {
            long bit = 1L << (b - levelBlock[l]);
            for (int k = blockStart[b]; k < blockStart[b + 1]; k++) {
              outMask[nodeBase[l] + source[k]] |= bit;
              inMask[nodeBase[l + 1] + target[k]] |= bit;
            }
          }
        }
      } else {
        inMask = null;
        outMask = null;
      }
    }

    private static int[] runEnds(int[] start, int[] block) {
      int[] end = new int[block.length];
      for (int u = 0; u + 1 < start.length; u++) {
        for (int a = start[u + 1] - 1; a >= start[u]; a--) {
          end[a] = a + 1 < start[u + 1] && block[a + 1] == block[a] ? end[a + 1] : a + 1;
        }
      }
      return end;
    }

    // the edges of each level by value, in the order of the description within a value: fills
    // source, value, target and levelBlock and returns the block starts and the block values
    private int[][] orderByValue(int[] e, int[] byLevel) {
      int size = byLevel.length;
      int blocks = 0;
      int[] starts = new int[size + 1];
      int[] values = new int[size];
      for (int l = 0; l < levels; l++) {
        int from = levelStart[l];
        int count = levelStart[l + 1] - from;
        long[] keys = new long[count];
        for (int j = 0; j < count; j++) {
          keys[j] = ((long) e[4 * byLevel[from + j] + 2] << 32) | j;
        }
        Arrays.sort(keys);
        for (int j = 0; j < count; j++) {
          int k = byLevel[from + (int) keys[j]];
          int at = from + j;
          source[at] = e[4 * k + 1];
          value[at] = e[4 * k + 2];
          target[at] = e[4 * k + 3];
          if (j == 0 || value[at] != value[at - 1]) {
            starts[blocks] = at;
            values[blocks++] = value[at];
          }
        }
        levelBlock[l + 1] = blocks;
      }
      starts[blocks] = size;
      return new int[][] {Arrays.copyOf(starts, blocks + 1), Arrays.copyOf(values, blocks)};
    }
  }

  /**
   * The arrays of the explanations of one thread on a graph: the flags of the nodes of each level
   * (all 0 between walks), two lists of nodes and the reachability of the nodes of each level.
   */
  static final class Scratch {
    final byte[][] flags;
    final boolean[][] forward;
    final boolean[][] backward;
    int[] nodes;
    int[] nextNodes;
    // the answers of the searches for a path through unreachable nodes or dead ends, by node in
    // the numbering of all nodes (1 for a path, 2 for none), the nodes answered, and the stack of
    // the search
    final byte[] memo;
    int[] answered;
    int answeredCount;
    final int[] stackNode;
    final int[] stackLevel;
    final int[] stackNext;

    Scratch(Graph graph) {
      int levels = graph.levels;
      flags = new byte[levels + 1][];
      forward = new boolean[levels + 1][];
      backward = new boolean[levels + 1][];
      int widest = 0;
      for (int l = 0; l <= levels; l++) {
        flags[l] = new byte[graph.levelNodes[l]];
        forward[l] = new boolean[graph.levelNodes[l]];
        backward[l] = new boolean[graph.levelNodes[l]];
        widest = Math.max(widest, graph.levelNodes[l]);
      }
      nodes = new int[widest];
      nextNodes = new int[widest];
      memo = new byte[graph.nodeBase[levels + 1]];
      answered = new int[16];
      stackNode = new int[levels + 1];
      stackLevel = new int[levels + 1];
      stackNext = new int[levels + 1];
    }

    void answer(int node, byte value) {
      memo[node] = value;
      if (answeredCount == answered.length) {
        answered = Arrays.copyOf(answered, 2 * answeredCount);
      }
      answered[answeredCount++] = node;
    }

    void clearAnswers() {
      for (int k = 0; k < answeredCount; k++) {
        memo[answered[k]] = 0;
      }
      answeredCount = 0;
    }
  }

  /** A variable's domain just before the position, from its atoms. */
  private static final class Before {
    // the widest range of a domain whose holes are looked up in an array, not by binary search
    private static final int DENSE_RANGE = 1 << 16;

    final IntDomain root;
    final int min;
    final int max;
    final int lower;
    final int upper;
    // the holes in increasing order, and the entry that made each
    final int[] holeValue;
    final int[] holeEntry;
    // for a domain of at most DENSE_RANGE values: per value of [min, max], 1 + the entry of its
    // hole, or 0
    private final int[] dense;

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
      if (min <= max && (long) max - min < DENSE_RANGE) {
        dense = new int[max - min + 1];
        for (int k = 0; k < holes; k++) {
          if (holeValue[k] >= min && holeValue[k] <= max) {
            dense[holeValue[k] - min] = holeEntry[k] + 1;
          }
        }
      } else {
        dense = null;
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

    // the entry that removed v, which is not in the domain, or NO_ENTRY when v was never in the
    // root domain
    int removal(int v) {
      if (!root.contains(v)) {
        return NO_ENTRY;
      }
      if (v < min) {
        return lower;
      }
      return v > max ? upper : hole(v);
    }
  }

  private final AtomicTrail trail;
  private final IntVar[] list;
  private final Graph graph;
  private final int position;
  // the domain of each level's variable just before the position, filled on first use
  private final Before[] levelDomain;
  // the same per block of the level's edges, filled on first use
  private final Labels[] levelLabels;
  private final Scratch scratch;

  LayeredGraphExplanation(AtomicTrail trail, IntVar[] list, Graph graph, int position) {
    this.trail = trail;
    this.list = list;
    this.graph = graph;
    this.position = position;
    this.levelDomain = new Before[list.length];
    this.levelLabels = new Labels[list.length];
    this.scratch = graph.scratch.get();
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
    for (int b = graph.levelBlock[i]; b < graph.levelBlock[i + 1]; b++) {
      if (cut(b, lo, hi, own) && onPath(b, forward[i], backward[i + 1])) {
        return false;
      }
    }
    // removed values of y that were holes before
    for (int k = 0; k < own.holeValue.length; k++) {
      if (own.holeValue[k] >= lo && own.holeValue[k] <= hi) {
        out.add(own.holeEntry[k]);
      }
    }
    // the four cuts, walked together: bit c of a node's flags marks it for cut c
    byte[] unreachable = scratch.flags[i];
    byte[] deadEnd = scratch.flags[i + 1];
    for (int b = graph.levelBlock[i]; b < graph.levelBlock[i + 1]; b++) {
      if (cut(b, lo, hi, own)) {
        markBlock(b, forward[i], backward[i + 1], unreachable, deadEnd);
      }
    }
    EntryList[] reasons = new EntryList[4];
    for (int c = 0; c < 4; c++) {
      reasons[c] = new EntryList();
    }
    far(i, true, forward, reasons);
    far(i + 1, false, backward, reasons);
    walk(i, true, forward, reasons);
    walk(i + 1, false, backward, reasons);
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

  // whether the edges of block b carry a value of [lo, hi] still in the domain, so must be cut
  private boolean cut(int b, int lo, int hi, Before own) {
    int v = graph.blockValue[b];
    return v >= lo && v <= hi && own.contains(v);
  }

  // whether an edge of block b leads from a reached node to a node that reaches the last level
  private boolean onPath(int b, boolean[] reached, boolean[] reaching) {
    for (int k = graph.blockStart[b]; k < graph.blockStart[b + 1]; k++) {
      if (reached[graph.source[k]] && reaching[graph.target[k]]) {
        return true;
      }
    }
    return false;
  }

  // keeps each edge of block b off every path, in the four cuts: cuts 0 and 1 by its source when
  // that is unreachable and else by its target, cuts 2 and 3 by its source only when its target
  // reaches the last level (an edge cut on both sides is cut by its target there)
  private void markBlock(
      int b, boolean[] reached, boolean[] reaching, byte[] unreachable, byte[] deadEnd) {
    for (int k = graph.blockStart[b]; k < graph.blockStart[b + 1]; k++) {
      int s = graph.source[k];
      int t = graph.target[k];
      if (!reached[s]) {
        unreachable[s] |= reaching[t] ? ALL : SOURCE_FIRST;
        if (!reaching[t]) {
          deadEnd[t] |= TARGET_FIRST;
        }
      } else {
        deadEnd[t] |= ALL;
      }
    }
  }

  /*
   * The cuts that keep the flagged nodes of a level away from the other end: from level 0 when up,
   * walking back, or from the last level, walking forward. An edge from a node flagged for cut c is
   * cut by its label's removal, or else its other node is flagged for c too. A nearest cut (c even)
   * takes every removal it meets; a far cut (c odd) goes on through a node that is unreachable from
   * that end anyway (given by reach), to cut nearer the end. The four cuts are walked together, so
   * each edge is looked at once, and cut c adds its removals to reasons[c].
   */
  private void walk(int level, boolean up, boolean[][] reach, EntryList[] reasons) {
    byte[] flags = scratch.flags[level];
    int[] nodes = scratch.nodes;
    int count = 0;
    for (int u = 0; u < flags.length; u++) {
      if (flags[u] != 0) {
        nodes[count++] = u;
      }
    }
    int[] start = up ? graph.inStart : graph.outStart;
    int[] other = up ? graph.inSource : graph.outTarget;
    int[] block = up ? graph.inBlock : graph.outBlock;
    int[] runEnd = up ? graph.inRunEnd : graph.outRunEnd;
    // the level of the edges walked, and the level of the nodes they lead to
    int l = up ? level - 1 : level;
    while (count > 0 && l >= 0 && l < graph.levels) {
      int next = up ? l : l + 1;
      int base = graph.nodeBase[up ? l + 1 : l];
      boolean[] around = reach[next];
      Labels labels = labels(l);
      int firstBlock = graph.levelBlock[l];
      byte[] cited = new byte[graph.levelBlock[l + 1] - firstBlock];
      byte[] nextFlags = scratch.flags[next];
      int[] nextNodes = scratch.nextNodes;
      int nextCount = 0;
      for (int m = 0; m < count; m++) {
        int u = nodes[m];
        int f = flags[u];
        flags[u] = 0;
        int end = start[base + u + 1];
        int a = start[base + u];
        while (a < end) {
          int b = block[a] - firstBlock;
          int stop = runEnd[a];
          if (labels.in[b]) {
            // every cut goes on through the edges of a value in the domain
            for (; a < stop; a++) {
              int w = other[a];
              if (nextFlags[w] == 0) {
                nextNodes[nextCount++] = w;
              }
              nextFlags[w] |= (byte) f;
            }
            continue;
          }
          // a removed value: the nearest cuts take it, a far cut goes on through the nodes
          // unreachable from its end and takes it at the others
          int far = f & FAR;
          int cite = f & ~FAR;
          if (far != 0) {
            for (; a < stop; a++) {
              int w = other[a];
              if (around[w]) {
                cite |= far;
              } else {
                if (nextFlags[w] == 0) {
                  nextNodes[nextCount++] = w;
                }
                nextFlags[w] |= (byte) far;
              }
            }
          }
          a = stop;
          cite &= ~cited[b];
          if (cite != 0) {
            cited[b] |= (byte) cite;
            int e = labels.removal[b];
            if (e != NO_ENTRY) {
              for (int c = 0; c < 4; c++) {
                if ((cite & 1 << c) != 0) {
                  reasons[c].add(e);
                }
              }
            }
          }
        }
      }
      flags = nextFlags;
      scratch.nextNodes = nodes;
      scratch.nodes = nextNodes;
      nodes = nextNodes;
      count = nextCount;
      l = up ? l - 1 : l + 1;
    }
    // the flags of the level the walk stopped at are cleared too
    for (int m = 0; m < count; m++) {
      flags[nodes[m]] = 0;
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
    EntryList[] reasons = new EntryList[4];
    for (int c = 0; c < 4; c++) {
      reasons[c] = new EntryList();
    }
    // cuts 0 and 1 keep the last level unreachable, cuts 2 and 3 keep level 0 away from it
    if (graph.inMask == null) {
      Arrays.fill(scratch.flags[graph.levels], (byte) SOURCE_FIRST);
      walk(graph.levels, true, forward, reasons);
      Arrays.fill(scratch.flags[0], (byte) TARGET_FIRST);
      walk(0, false, backward, reasons);
      addShortest(reasons, out);
      return true;
    }
    // The nearest cut walked back from the last level goes through the nodes that reach it, and
    // takes each removed value on an edge into one of them; the one walked forward from level 0
    // goes through the reached nodes and takes each removed value on an edge out of them. Both
    // are read from the labels of the edges of each node.
    for (int l = 0; l < graph.levels; l++) {
      Labels labels = labels(l);
      if (labels.removed != 0) {
        add(
            labels,
            labels(backward[l + 1], graph.inMask, graph.nodeBase[l + 1], labels.removed),
            reasons[0]);
        add(
            labels,
            labels(forward[l], graph.outMask, graph.nodeBase[l], labels.removed),
            reasons[2]);
      }
    }
    Arrays.fill(scratch.flags[graph.levels], (byte) (SOURCE_FIRST & FAR));
    far(graph.levels, true, forward, reasons);
    walk(graph.levels, true, forward, reasons);
    Arrays.fill(scratch.flags[0], (byte) (TARGET_FIRST & FAR));
    far(0, false, backward, reasons);
    walk(0, false, backward, reasons);
    addShortest(reasons, out);
    return true;
  }

  private static int count(boolean[] set) {
    int n = 0;
    for (boolean b : set) {
      if (b) {
        n++;
      }
    }
    return n;
  }

  // the blocks of removed values among the labels of the edges of the nodes in set
  private static long labels(boolean[] set, long[] mask, int base, long removed) {
    long found = 0;
    for (int u = 0; u < set.length && found != removed; u++) {
      if (set[u]) {
        found |= mask[base + u] & removed;
      }
    }
    return found;
  }

  // adds the entries that removed the values of the blocks given as bits
  private static void add(Labels labels, long blocks, EntryList reason) {
    for (long rest = blocks; rest != 0; rest &= rest - 1) {
      int e = labels.removal[Long.numberOfTrailingZeros(rest)];
      if (e != NO_ENTRY) {
        reason.add(e);
      }
    }
  }

  /*
   * The far cuts (bits 1 and 3) of the walk from the flagged nodes of a level, found from the other
   * side when that is the smaller one; their flags are then taken off, and the walk does the rest.
   * A far cut walks through the nodes that are unreachable (back) or dead ends (forward), most of
   * the graph deep in the search; it takes each removed value on an edge between such a node and
   * a reached node (back) or a node reaching the last level (forward). From the other side these
   * edges are the edges with a removed value out of the reached nodes or into the nodes reaching
   * the last level, each kept when a search finds a path of unreachable nodes or dead ends between
   * the edge and a flagged node.
   */
  private void far(int level, boolean up, boolean[][] reach, EntryList[] reasons) {
    if (graph.inMask == null) {
      return;
    }
    long side = 0;
    long nodes = 0;
    for (int l = up ? 0 : level + 1; up ? l < level : l <= graph.levels; l++) {
      side += count(reach[l]);
      nodes += reach[l].length;
    }
    if (side > nodes - side) {
      return;
    }
    byte[] flags = scratch.flags[level];
    int bits = 0;
    for (byte f : flags) {
      bits |= f;
    }
    for (int c = 1; c < 4; c += 2) {
      if ((bits & 1 << c) != 0) {
        farFrom(level, up, 1 << c, reach, reasons[c]);
      }
    }
    for (int u = 0; u < flags.length; u++) {
      flags[u] &= (byte) ~FAR;
    }
  }

  private void farFrom(int level, boolean up, int bit, boolean[][] reach, EntryList reason) {
    int[] start = up ? graph.outStart : graph.inStart;
    int[] other = up ? graph.outTarget : graph.inSource;
    int[] block = up ? graph.outBlock : graph.inBlock;
    int[] runEnd = up ? graph.outRunEnd : graph.inRunEnd;
    for (int l = up ? 0 : level; up ? l < level : l < graph.levels; l++) {
      Labels labels = labels(l);
      int firstBlock = graph.levelBlock[l];
      // the nodes on the other side, and the level of the far nodes their edges lead to
      int near = up ? l : l + 1;
      int far = up ? l + 1 : l;
      int base = graph.nodeBase[near];
      long cited = 0;
      boolean[] at = reach[near];
      for (int u = 0; u < at.length && cited != labels.removed; u++) {
        if (!at[u]) {
          continue;
        }
        int a = start[base + u];
        while (a < start[base + u + 1]) {
          int b = block[a] - firstBlock;
          int stop = runEnd[a];
          if (!labels.in[b] && (cited & 1L << b) == 0) {
            for (; a < stop; a++) {
              int w = other[a];
              if (!reach[far][w] && pathThrough(far, w, reach, up, level, bit)) {
                cited |= 1L << b;
                break;
              }
            }
          }
          a = stop;
        }
      }
      add(labels, cited, reason);
    }
    scratch.clearAnswers();
  }

  /*
   * Whether node u of a level, outside the set given per level, has a path of nodes outside it,
   * along edges of any value, to a node of level end flagged with bit; down or up the levels. A
   * depth-first search whose answers are kept until the cut is done.
   */
  private boolean pathThrough(int level, int u, boolean[][] set, boolean down, int end, int bit) {
    if (level == end) {
      return (scratch.flags[end][u] & bit) != 0;
    }
    byte[] memo = scratch.memo;
    int g = graph.nodeBase[level] + u;
    if (memo[g] != 0) {
      return memo[g] == 1;
    }
    int[] start = down ? graph.outStart : graph.inStart;
    int[] other = down ? graph.outTarget : graph.inSource;
    int[] stackNode = scratch.stackNode;
    int[] stackLevel = scratch.stackLevel;
    int[] stackNext = scratch.stackNext;
    int depth = 0;
    stackNode[0] = g;
    stackLevel[0] = level;
    stackNext[0] = start[g];
    while (depth >= 0) {
      int x = stackNode[depth];
      if (stackNext[depth] == start[x + 1]) {
        scratch.answer(x, (byte) 2);
        depth--;
        continue;
      }
      int w = other[stackNext[depth]++];
      int next = stackLevel[depth] + (down ? 1 : -1);
      if (set[next][w]) {
        continue;
      }
      int gw = graph.nodeBase[next] + w;
      if (next == end ? (scratch.flags[end][w] & bit) != 0 : memo[gw] == 1) {
        for (int k = 0; k <= depth; k++) {
          scratch.answer(stackNode[k], (byte) 1);
        }
        return true;
      }
      if (next != end && memo[gw] == 0) {
        depth++;
        stackNode[depth] = gw;
        stackLevel[depth] = next;
        stackNext[depth] = start[gw];
      }
    }
    return false;
  }

  // per block of a level: whether its value is in the domain before the position, and else the
  // entry that removed it
  private static final class Labels {
    final boolean[] in;
    final int[] removal;
    // the blocks of removed values, as bits, when the level has at most 64 blocks
    final long removed;

    Labels(Graph graph, int l, Before d) {
      int first = graph.levelBlock[l];
      int n = graph.levelBlock[l + 1] - first;
      in = new boolean[n];
      removal = new int[n];
      long bits = 0;
      for (int b = 0; b < n; b++) {
        int v = graph.blockValue[first + b];
        in[b] = d.contains(v);
        removal[b] = in[b] ? NO_ENTRY : d.removal(v);
        if (!in[b] && b < Long.SIZE) {
          bits |= 1L << b;
        }
      }
      removed = bits;
    }
  }

  private Labels labels(int l) {
    Labels t = levelLabels[l];
    if (t == null) {
      t = new Labels(graph, l, level(l));
      levelLabels[l] = t;
    }
    return t;
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
    boolean[][] reached = scratch.forward;
    Arrays.fill(reached[0], true);
    int[] nodes = all(graph.levelNodes[0]);
    int count = nodes.length;
    for (int l = 0; l < upTo; l++) {
      Arrays.fill(reached[l + 1], false);
      nodes = step(l, true, reached[l], nodes, count, reached[l + 1]);
      count = stepCount;
    }
    return reached;
  }

  // the nodes of levels from down to the last from which the last level is reachable
  private boolean[][] backward(int from) {
    boolean[][] reached = scratch.backward;
    Arrays.fill(reached[graph.levels], true);
    int[] nodes = all(graph.levelNodes[graph.levels]);
    int count = nodes.length;
    for (int l = graph.levels - 1; l >= from; l--) {
      Arrays.fill(reached[l], false);
      nodes = step(l, false, reached[l + 1], nodes, count, reached[l]);
      count = stepCount;
    }
    return reached;
  }

  private static int[] all(int n) {
    int[] nodes = new int[n];
    for (int u = 0; u < n; u++) {
      nodes[u] = u;
    }
    return nodes;
  }

  // the number of nodes step returned
  private int stepCount;

  /*
   * One level of reachability along the edges of level l with values in the domain: from the
   * reached nodes (count of them in nodes, or null when unknown) of level l (forth) or l + 1 to
   * the nodes of the other level, which are marked in to and returned (their number in stepCount,
   * the array null when not listed). Few reached nodes are followed by their own edges, otherwise
   * the edges of each value in the domain are scanned.
   */
  private int[] step(int l, boolean forth, boolean[] at, int[] nodes, int count, boolean[] to) {
    Labels labels = labels(l);
    int firstBlock = graph.levelBlock[l];
    if (nodes != null && count < graph.levelNodes[forth ? l : l + 1] / FOLLOW_SHARE) {
      int[] start = forth ? graph.outStart : graph.inStart;
      int[] other = forth ? graph.outTarget : graph.inSource;
      int[] block = forth ? graph.outBlock : graph.inBlock;
      int base = graph.nodeBase[forth ? l : l + 1];
      int[] next = new int[Math.min(to.length, 16)];
      int n = 0;
      for (int m = 0; m < count; m++) {
        int u = base + nodes[m];
        for (int a = start[u]; a < start[u + 1]; a++) {
          int w = other[a];
          if (!to[w] && labels.in[block[a] - firstBlock]) {
            to[w] = true;
            if (n == next.length) {
              next = Arrays.copyOf(next, Math.min(to.length, 2 * n));
            }
            next[n++] = w;
          }
        }
      }
      stepCount = n;
      return next;
    }
    int[] from = forth ? graph.source : graph.target;
    int[] into = forth ? graph.target : graph.source;
    int n = 0;
    for (int b = firstBlock; b < graph.levelBlock[l + 1]; b++) {
      if (labels.in[b - firstBlock]) {
        for (int k = graph.blockStart[b]; k < graph.blockStart[b + 1]; k++) {
          if (at[from[k]] && !to[into[k]]) {
            to[into[k]] = true;
            n++;
          }
        }
      }
    }
    if (n >= to.length / FOLLOW_SHARE) {
      stepCount = n;
      return null;
    }
    int[] next = new int[n];
    n = 0;
    for (int w = 0; w < to.length; w++) {
      if (to[w]) {
        next[n++] = w;
      }
    }
    stepCount = n;
    return next;
  }
}
