/*
 * ShortTableMdd.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in the material and in all works containing the material.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.core.IntDomain;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;

/**
 * It compiles a large (short) table into a reduced multi-valued decision diagram, in the MiniZinc
 * form of {@link org.jacop.constraints.ExtensionalSupportMdd}: node 1 is the root, node 0 the
 * terminal node, and each edge carries a set of values.
 *
 * <p>Large tables that list a rule rather than data compile into small diagrams. The connectivity
 * table of Benzenoide (XCSP 2023: a hexagon at distance y from the root has a neighbour at y - 1
 * and none closer) has about a million short rows of arity 8 at y in 0..10, and four million at y
 * in 0..12, but its diagram has a few hundred edges, so the rows never reach the propagator.
 *
 * <p>The diagram is built top down: a node is the set of row suffixes still matching the prefix,
 * identified by suffix ids interned from the last column, so two prefixes that leave the same
 * suffixes share one node. Values of a column leading to the same child share one edge, and nodes
 * with the same edges are merged, which makes the diagram reduced. A star matches every value of
 * the column's domain. The construction stops once the diagram grows beyond a given number of
 * edges.
 *
 * <p>Bryant, R. E., Graph-based algorithms for Boolean function manipulation, IEEE Transactions on
 * Computers 35(8), 1986; Cheng, K. C. K. and Yap, R. H. C., An MDD-based generalized arc
 * consistency algorithm for positive and negative table constraints and some global constraints,
 * Constraints 15(2), 2010.
 */
final class ShortTableMdd {

  /**
   * A diagram in the MiniZinc form.
   *
   * @param level the level of each node 1..N, from 1 (the root).
   * @param from the source node of each edge.
   * @param label the values of each edge.
   * @param to the target node of each edge, 0 for the terminal node.
   */
  record Diagram(int[] level, int[] from, IntDomain[] label, int[] to) {}

  /** It is thrown when the diagram has more edges than allowed. */
  private static final class TooLarge extends RuntimeException {
    private static final long serialVersionUID = 1L;

    TooLarge() {
      super(null, null, false, false);
    }
  }

  // Interned row suffixes per column: a suffix of column c is its value at c (or star) and the id
  // of its suffix from column c + 1.
  private final int[][] suffixValue;
  private final int[][] suffixNext;
  private final int star;
  private final IntDomain[] domains;
  private final int edgeLimit;

  // Nodes per column: memo from the set of suffix ids to the node, and interned nodes by edges.
  private final List<Map<IntKey, Integer>> memo = new ArrayList<>();
  private final List<Map<IntKey, Integer>> nodesByEdges = new ArrayList<>();
  // For each node (index = id - 1): its column and its edges as (label, child) pairs.
  private final List<Integer> nodeColumn = new ArrayList<>();
  private final List<IntDomain[]> nodeLabels = new ArrayList<>();
  private final List<int[]> nodeChildren = new ArrayList<>();
  private int edges;

  private ShortTableMdd(
      int[][] suffixValue, int[][] suffixNext, int star, IntDomain[] domains, int edgeLimit) {
    this.suffixValue = suffixValue;
    this.suffixNext = suffixNext;
    this.star = star;
    this.domains = domains;
    this.edgeLimit = edgeLimit;
    for (int c = 0; c < domains.length; c++) {
      memo.add(new HashMap<>());
      nodesByEdges.add(new HashMap<>());
    }
  }

  /**
   * It compiles rows into a reduced diagram.
   *
   * @param rows the rows, each of domains.length values or star.
   * @param star the value that matches every value of its column.
   * @param domains the domain of each column; a star stands for all of it.
   * @param edgeLimit the most edges the diagram may have.
   * @return the diagram, or null when it has more than edgeLimit edges.
   */
  static Diagram compile(List<int[]> rows, int star, IntDomain[] domains, int edgeLimit) {
    int arity = domains.length;
    int n = rows.size();
    if (arity == 0 || n == 0) {
      return null;
    }
    int[][] suffixValue = new int[arity][];
    int[][] suffixNext = new int[arity][];
    int[] next = new int[n];
    int[] current = new int[n];
    for (int c = arity - 1; c >= 0; c--) {
      Map<Long, Integer> ids = new HashMap<>();
      int[] values = new int[16];
      int[] nexts = new int[16];
      for (int r = 0; r < n; r++) {
        int value = rows.get(r)[c];
        long key = ((long) value << 32) | (next[r] & 0xffffffffL);
        Integer id = ids.get(key);
        if (id == null) {
          id = ids.size();
          ids.put(key, id);
          if (id == values.length) {
            values = Arrays.copyOf(values, 2 * id);
            nexts = Arrays.copyOf(nexts, 2 * id);
          }
          values[id] = value;
          nexts[id] = next[r];
        }
        current[r] = id;
      }
      suffixValue[c] = Arrays.copyOf(values, ids.size());
      suffixNext[c] = Arrays.copyOf(nexts, ids.size());
      int[] swap = next;
      next = current;
      current = swap;
    }
    ShortTableMdd builder = new ShortTableMdd(suffixValue, suffixNext, star, domains, edgeLimit);
    int[] all = new int[suffixValue[0].length];
    for (int i = 0; i < all.length; i++) {
      all[i] = i;
    }
    try {
      int root = builder.node(0, all);
      return root < 0 ? null : builder.miniZincForm(root);
    } catch (TooLarge e) {
      return null;
    }
  }

  /**
   * It returns the node of column c for a sorted set of distinct suffix ids of that column, 0 for
   * the terminal node or -1 for the empty diagram.
   */
  private int node(int c, int[] suffixes) {
    if (suffixes.length == 0) {
      return -1;
    }
    if (c == domains.length) {
      return 0;
    }
    IntKey key = new IntKey(suffixes);
    Integer known = memo.get(c).get(key);
    if (known != null) {
      return known;
    }
    // the next suffixes of each explicit value, and of the stars
    Map<Integer, IntList> byValue = new HashMap<>();
    IntList stars = new IntList();
    for (int s : suffixes) {
      int value = suffixValue[c][s];
      if (value == star) {
        stars.add(suffixNext[c][s]);
      } else {
        byValue.computeIfAbsent(value, v -> new IntList()).add(suffixNext[c][s]);
      }
    }
    // child per value; values with the same child share one label
    Map<Integer, IntervalDomain> labelOfChild = new HashMap<>();
    List<Integer> childOrder = new ArrayList<>();
    IntervalDomain explicit = new IntervalDomain();
    int[] values = byValue.keySet().stream().mapToInt(Integer::intValue).sorted().toArray();
    for (int value : values) {
      if (!domains[c].contains(value)) {
        continue;
      }
      explicit.unionAdapt(value, value);
      IntList targets = byValue.get(value).copy();
      targets.addAll(stars);
      addEdge(labelOfChild, childOrder, node(c + 1, targets.sortedDistinct()), value, value);
    }
    if (stars.size > 0) {
      IntDomain rest = domains[c].subtract(explicit);
      int child = node(c + 1, stars.copy().sortedDistinct());
      if (child >= 0 && !rest.isEmpty()) {
        for (IntervalEnumeration e = rest.intervalEnumeration(); e.hasMoreElements(); ) {
          Interval interval = e.nextElement();
          addEdge(labelOfChild, childOrder, child, interval.min(), interval.max());
        }
      }
    }
    int result;
    if (childOrder.isEmpty()) {
      result = -1;
    } else {
      childOrder.sort(null);
      int[] children = childOrder.stream().mapToInt(Integer::intValue).toArray();
      IntDomain[] labels = new IntDomain[children.length];
      List<Integer> keyParts = new ArrayList<>();
      for (int i = 0; i < children.length; i++) {
        labels[i] = labelOfChild.get(children[i]);
        keyParts.add(children[i]);
        keyParts.add(labels[i].noIntervals());
        for (IntervalEnumeration e = labels[i].intervalEnumeration(); e.hasMoreElements(); ) {
          Interval interval = e.nextElement();
          keyParts.add(interval.min());
          keyParts.add(interval.max());
        }
      }
      int[] edgeKey = keyParts.stream().mapToInt(Integer::intValue).toArray();
      IntKey edgesKey = new IntKey(edgeKey);
      Integer same = nodesByEdges.get(c).get(edgesKey);
      if (same != null) {
        result = same;
      } else {
        edges += children.length;
        if (edges > edgeLimit) {
          throw new TooLarge();
        }
        nodeColumn.add(c);
        nodeLabels.add(labels);
        nodeChildren.add(children);
        result = nodeColumn.size();
        nodesByEdges.get(c).put(edgesKey, result);
      }
    }
    memo.get(c).put(key, result);
    return result;
  }

  private static void addEdge(
      Map<Integer, IntervalDomain> labelOfChild,
      List<Integer> childOrder,
      int child,
      int min,
      int max) {
    if (child < 0) {
      return;
    }
    IntervalDomain label = labelOfChild.get(child);
    if (label == null) {
      label = new IntervalDomain();
      labelOfChild.put(child, label);
      childOrder.add(child);
    }
    label.unionAdapt(min, max);
  }

  /** It renumbers the nodes reachable from the root breadth first, the root as node 1. */
  private Diagram miniZincForm(int root) {
    if (root == 0) {
      return null;
    }
    int[] number = new int[nodeColumn.size() + 1];
    List<Integer> order = new ArrayList<>();
    order.add(root);
    number[root] = 1;
    for (int i = 0; i < order.size(); i++) {
      for (int child : nodeChildren.get(order.get(i) - 1)) {
        if (child != 0 && number[child] == 0) {
          order.add(child);
          number[child] = order.size();
        }
      }
    }
    int[] level = new int[order.size()];
    int edgeCount = 0;
    for (int i = 0; i < order.size(); i++) {
      level[i] = nodeColumn.get(order.get(i) - 1) + 1;
      edgeCount += nodeChildren.get(order.get(i) - 1).length;
    }
    int[] from = new int[edgeCount];
    int[] to = new int[edgeCount];
    IntDomain[] label = new IntDomain[edgeCount];
    int e = 0;
    for (int i = 0; i < order.size(); i++) {
      int[] children = nodeChildren.get(order.get(i) - 1);
      IntDomain[] labels = nodeLabels.get(order.get(i) - 1);
      for (int k = 0; k < children.length; k++) {
        from[e] = i + 1;
        to[e] = number[children[k]];
        label[e] = labels[k];
        e++;
      }
    }
    return new Diagram(level, from, label, to);
  }

  /** An int array compared by content. */
  private record IntKey(int[] values, int hash) {
    IntKey(int[] values) {
      this(values, Arrays.hashCode(values));
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof IntKey(int[] other, int otherHash)
          && otherHash == hash
          && Arrays.equals(values, other);
    }

    @Override
    public int hashCode() {
      return hash;
    }

    @Override
    public String toString() {
      return "IntKey" + Arrays.toString(values);
    }
  }

  /** A growable list of ints. */
  private static final class IntList {
    int[] data = new int[8];
    int size;

    void add(int v) {
      if (size == data.length) {
        data = Arrays.copyOf(data, 2 * size);
      }
      data[size++] = v;
    }

    void addAll(IntList other) {
      for (int i = 0; i < other.size; i++) {
        add(other.data[i]);
      }
    }

    IntList copy() {
      IntList c = new IntList();
      c.data = Arrays.copyOf(data, Math.max(8, size));
      c.size = size;
      return c;
    }

    int[] sortedDistinct() {
      int[] a = Arrays.copyOf(data, size);
      Arrays.sort(a);
      int k = 0;
      for (int i = 0; i < a.length; i++) {
        if (k == 0 || a[i] != a[k - 1]) {
          a[k++] = a[i];
        }
      }
      return Arrays.copyOf(a, k);
    }
  }
}
