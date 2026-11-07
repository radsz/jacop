/*
 * CostMdd.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2026 Radoslaw Szymanek
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

package org.jacop.constraints.regular;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.table.Table;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Cost MDD constraint, the MiniZinc {@code cost_mdd}: the values of the variables must label a path
 * from the root to the terminal node of a multi-valued decision diagram whose edges have costs, and
 * cost must equal the sum of the costs of the edges of that path. The diagram may be
 * non-deterministic; cost is then the cost of some path labelled by the values.
 *
 * <p>The diagram is propagated by the shortest and longest path filtering of {@link CostRegular}
 * (Demassey, Pesant and Rousseau 2006; the cost-MDD propagator of Perez and Régin, "Soft and Cost
 * MDD Propagators", AAAI 2017, maintains the same shortest paths): every alive edge lies on a path
 * whose cost is not above the maximum of cost, and on one, possibly another, whose cost is not
 * below its minimum. With cost unconstrained this is the generalized arc consistency of the MDD and
 * cost is narrowed to the cheapest and the most expensive path.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class CostMdd extends CostRegular {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // The diagram in the MiniZinc form: the level (1-based) of each node 1..N and, for each edge,
  // its source node, its label, its cost and its target node, where 0 is the terminal node.
  private final int[] nodeLevel;
  private final int[] from;
  private final IntDomain[] label;
  private final int[] edgeCost;
  private final int[] to;

  /** True when two edges of a node share a value, so that ground variables may label two paths. */
  private boolean nondeterministic;

  /**
   * It constructs a cost MDD constraint from a layered graph as in the MiniZinc {@code cost_mdd}
   * constraint. Node 1 is the root and node 0 the terminal node.
   *
   * @param list the variables, the i-th of them labels the edges leaving the nodes of level i + 1,
   *     without duplicates.
   * @param level the level of each node 1..N, from 1 (the root) to list.length; level[n - 1] is the
   *     level of node n.
   * @param from the source node (1..N) of each edge.
   * @param label the values of each edge.
   * @param edgeCost the cost of each edge.
   * @param to the target node (0..N, where 0 is the terminal node) of each edge.
   * @param cost the variable equal to the sum of the costs of the edges of the path.
   */
  public CostMdd(
      IntVar[] list,
      int[] level,
      int[] from,
      IntDomain[] label,
      int[] edgeCost,
      int[] to,
      IntVar cost) {
    super(list, cost);
    if (level == null || from == null || label == null || edgeCost == null || to == null) {
      throw new IllegalArgumentException("CostMdd: null arguments");
    }
    checkInputForNullness("label", label);
    if (from.length != label.length || from.length != to.length || from.length != edgeCost.length) {
      throw new IllegalArgumentException(
          "CostMdd: from, label, cost and to have different lengths");
    }
    int nodes = level.length;
    if (nodes > 0 && level[0] != 1) {
      throw new IllegalArgumentException("CostMdd: root not at level 1");
    }
    for (int e = 0; e < from.length; e++) {
      if (from[e] < 1 || from[e] > nodes || to[e] < 0 || to[e] > nodes) {
        throw new IllegalArgumentException(
            "CostMdd: edge " + (e + 1) + " outside nodes 1.." + nodes);
      }
      int targetLevel = to[e] == 0 ? list.length + 1 : level[to[e] - 1];
      if (level[from[e] - 1] < 1 || level[from[e] - 1] + 1 != targetLevel) {
        throw new IllegalArgumentException(
            "CostMdd: edge " + (e + 1) + " does not go from a level to the next one");
      }
    }
    this.nodeLevel = Arrays.copyOf(level, level.length);
    this.from = Arrays.copyOf(from, from.length);
    this.label = Arrays.copyOf(label, label.length);
    this.edgeCost = Arrays.copyOf(edgeCost, edgeCost.length);
    this.to = Arrays.copyOf(to, to.length);
    this.numberId = idNumber.incrementAndGet();
  }

  /** It returns the level (0-based) of the edges leaving node n, or -1 when n is not used. */
  private int levelOf(int n) {
    int level = nodeLevel[n - 1] - 1;
    if (level < 0 || level >= list.length || (level == 0 && n != 1)) {
      return -1;
    }
    return level;
  }

  /**
   * It unfolds the edges into one edge per value in the domain of its variable and keeps the nodes
   * that are on a path from the root to the terminal node.
   */
  @Override
  protected void buildGraph() {
    int levels = list.length;
    int nodes = nodeLevel.length;

    // edges ordered by level
    int[] levelEdgeStart = new int[levels + 1];
    for (int e = 0; e < from.length; e++) {
      int level = levelOf(from[e]);
      if (level >= 0) {
        levelEdgeStart[level + 1]++;
      }
    }
    for (int level = 0; level < levels; level++) {
      levelEdgeStart[level + 1] += levelEdgeStart[level];
    }
    int[] order = new int[levelEdgeStart[levels]];
    int[] fill = Arrays.copyOf(levelEdgeStart, levels);
    for (int e = 0; e < from.length; e++) {
      int level = levelOf(from[e]);
      if (level >= 0) {
        order[fill[level]++] = e;
      }
    }

    // an edge is usable when one of its values is in the domain of its variable
    boolean[] usable = new boolean[from.length];
    for (int e : order) {
      IntDomain dom = list[levelOf(from[e])].dom();
      usable[e] = !label[e].isEmpty() && dom.isIntersecting(label[e]);
    }

    // node 0 is the terminal node; nodes reached from the root and reaching the terminal are kept
    boolean[] reached = new boolean[nodes + 1];
    boolean[] reaching = new boolean[nodes + 1];
    if (nodes > 0) {
      reached[1] = true;
    }
    for (int e : order) {
      if (usable[e] && reached[from[e]]) {
        reached[to[e]] = true;
      }
    }
    reaching[0] = true;
    for (int i = order.length - 1; i >= 0; i--) {
      int e = order[i];
      if (usable[e] && reaching[to[e]]) {
        reaching[from[e]] = true;
      }
    }
    if (levels == 0) {
      // the root is the terminal node
      installGraph(new int[] {0, 1}, new int[] {0}, new int[0]);
      return;
    }

    int[] localId = new int[nodes + 1];
    Arrays.fill(localId, -1);
    int[] nodeStart = new int[levels + 2];
    boolean alive = nodes > 0 && reached[1] && reaching[1] && reached[0];
    int[] count = new int[levels + 1];
    if (alive) {
      for (int n = 1; n <= nodes; n++) {
        if (reached[n] && reaching[n] && levelOf(n) >= 0) {
          localId[n] = count[levelOf(n)]++;
        }
      }
      localId[0] = 0;
      count[levels] = 1;
    }
    for (int level = 0; level <= levels; level++) {
      nodeStart[level + 1] = nodeStart[level] + count[level];
    }

    int[] edgeStart = new int[levels + 1];
    int[] edges = new int[64];
    Set<Long> sourceValue = new HashSet<>();
    int edgeCount = 0;
    for (int level = 0; level < levels; level++) {
      edgeStart[level] = edgeCount;
      if (!alive) {
        continue;
      }
      IntDomain dom = list[level].dom();
      for (int i = levelEdgeStart[level]; i < levelEdgeStart[level + 1]; i++) {
        int e = order[i];
        if (!usable[e] || localId[from[e]] < 0 || localId[to[e]] < 0) {
          continue;
        }
        int source = nodeStart[level] + localId[from[e]];
        int target = nodeStart[level + 1] + localId[to[e]];
        for (ValueEnumeration v = label[e].valueEnumeration(); v.hasMoreElements(); ) {
          int value = v.nextElement();
          if (!dom.contains(value)) {
            continue;
          }
          if (4 * edgeCount + 4 > edges.length) {
            edges = Arrays.copyOf(edges, 2 * edges.length);
          }
          if (!sourceValue.add(((long) source << 32) | (value & 0xffffffffL))) {
            nondeterministic = true;
          }
          edges[4 * edgeCount] = source;
          edges[4 * edgeCount + 1] = target;
          edges[4 * edgeCount + 2] = value;
          edges[4 * edgeCount + 3] = edgeCost[e];
          edgeCount++;
        }
      }
    }
    edgeStart[levels] = edgeCount;
    installGraph(nodeStart, edgeStart, edges);
  }

  @Override
  public void consistency(Store store) {
    super.consistency(store);
    // The path filtering keeps cost between the cheapest and the most expensive path. When the
    // diagram is non-deterministic, several paths may remain once every variable is ground, so cost
    // is then restricted to the costs of these paths.
    if (nondeterministic && ground()) {
      IntervalDomain costs = new IntervalDomain();
      pathCosts().stream()
          .filter(c -> c >= IntDomain.MIN_INT && c <= IntDomain.MAX_INT)
          .mapToInt(Long::intValue)
          .sorted()
          .forEach(c -> costs.unionAdapt(c, c));
      cost.domain.in(store.level, cost, costs);
    }
  }

  private boolean ground() {
    for (IntVar x : list) {
      if (!x.singleton()) {
        return false;
      }
    }
    return true;
  }

  /** It returns the costs of the paths labelled by the values of the ground variables. */
  private Set<Long> pathCosts() {
    if (list.length == 0) {
      return Set.of(0L);
    }
    if (nodeLevel.length == 0) {
      return Set.of();
    }
    // the costs of the paths reaching each node of the current level
    List<Set<Long>> reached = new ArrayList<>(nodeLevel.length + 1);
    for (int n = 0; n <= nodeLevel.length; n++) {
      reached.add(null);
    }
    reached.set(1, new HashSet<>(List.of(0L)));
    for (int level = 0; level < list.length; level++) {
      int value = list[level].value();
      for (int e = 0; e < from.length; e++) {
        Set<Long> sums = reached.get(from[e]);
        if (sums == null || levelOf(from[e]) != level || !label[e].contains(value)) {
          continue;
        }
        Set<Long> target = reached.get(to[e]);
        if (target == null) {
          target = new HashSet<>();
          reached.set(to[e], target);
        }
        for (long s : sums) {
          target.add(s + edgeCost[e]);
        }
      }
    }
    Set<Long> sums = reached.get(0);
    return sums == null ? Set.of() : sums;
  }

  @Override
  public boolean satisfied() {
    return cost.singleton() && ground() && pathCosts().contains((long) cost.value());
  }

  /**
   * It decomposes the constraint into a node variable per level, a table of the edges with their
   * costs per variable and a sum of the edge costs. With a non-deterministic diagram the node
   * variables must be ground to fix the path, and with it the cost.
   */
  @Override
  public List<Constraint> decompose(Store store) {

    int levels = list.length;
    List<Constraint> result = new ArrayList<>();
    if (levels == 0) {
      result.add(new XeqC(cost, 0));
      return result;
    }
    IntVar[] q = new IntVar[levels + 1];
    for (int i = 0; i <= levels; i++) {
      q[i] = new IntVar(store, "N" + i, 0, nodeLevel.length);
    }
    IntVar[] w = new IntVar[levels];
    List<List<int[]>> tuples = new ArrayList<>();
    for (int i = 0; i < levels; i++) {
      tuples.add(new ArrayList<>());
    }
    for (int e = 0; e < from.length; e++) {
      int level = levelOf(from[e]);
      if (level < 0) {
        continue;
      }
      for (ValueEnumeration v = label[e].valueEnumeration(); v.hasMoreElements(); ) {
        tuples.get(level).add(new int[] {from[e], v.nextElement(), to[e], edgeCost[e]});
      }
    }
    for (int i = 0; i < levels; i++) {
      int lo = tuples.get(i).stream().mapToInt(t -> t[3]).min().orElse(0);
      int hi = tuples.get(i).stream().mapToInt(t -> t[3]).max().orElse(0);
      w[i] = new IntVar(store, "W" + i, lo, hi);
      result.add(
          new Table(
              new IntVar[] {q[i], list[i], q[i + 1], w[i]}, tuples.get(i).toArray(new int[0][])));
    }
    result.add(new XeqC(q[0], 1));
    result.add(new XeqC(q[levels], 0));
    result.add(new SumInt(w, "==", cost));
    return result;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append("([");
    for (int i = 0; i < list.length; i++) {
      result.append(list[i].id()).append(i + 1 < list.length ? ", " : "");
    }
    result.append("], level=").append(Arrays.toString(nodeLevel));
    result.append(", from=").append(Arrays.toString(from));
    result.append(", label=").append(Arrays.toString(label));
    result.append(", cost=").append(Arrays.toString(edgeCost));
    result.append(", to=").append(Arrays.toString(to));
    result.append(", totalCost=").append(cost.id()).append(")");
    return result.toString();
  }

  @Override
  public CostMdd copy(VarMap map) {
    return new CostMdd(map.get(list), nodeLevel, from, label, edgeCost, to, map.get(cost));
  }
}
