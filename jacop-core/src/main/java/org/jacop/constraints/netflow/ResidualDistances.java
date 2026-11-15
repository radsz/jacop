/*
 * ResidualDistances.java
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

package org.jacop.constraints.netflow;

import static org.jacop.constraints.netflow.simplex.NetworkSimplex.DELETED_ARC;

import java.util.Arrays;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;

/**
 * Shortest path distances in the residual graph of an optimal flow, with the reduced costs as arc
 * lengths. At optimality every residual arc has a non-negative reduced cost, so Dijkstra's
 * algorithm applies. The cheapest way to push one more unit of flow through a residual arc (u, v)
 * costs its reduced cost plus the distance from v back to u.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ResidualDistances {

  /** Distance of a node that was not reached within the limit. */
  static final long UNREACHED = Long.MAX_VALUE;

  private final Node[] nodes;
  private final long[] distance;
  private final int[] heap;
  private final int[] heapPosition;
  private int heapSize;
  private final int[] targetMark;
  private int mark;

  /** The residual arc that reaches each node on its shortest path, or null for the origin. */
  private final Arc[] predecessor;

  /** The least residual capacity on the shortest path of each node, ties broken towards more. */
  private final int[] bottleneck;

  /** The node potentials of the successive shortest paths of {@link #fits}. */
  private final long[] potential;

  /** The arcs whose capacity {@link #fits} changed, to be restored. */
  private Arc[] changed = new Arc[16];

  /** The flow {@link #fits} pushed through each changed arc. */
  private int[] pushed = new int[16];

  /**
   * Prepares the distance computation for a network.
   *
   * @param nodes the nodes of the network, numbered by their index
   */
  ResidualDistances(Node[] nodes) {
    this.nodes = nodes;
    this.distance = new long[nodes.length];
    this.heap = new int[nodes.length];
    this.heapPosition = new int[nodes.length];
    this.targetMark = new int[nodes.length];
    this.predecessor = new Arc[nodes.length];
    this.bottleneck = new int[nodes.length];
    this.potential = new long[nodes.length];
  }

  /**
   * Computes the distances from a node (or to a node when reverse) along residual arcs, up to a
   * limit; distances above the limit are reported as UNREACHED.
   *
   * @param origin the node the paths start at, or end at when reverse
   * @param reverse whether to compute the distances to origin instead of from it
   * @param limit the largest distance of interest
   * @param targets the nodes whose distances are needed; the computation stops once they are known
   * @param count the number of targets
   */
  void compute(Node origin, boolean reverse, long limit, Node[] targets, int count) {
    Arrays.fill(distance, UNREACHED);
    Arrays.fill(heapPosition, -1);
    heapSize = 0;
    mark++;
    int remaining = 0;
    for (int i = 0; i < count; i++) {
      if (targetMark[targets[i].index] != mark) {
        targetMark[targets[i].index] = mark;
        remaining++;
      }
    }
    distance[origin.index] = 0;
    predecessor[origin.index] = null;
    bottleneck[origin.index] = Integer.MAX_VALUE;
    push(origin.index);
    while (heapSize > 0) {
      int u = pop();
      if (targetMark[u] == mark && --remaining == 0) {
        return;
      }
      long du = distance[u];
      Node node = nodes[u];
      for (Arc arc : node.incident) {
        if (arc.index == DELETED_ARC) {
          continue;
        }
        // the residual arc leaving node, or entering it when reverse
        Arc residual = (arc.head == node) != reverse ? arc.sister : arc;
        if (residual.capacity <= 0) {
          continue;
        }
        Node next = reverse ? residual.tail() : residual.head;
        long d = du + residual.reducedCost();
        int b = Math.min(bottleneck[u], residual.capacity);
        if (d <= limit && d < distance[next.index]) {
          distance[next.index] = d;
          predecessor[next.index] = residual;
          bottleneck[next.index] = b;
          if (heapPosition[next.index] == -1) {
            push(next.index);
          } else {
            siftUp(heapPosition[next.index]);
          }
        } else if (d == distance[next.index]
            && heapPosition[next.index] >= 0
            && b > bottleneck[next.index]) {
          // an equally short path with more room, while the node is not settled yet
          predecessor[next.index] = residual;
          bottleneck[next.index] = b;
        }
      }
    }
  }

  /**
   * Returns the distance found by the last computation.
   *
   * @param node a node of the network
   * @return its distance, or UNREACHED
   */
  long distance(Node node) {
    return distance[node.index];
  }

  /**
   * Returns the least residual capacity on the shortest path that the last computation found for a
   * node, or 0 when the path uses one of the excluded arcs (an arc or its sister) or the node was
   * not reached. Following the path is the cost of its length.
   *
   * @param node a node of the network
   * @param excluded an arc whose two directions the path must not use
   * @return the capacity a flow along that path can take, or 0
   */
  int room(Node node, Arc excluded) {
    if (distance[node.index] == UNREACHED) {
      return 0;
    }
    int room = Integer.MAX_VALUE;
    int at = node.index;
    Arc arc = predecessor[at];
    while (arc != null) {
      if (arc == excluded || arc == excluded.sister) {
        return 0;
      }
      room = Math.min(room, arc.capacity);
      // the path is followed back from the node: from the head when it leaves the origin, from
      // the tail when it enters it
      Node previous = arc.head.index == at ? arc.tail() : arc.head;
      at = previous.index;
      arc = predecessor[at];
    }
    return room;
  }

  /**
   * Returns how much flow fits from a node to another through the residual graph without an arc
   * (its two directions), when each unit costs the given cost plus the reduced costs along its path
   * and all of them together at most the budget: the successive shortest paths of a minimum cost
   * flow (Ahuja, Magnanti and Orlin, Network Flows, 1993, ch. 9), with node potentials that keep
   * the arc lengths non-negative. This is the probe of {@link Pruning} for the arc from the second
   * node to the first one, without pivots of the network simplex. The residual capacities are
   * restored before it returns.
   *
   * @param source the node the flow leaves, the head of the arc
   * @param sink the node the flow reaches, the tail of the arc
   * @param excluded the arc
   * @param capacity the most flow asked for
   * @param unitCost the reduced cost of the arc, paid by each unit
   * @param budget the cost the flow may have
   * @return the flow that fits, or -1 when an arc length is negative (not at optimality)
   */
  int fits(Node source, Node sink, Arc excluded, int capacity, long unitCost, long budget) {
    Arrays.fill(potential, 0);
    int changes = 0;
    int flow = 0;
    try {
      while (flow < capacity) {
        long reach = shortestPath(source, sink, excluded);
        if (reach == -2) {
          return -1;
        }
        if (reach == UNREACHED) {
          break;
        }
        // the cost of a unit along the path: the reduced costs of its arcs, which the potentials
        // shift by the potential of the sink (the source keeps potential 0)
        long cost = unitCost + reach + potential[sink.index];
        int amount = Math.min(bottleneck[sink.index], capacity - flow);
        if (cost > 0) {
          amount = (int) Math.min(amount, budget / cost);
        }
        if (amount <= 0) {
          break;
        }
        for (Node at = sink; at != source; ) {
          Arc arc = predecessor[at.index];
          if (changes == changed.length) {
            changed = Arrays.copyOf(changed, 2 * changes);
            pushed = Arrays.copyOf(pushed, 2 * changes);
          }
          changed[changes] = arc;
          pushed[changes++] = amount;
          arc.capacity -= amount;
          arc.sister.capacity += amount;
          at = arc.tail();
        }
        boolean limited = amount < Math.min(bottleneck[sink.index], capacity - flow);
        flow += amount;
        budget -= amount * cost;
        if (limited) {
          break;
        }
        for (int i = 0; i < nodes.length; i++) {
          potential[i] += Math.min(distance[i], reach);
        }
      }
      return flow;
    } finally {
      for (int k = changes - 1; k >= 0; k--) {
        changed[k].capacity += pushed[k];
        changed[k].sister.capacity -= pushed[k];
      }
    }
  }

  // Dijkstra from source to sink over the residual arcs other than excluded (and its sister), with
  // the reduced costs shifted by the potentials as lengths: the distance of sink, UNREACHED, or -2
  // for a negative length
  private long shortestPath(Node source, Node sink, Arc excluded) {
    Arrays.fill(distance, UNREACHED);
    Arrays.fill(heapPosition, -1);
    heapSize = 0;
    distance[source.index] = 0;
    predecessor[source.index] = null;
    bottleneck[source.index] = Integer.MAX_VALUE;
    push(source.index);
    while (heapSize > 0) {
      int u = pop();
      if (u == sink.index) {
        return distance[u];
      }
      long du = distance[u];
      Node node = nodes[u];
      for (Arc arc : node.incident) {
        if (arc.index == DELETED_ARC || arc == excluded || arc == excluded.sister) {
          continue;
        }
        Arc residual = arc.head == node ? arc.sister : arc;
        if (residual.capacity <= 0) {
          continue;
        }
        Node next = residual.head;
        long length = residual.reducedCost() + potential[u] - potential[next.index];
        if (length < 0) {
          return -2;
        }
        long d = du + length;
        if (d < distance[next.index]) {
          distance[next.index] = d;
          predecessor[next.index] = residual;
          bottleneck[next.index] = Math.min(bottleneck[u], residual.capacity);
          if (heapPosition[next.index] == -1) {
            push(next.index);
          } else if (heapPosition[next.index] >= 0) {
            siftUp(heapPosition[next.index]);
          }
        }
      }
    }
    return UNREACHED;
  }

  private void push(int u) {
    heap[heapSize] = u;
    heapPosition[u] = heapSize;
    siftUp(heapSize++);
  }

  private int pop() {
    int top = heap[0];
    heapPosition[top] = -2;
    int last = heap[--heapSize];
    if (heapSize > 0) {
      heap[0] = last;
      heapPosition[last] = 0;
      siftDown(0);
    }
    return top;
  }

  private void siftUp(int i) {
    int u = heap[i];
    while (i > 0) {
      int parent = (i - 1) >> 1;
      int p = heap[parent];
      if (distance[p] <= distance[u]) {
        break;
      }
      heap[i] = p;
      heapPosition[p] = i;
      i = parent;
    }
    heap[i] = u;
    heapPosition[u] = i;
  }

  private void siftDown(int i) {
    int u = heap[i];
    while (true) {
      int child = 2 * i + 1;
      if (child >= heapSize) {
        break;
      }
      if (child + 1 < heapSize && distance[heap[child + 1]] < distance[heap[child]]) {
        child++;
      }
      int c = heap[child];
      if (distance[u] <= distance[c]) {
        break;
      }
      heap[i] = c;
      heapPosition[c] = i;
      i = child;
    }
    heap[i] = u;
    heapPosition[u] = i;
  }
}
