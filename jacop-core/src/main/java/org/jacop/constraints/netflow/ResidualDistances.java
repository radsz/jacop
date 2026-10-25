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
        if (d <= limit && d < distance[next.index]) {
          distance[next.index] = d;
          if (heapPosition[next.index] == -1) {
            push(next.index);
          } else {
            siftUp(heapPosition[next.index]);
          }
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
