/*
 * Forest.java
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

package org.jacop.constraints.graph;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Forest states that the selected edges of a graph form a forest of its undirected graph, and that
 * each selected edge has both its nodes selected. The graph has the nodes {@code 0 .. ns.length -
 * 1} and the edges {@code tail[e] - head[e]}; node i is selected when {@code ns[i]} is 1 and edge e
 * when {@code es[e]} is 1.
 *
 * <p>It is meant as a redundant constraint, for a relation the model implies already (as the
 * successor arcs of a path whose positions grow along it do), and it carries that relation to the
 * linear relaxation: there its generalized subtour elimination cuts are separated ({@link
 * org.jacop.constraints.lp.TreeCuts}). It does not propagate; it only checks complete assignments.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Forest extends Constraint implements SatisfiedPresent, Copyable<Forest> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private final IntVar[] ns;
  private final IntVar[] es;
  private final int[] tail;
  private final int[] head;

  /**
   * It constructs a forest constraint.
   *
   * @param ns the Boolean of each node.
   * @param es the Boolean of each edge.
   * @param tail the node of the tail of each edge, from 0.
   * @param head the node of the head of each edge, from 0.
   */
  public Forest(IntVar[] ns, IntVar[] es, int[] tail, int[] head) {
    checkInputForNullness("ns", ns);
    checkInputForNullness("es", es);
    checkInputForNullness("tail", tail);
    checkInputForNullness("head", head);
    if (tail.length != es.length || head.length != es.length) {
      throw new IllegalArgumentException("Forest needs a tail and a head for every edge.");
    }
    for (int e = 0; e < es.length; e++) {
      if (tail[e] < 0 || tail[e] >= ns.length || head[e] < 0 || head[e] >= ns.length) {
        throw new IllegalArgumentException("Forest has an edge to a node that does not exist.");
      }
    }
    for (IntVar v : ns) {
      if (v.min() < 0 || v.max() > 1) {
        throw new IllegalArgumentException("Forest needs 0/1 node variables.");
      }
    }
    for (IntVar v : es) {
      if (v.min() < 0 || v.max() > 1) {
        throw new IllegalArgumentException("Forest needs 0/1 edge variables.");
      }
    }
    this.ns = Arrays.copyOf(ns, ns.length);
    this.es = Arrays.copyOf(es, es.length);
    this.tail = Arrays.copyOf(tail, tail.length);
    this.head = Arrays.copyOf(head, head.length);
    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 0;
    setScope(this.ns, this.es);
  }

  /**
   * The node Booleans.
   *
   * @return the node Booleans, not a copy
   */
  public IntVar[] nodes() {
    return ns;
  }

  /**
   * The edge Booleans.
   *
   * @return the edge Booleans, not a copy
   */
  public IntVar[] edges() {
    return es;
  }

  /**
   * The node of each edge's tail, counted from 0.
   *
   * @return a new array of the tails
   */
  public int[] tails() {
    return tail.clone();
  }

  /**
   * The node of each edge's head, counted from 0.
   *
   * @return a new array of the heads
   */
  public int[] heads() {
    return head.clone();
  }

  @Override
  public void consistency(Store store) {
    // redundant: the model implies the relation, which is here for the linear relaxation; a
    // complete assignment is still checked, so that the constraint holds on its own
    if (allFixed() && !satisfied()) {
      throw Store.failException;
    }
  }

  private boolean allFixed() {
    for (IntVar v : ns) {
      if (!v.singleton()) {
        return false;
      }
    }
    for (IntVar v : es) {
      if (!v.singleton()) {
        return false;
      }
    }
    return true;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public boolean satisfied() {
    for (IntVar v : ns) {
      if (!v.singleton()) {
        return false;
      }
    }
    for (IntVar v : es) {
      if (!v.singleton()) {
        return false;
      }
    }
    int[] parent = new int[ns.length];
    for (int v = 0; v < parent.length; v++) {
      parent[v] = v;
    }
    for (int e = 0; e < es.length; e++) {
      if (es[e].value() == 1) {
        if (ns[tail[e]].value() == 0 || ns[head[e]].value() == 0) {
          return false;
        }
        int a = find(parent, tail[e]);
        int b = find(parent, head[e]);
        if (a == b) {
          return false;
        }
        parent[a] = b;
      }
    }
    return true;
  }

  private static int find(int[] parent, int v) {
    while (parent[v] != v) {
      parent[v] = parent[parent[v]];
      v = parent[v];
    }
    return v;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : Forest(");
    appendArrayToString(result, ns);
    result.append(", ");
    appendArrayToString(result, es);
    result.append(", ").append(Arrays.toString(tail));
    result.append(", ").append(Arrays.toString(head)).append(")");
    return result.toString();
  }

  @Override
  public Forest copy(VarMap map) {
    return new Forest(map.get(ns), map.get(es), tail, head);
  }
}
