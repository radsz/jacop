/*
 * Arc.java
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

package org.jacop.constraints.netflow.simplex;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import org.jacop.constraints.netflow.ArcCompanion;

/**
 * A directed, residual arc in the graph.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 5.0
 */
public final class Arc {

  /**
   * The head of the arc (where the arc points to). The head of an arc is the tail of its sister
   * arc.
   */
  public final Node head;

  /** The flow of an arc is the residual capacity of its sister arc. */
  public final Arc sister;

  /** The cost of the Arc cost. */
  public int cost;

  /** The unused (i.e. residual) capacity of the arc */
  public int capacity;

  /** Index in lower arcs array. */
  public int index;

  /**
   * The arc companion for constraint API. Only forward arcs have a companion, residual arcs do not.
   */
  public ArcCompanion companion;

  /** Whether this arc is a forward arc or a residual arc. */
  public boolean forward;

  /**
   * Special constructor to create artificial arcs. Should NOT be used in a model. Models should use
   * (or subclass) a NetworkBuilder instead. A NetworkBuilder provides various addArc methods to
   * create arcs more conveniently.
   *
   * @param tail tail of the arc
   * @param head head of the arc
   */
  public Arc(Node tail, Node head) {
    this(tail, head, 0, 0, 0);
  }

  /**
   * General constructor to create arcs. Models should consider to use (or subclass) a
   * NetworkBuilder instead. A NetworkBuilder provides various addArc methods to create arcs more
   * conveniently.
   *
   * @param tail tail of the arc
   * @param head head of the arc
   * @param cost cost-per-unit of the arc
   * @param lowerCapacity lower capacity of the arc
   * @param upperCapacity upper capacity of the arc
   */
  public Arc(Node tail, Node head, int cost, int lowerCapacity, int upperCapacity) {

    if (lowerCapacity > upperCapacity) {
      throw new IllegalArgumentException("lower capacity > upper capacity");
    }

    this.head = head;
    this.cost = cost;
    this.capacity = upperCapacity - lowerCapacity;
    this.index = -2;
    this.forward = true;
    this.sister = new Arc(this, tail);

    if (lowerCapacity != 0) {
      this.companion = new ArcCompanion(this, lowerCapacity);

      // set balance correction for next flow computation
      tail.deltaBalance -= lowerCapacity;
      head.deltaBalance += lowerCapacity;
    }
  }

  // creates the sister arc
  private Arc(Arc sister, Node to) {
    this.head = to;
    this.cost = -sister.cost;
    this.capacity = 0;
    this.index = -2;
    this.sister = sister;
    this.forward = false;
  }

  /**
   * Computes the cost of this arc considering node potentials.
   *
   * @return the reduced cost
   */
  public int reducedCost() {
    // arc from i (tail) to j (head)
    // c_ij^pi = c_ij - pi_i + pi_j
    Node tail = tail();
    return cost - tail.potential + head.potential;
  }

  /**
   * Adjusts the flow on this arc by the given delta, updating residual capacities accordingly.
   *
   * @param delta the amount of flow to add (positive increases flow, negative decreases it).
   */
  public void addFlow(int delta) {
    capacity -= delta;
    sister.capacity += delta;

    if (ASSERTS_ENABLED && !(sister.capacity >= 0)) {
      throw new IllegalStateException(String.valueOf(delta + ", Bad capacity: " + this));
    }
    if (ASSERTS_ENABLED && !(capacity >= 0)) {
      throw new IllegalStateException(String.valueOf(delta + ", Bad capacity: " + this));
    }
  }

  /**
   * Returns the tail node of this arc (the node where the arc originates).
   *
   * @return the tail node, which is the head of the sister arc.
   */
  public Node tail() {
    return sister.head;
  }

  /**
   * Checks whether this arc crosses a cut defined by marked nodes.
   *
   * @param forward true to check for a forward cut (tail marked, head unmarked).
   * @return true if the arc crosses the cut in the specified direction.
   */
  public boolean isInCut(boolean forward) {
    boolean t = tail().marked;
    boolean h = head.marked;
    return (t ^ h) && (t == forward);
  }

  /**
   * Initializes an artificial arc.
   *
   * @param newCost new cost for the arc
   * @param newCapacity new capacity for the arc
   */
  public void set(int newCost, int newCapacity) {

    if (ASSERTS_ENABLED && !(cost == 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(sister.cost == 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(capacity == 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(sister.capacity == 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    cost = newCost;
    sister.cost = -newCost;
    capacity = newCapacity;
    sister.capacity = 0;
    forward = false;
    sister.forward = true;
  }

  /** Clears an artificial arc. */
  public void clear() {

    cost = 0;
    sister.cost = 0;
    capacity = 0;
    sister.capacity = 0;
  }

  /**
   * Returns the cost associated with this arc.
   *
   * @return cost associated with an arc.
   */
  public long longCost() {

    if (cost == 0) {
      return 0L;
    }

    if (!forward) {
      return sister.longCost();
    }

    int flow = sister.capacity;
    if (companion != null) {
      flow += companion.flowOffset;
    }

    return (long) flow * (long) cost;
  }

  /** {@inheritDoc} */
  public String toString() {

    Node tail = tail();
    int flow = sister.capacity;
    int total = capacity + flow;

    ArcCompanion comp = forward ? companion : sister.companion;
    String compstr = comp == null ? "" : ", forward = " + forward + ", companion = " + comp;

    return "["
        + tail.name
        + "->"
        + head.name
        + ", flow="
        + flow
        + "/"
        + total
        + "  reduced="
        + reducedCost()
        + ", index="
        + index
        + compstr
        + "]";
  }

  /**
   * Returns a string representation of this arc's flow information for debugging.
   *
   * @return a string showing tail, head, flow, capacity, and cost details.
   */
  public String toFlow() {
    Node tail = tail();
    int flow = sister.capacity;
    int total = capacity + flow;
    String coststr = cost > 0 ? "+" + cost : "" + cost;
    return tail.name
        + "->"
        + head.name
        + " "
        + flow
        + " / "
        + total
        + ", cost: "
        + flow
        + " * "
        + coststr
        + " = "
        + (flow * cost);
  }

  /**
   * Checks whether this arc or its sister arc has a companion.
   *
   * @return true if either this arc or its sister has a non-null companion.
   */
  public boolean hasCompanion() {
    return (companion != null) || (sister.companion != null);
  }

  /**
   * Returns the companion of this arc, checking the sister arc if this arc has none.
   *
   * @return the arc companion, or null if neither this arc nor its sister has one.
   */
  public ArcCompanion getCompanion() {
    return companion != null ? companion : sister.companion;
  }

  /**
   * Returns a short name for this arc in the format "tail-&gt;head".
   *
   * @return the name string identifying this arc by its endpoint node names.
   */
  public String name() {
    return tail().name + "->" + head.name;
  }
}
