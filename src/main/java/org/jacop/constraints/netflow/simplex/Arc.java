/**
 *  Arc.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.constraints.netflow.simplex;

import org.jacop.constraints.netflow.ArcCompanion;

/**
 * 
 * A directed, residual arc in the graph.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public final class Arc {

	/**
	 * The head of the arc (where the arc points to). The head of an arc is the
	 * tail of its sister arc.
	 */
	public final Node head;

	/** The cost of the Arc cost */
	public int cost;

	/** The unused (i.e. residual) capacity of the arc */
	public int capacity;

	/** The flow of an arc is the residual capacity of its sister arc. */
	public final Arc sister;

	/** Index in lower arcs array */
	public int index;

	/**
	 * The arc companion for constraint API. Only forward arcs have a companion,
	 * residual arcs do not.
	 */
	public ArcCompanion companion;

	/** whether this arc is a forward arc or a residual arc */
	public boolean forward;

	/**
	 * Special constructor to create artificial arcs. Should NOT be used in a
	 * model. Models should use (or subclass) a NetworkBuilder instead. A
	 * NetworkBuilder provides various addArc methods to create arcs more
	 * conveniently.
	 * 
	 * @param tail tail of the arc
	 * @param head head of the arc
	 */
	public Arc(Node tail, Node head) {
		this(tail, head, 0, 0, 0);
	}

	/**
	 * General constructor to create arcs. Models should consider to use (or
	 * subclass) a NetworkBuilder instead. A NetworkBuilder provides various
	 * addArc methods to create arcs more conveniently.
	 * 
	 * @param tail tail of the arc
	 * @param head head of the arc
	 * @param cost cost-per-unit of the arc
	 * @param lowerCapacity lower capacity of the arc
	 * @param upperCapacity upper capacity of the arc
	 */
	public Arc(Node tail, 
			   Node head, 
			   int cost, 
			   int lowerCapacity,
			   int upperCapacity) {
		
		if (lowerCapacity > upperCapacity)
			throw new IllegalArgumentException(
					"lower capacity > upper capacity");

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

	public void addFlow(int delta) {
		capacity -= delta;
		sister.capacity += delta;

		assert (sister.capacity >= 0) : delta + ", Bad capacity: " + this;
		assert (capacity >= 0) : delta + ", Bad capacity: " + this;
	}

	public Node tail() {
		return sister.head;
	}

	public boolean isInCut(boolean forward) {
		boolean t = tail().marked;
		boolean h = head.marked;
		return (t ^ h) && (t == forward);
	}

	/**
	 * Initializes an artificial arc
	 * 
	 * @param newCost
	 * @param newCapacity
	 */
	public void set(int newCost, int newCapacity) {
		
		assert(cost == 0);
		assert(sister.cost == 0);
		assert(capacity == 0);
		assert(sister.capacity == 0);

		cost = newCost;
		sister.cost = -newCost;
		capacity = newCapacity;
		sister.capacity = 0;
		forward = false;
		sister.forward = true;
	}

	/** Clears an artificial arc */
	public void clear() {
	
		cost = 0;
		sister.cost = 0;
		capacity = 0;
		sister.capacity = 0;
	
	}

	/**
	 * 
	 * @return cost associated with an arc.
	 */
	public long longCost() {
	
		if (cost == 0)
			return 0L;
		
		if (!forward)
			return sister.longCost();
		
		int flow = sister.capacity;
		if (companion != null)
			flow += companion.flowOffset;
		
		return (long) flow * (long) cost;
	
	}

	/* for debugging */
	public String toString() {
	
		// TODO only for debugging, otherwise we would use StringBuilder
		Node tail = tail();
		int flow = sister.capacity;
		int total = capacity + flow;

		ArcCompanion comp = forward ? companion : sister.companion;
//		String x = (companion == null) ? "" : ", offset=" + companion.flowOffset;
		String compstr = (comp == null) ? "" : ", forward = " + forward + ", companion = " + comp.toString();
		
		return "[" + tail.name + "->" + head.name + ", flow=" + flow
				+ "/" + total + "  reduced=" + reducedCost()
				+ ", index=" + index + compstr + "]";
		
	}

	public String toFlow() {
		// TODO only for debugging, otherwise we would use StringBuilder
		Node tail = tail();
		int flow = sister.capacity;
		int total = capacity + flow;
		String coststr = (cost > 0) ? "+" + cost : "" + cost;
		return tail.name + "->" + head.name + " " + flow + " / " + total
				+ ", cost: " + flow + " * " + coststr + " = " + (flow * cost);
	}

	public boolean hasCompanion() {
		return (companion != null) || (sister.companion != null);
	}
	
	public ArcCompanion getCompanion() {
		return (companion != null) ? companion : sister.companion;
	}
	
	public String name() {
		return tail().name + "->" + head.name;
	}
}
