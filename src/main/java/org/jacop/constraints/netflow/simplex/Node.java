/**
 *  Node.java 
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

/**
 *  A node (vertex) in the network.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public final class Node {
	
	/** for debug only */
	public final int initialBalance;
	
	/** a label, great for debugging */
	public final String name;
	
	/** the potential (or dual variable) of the network simplex */
	public int potential;

	/** balance of the last feasible flow */
	public int balance;

	/** change in balance for the next flow computation */
	public int deltaBalance;

	/** connects this node to the root */
	public Arc artificial;

	// we use the parent-thread-depth data structure to store the spanning tree
	public Arc toParent;
	public Node parent; // TODO useful (?) redundancy: parent == toParent.head
	public Node thread;
	public int depth;
	
	/** marks the cut (S,T) for dual pivot */
	boolean marked;

	/** number of connected arcs */
	public int degree;
	
	/** adjacency list (recorded when degree reaches 2) */
	public Arc[] adjacencyList;
	
	public Node(String name, int balance) {
		this.name = name;
		this.balance = 0;
		this.deltaBalance = balance;
		this.initialBalance = balance;
		this.degree = 0;
		this.adjacencyList = new Arc[2];
	}

	/**
	 * Finds the root of the smallest subtree that contains both this node and
	 * that node.
	 * 
	 * @param that
	 *            another node
	 * @return the least common ancestor of this & that
	 */
	public Node lca(Node that) {
		Node i = this;
		Node j = that;
		while (i != j) {
			int delta = i.depth - j.depth;
			if (delta >= 0)
				i = i.parent;
			if (delta <= 0)
				j = j.parent;
		}
		return i;
	}

	/**
	 * Finds the last node on the thread that has a larger depth than this node.
	 * Note that if this node is a leaf node then 'this' is returned.
	 * 
	 * @return the last node on the thread that is in the subtree of this node
	 */
	public Node rightMostLeaf() {
		Node i = this;
		while (i.thread.depth > depth)
			i = i.thread;
		return i;
	}

	/**
	 * Finds the predecessor of this node on the thread. It uses the parent node
	 * as starting point of the search. (Hence, this method cannot be invoked on
	 * the root)
	 * 
	 * @return the node i with i.thread == this
	 */
	public Node predecessorOnThread() {
		Node i = parent;
		while (i.thread != this)
			i = i.thread;
		return i;
	}

	/**
	 * Sets or clears a mark on a subtree rooted at this node
	 * 
	 * @param setMark
	 *            whether to set or clear the mark
	 */
	public void markTree(boolean setMark) {
		Node i = this;
		do {
			i.marked = setMark;
			i = i.thread;
		} while (i.depth > depth);
	}

	/**
	 * Recomputes the potential & depth values in the subtree rooted at this
	 * node.
	 */
	void computePotentials() {
		for (Node i = thread; true; i = i.thread) {
			// the depth value of i might be wrong so we use its parent's depth
			Node j = i.parent;
			if (j == null || j.depth < depth)
				break;

			// arc from i to j
			// c_ij^pi = 0 implies that pi_i = c_ij + pi_j
			Arc ij = i.toParent;
			i.depth = j.depth + 1;
			i.potential = ij.cost + j.potential;
		}
	}

	// a string representation of the state
	public String toString() {
		// TODO only for debugging, otherwise we would use StringBuilder
	    return "[node: " + name + ", balance=" + balance + ", delta="
		+ deltaBalance + ", potential=" + potential + ", depth="
		+ depth + ", parent=" + (parent == null ? null : parent.name)
		+ ", thread=" + (thread == null ? null : thread.name) + "]";
	}
}
