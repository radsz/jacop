/**
 *  Asserts.java 
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

package org.jacop.constraints.netflow;

import java.util.ArrayList;
import java.util.List;

import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.NetworkSimplex;
import org.jacop.constraints.netflow.simplex.Node;


/**
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class Assert {

	public static boolean checkFlow(NetworkSimplex g) {
		
		List<Arc> allArcsForDebug = allArcsForDebug(g);
		int sum = 0;
		for (Node n : g.nodes)
			sum += n.balance;

		assert ( sum == 0) : "sum != 0";
		assert ( g.root.balance == 0) : "root balance != 0";

		for (Node n : g.nodes) {
			int del_out = 0, del_in = 0;
			int out = 0, in = 0;
			
			for (Arc a : allArcsForDebug) {
				if (!a.forward)
					a = a.sister;
				
				if (a.companion != null) {
					// lower capacity
					if (a.head == n)
						del_in += a.companion.flowOffset;
					else if (a.tail() == n)
						del_out += a.companion.flowOffset;
				}
				
				if (a.index == -3) {
					// deleted arc
					if (a.head == n)
						del_in += a.sister.capacity;
					else if (a.tail() == n)
						del_out += a.sister.capacity;
					else continue;
				} else {
					// available arc
					if (a.head == n)
						in += a.sister.capacity;
					else if (a.tail() == n)
						out += a.sister.capacity;
					else continue;
				}
//				System.out.println("  " + a);
			}
			
			assert ( n.balance == out - in ) : "Balance on node\n" + "out = " + out + ", in = " + in
					+ ", balance = " + n.balance + "\n" + n + "\n";

			assert (n.initialBalance - n.balance -n.deltaBalance == del_out - del_in) : 
				"Balance on deleted node\n" + "out = " + del_out
					+ ", in = " + del_in + ", balance = " + n.balance
					+ ", delta = " + n.deltaBalance
					+ ", initial = " + n.initialBalance + "\n"
					+ "  out-in = " + (del_out - del_in)
					+ ", initial-balance-delta = "
					+ (n.initialBalance - n.balance -n.deltaBalance) + "\n"
					+ n + "\n";
		}

		{
			int out = 0, in = 0;
			for (Arc a : allArcsForDebug) {
				if (!a.forward)
					a = a.sister;
				if (a.head == g.root)
					in += a.sister.capacity;
				if (a.tail() == g.root)
					out += a.sister.capacity;
			}
			
			assert(0 == out - in) : "Balance on node (root)\n" + "in = " + out + ", out = "
					+ in + ", balance = " + 0 + "\n" + g.root + "\n";
		}

		return true;
	}

	public static boolean checkBeforeUpdate(Arc leaving, Arc entering) {

		assert(leaving.index == -1);
		assert(entering.index >= 0);

		Node k = entering.sister.head;
		Node l = entering.head;
		Node p = leaving.sister.head;
		Node q = leaving.head;

		assert(q == p.parent) : "\nexpected: q is the parent of p\n";
		assert(p == p.lca(k)) : "\nexpected: {p,k} are in the same subtree\n";
		assert(p != p.lca(l) ): "\nexpected: {p,l} are not in the same subtree\n";

		return true;
	}

	public static boolean checkStructure(NetworkSimplex g) {
		List<Arc> allArcsForDebug = allArcsForDebug(g);
		List<Arc> tree = new ArrayList<Arc>();

		long del_cost = 0L;
		int N = g.nodes.length + 1;
		for (Arc arc : allArcsForDebug) {

			// tree arc
			if (arc.index == -1) {
				tree.add(arc);

				Node j = arc.head;
				Node i = arc.sister.head;
				
				if (i.toParent == arc) {
					assert(j == i.parent) : "\ni = " + i + "\nj = " + j + "\nij = " + arc + "\n";
				} else {
					assert(arc.sister == j.toParent) : "\ni = " + i + "\nj = " + j + "\nij = " + arc + "\n";
					assert(i == j.parent) : "\ni = " + i + "\nj = " + j + "\nij = " + arc + "\n";
				}

			}
			// non-tree arc
			else if (arc.index != -3) {
//				String s = arc.toString();

				assert(arc.index == arc.sister.index);
				assert(0 <= arc.index && arc.index < g.numArcs) : g.numArcs + ", " + arc;

				if (arc.capacity > 0) {
					assert(0 == arc.sister.capacity) : "\n" + arc;
					assert(arc == g.lower[arc.index]) : "\n" + arc;
				} else if (arc.sister.capacity > 0) {
					assert(0 == arc.capacity);
					assert(arc.sister == g.lower[arc.index]);
				} else {
					// degenerate arc
					assert(arc.capacity == 0);
					assert(arc.sister.capacity == 0);
					boolean b1 = arc.sister == g.lower[arc.index];
					boolean b2 = arc == g.lower[arc.index];
					assert(b1 ^ b2);
					b1 = arc.head == g.root;
					b2 = arc.sister.head == g.root;
					// assertTrue(s, b1 ^ b2);
				}
			}
			// deleted arc
			else {
				assert(arc.index == -3);
				del_cost += arc.longCost();
				}
		}
		assert(N - 1 == tree.size());
		assert(N - 1 == allArcsForDebug.size() - g.lower.length);
		assert(((Network)g).costOffset == del_cost);
		
		for (int i = 0; i < g.numArcs; i++) {
			Arc arc = g.lower[i];
			assert(arc.sister.capacity == 0);
		}

		assert(g.root.parent == null);
		assert(g.root.toParent == null);
		assert(0 == g.root.balance);
		assert(0 == g.root.potential);
		assert(0 == g.root.depth);
		int x = 1;
		for (Node i = g.root.thread; i != g.root; i = i.thread, ++x) {

			Node p = i.parent;

			assert(p.depth + 1 == i.depth) : "\ni = " + i + "\np = " + p + "\n";
			assert(i == i.toParent.sister.head) : "\ni = " + i + "\np = " + p + "\n";
			assert(p == i.toParent.head) : "\ni = " + i + "\np = " + p + "\n";
			assert(0 == i.toParent.reducedCost()) : "\ni = " + i + "\np = " + p + "\n";
			boolean b1 = tree.contains(i.toParent);
			boolean b2 = tree.contains(i.toParent.sister);
			assert(b1 ^ b2) : "\ni = " + i + "\np = " + p + "\n";
		}
		
		assert(N == x);

		
		for (Node node : g.nodes) {
			List<Arc> adjArcs = new ArrayList<Arc>();
			int count = -1;
			for (Arc arc : allArcsForDebug) {
				if (arc.index != NetworkSimplex.DELETED_ARC && (arc.head == node || arc.tail() == node)) {
					count++;
					adjArcs.add(arc);
				}
			}
			assert(/*node.toString() + "\n" + adjArcs.toString() + "\n" + Arrays.toString(node.adjacencyList) + "\n", */count == node.degree);
			if (node.degree <= 2) {
				int count2 = 0;
				for (Arc arc : node.adjacencyList) {
					if (arc != null) {
						// TODO, CRUCIAL, BUG?, assert removed.
	//					assertTrue(arc.forward);
						assert((arc.head == node) ^ (arc.tail() == node));
						assert(arc.index != NetworkSimplex.DELETED_ARC);
						count2++;
					}
				}
				assert(/*node.toString() + "\n" +adjArcs.toString() + "\n" + Arrays.toString(node.adjacencyList) + "\n", */count == count2);
			}
		}
		
		return true;
	}

	public static boolean checkOptimality(NetworkSimplex g) {
		String s = "";
		for (Arc arc : allArcsForDebug(g)) {
			if (arc.index == -3)
				continue;

			// System.out.println("@@ " + arc);
			int reduced = arc.reducedCost();

			if (arc.capacity > 0 && reduced < 0)
				s += "\n" + arc;
			if (arc.sister.capacity > 0 && reduced > 0)
				s += "\n" + arc;
		}
		// System.out.println(s);
		if (!s.isEmpty())
			assert (false) : "non-optimal arcs:" + s;

		return true;
	}

	public static boolean checkInfeasibleNodes(NetworkSimplex g) {
		
		for (Node node : g.nodes) {
			if (node.deltaBalance == 0) {
				assert(!g.infeasibleNodes.contains(node)) : "" + node;
			} else {
				assert(g.infeasibleNodes.contains(node)) : "" + node;
			}
		}
		
		return true;
	}
	
	public static void forceAsserts() {

		boolean asserts = false;
		assert (asserts = true);
		if (!asserts)
			throw new AssertionError("Assertions disabled");

	}

	
	public static List<Arc> allArcsForDebug(NetworkSimplex g) {
		List<Arc> arcs = new ArrayList<Arc>(g.allArcs);
		for (Node node : g.nodes)
			arcs.add(node.artificial);
		return arcs;
	}
}
