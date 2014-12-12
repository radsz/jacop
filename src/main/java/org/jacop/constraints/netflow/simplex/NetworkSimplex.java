/**
 *  NetworkSimplex.java 
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

import static org.jacop.constraints.netflow.Assert.checkBeforeUpdate;
import static org.jacop.constraints.netflow.Assert.checkFlow;
import static org.jacop.constraints.netflow.Assert.checkInfeasibleNodes;
import static org.jacop.constraints.netflow.Assert.checkOptimality;
import static org.jacop.constraints.netflow.Assert.checkStructure;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.jacop.constraints.netflow.Pruning;

/**
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class NetworkSimplex {
	
	public static final boolean DEBUG = false;// true;
	public static final boolean DEBUG_ALL = true & DEBUG;
	public static final int LARGE_COST = 100000;// 1 << 29; // or 28 ?

	public static final int TREE_ARC = -1;
//	public static final int OTHER_ARC = -2;
	public static final int DELETED_ARC = -3;
	
	// 'nodes' does NOT contain the root
	// 'lower' is the list of arcs at their lower bound
	// lower[*].sister is the list of arcs at their upper bound
	public final Node root;
	public final Node[] nodes;
	public final Arc[] lower;
	public int numArcs;

	// second 'return' value of augmentFlow method
	public Arc blocking;
	
	protected final PivotRule pivotRule;
	
	// the set of nodes with non-zero balance 
	public final Set<Node> infeasibleNodes;
	
	// TODO convenience or overhead ?
	public final List<Arc> allArcs;

	public NetworkSimplex(List<Node> nodes, List<Arc> arcs) {
		
		this.allArcs = new ArrayList<Arc>(arcs);

		this.nodes = nodes.toArray(new Node[nodes.size()]);
		this.lower = allArcs.toArray(new Arc[allArcs.size()]);
		this.root = new Node("(root)", 0);
		this.numArcs = lower.length;
		this.pivotRule = new Danzig(this);
		this.infeasibleNodes = new LinkedHashSet<Node>();

		// initialize index pointers
		for (int i = 0; i < lower.length; i++)
			lower[i].index = lower[i].sister.index = i;

		// create initial spanning tree structure
		Node nextOnThread = root;
		for (Node node : nodes) {
			node.parent = root;
			node.thread = nextOnThread;
			node.depth = 1;
			nextOnThread = node;

			Arc arc = new Arc(node, root);
			node.artificial = arc;
			node.toParent = arc;
			arc.index = TREE_ARC;
			arc.sister.index = TREE_ARC;
			//allArcs.add(arc);

			// if (node.balance > 0) {
			// Arc arc = new Arc(node, root, LARGE_COST, node.balance);
			// arc.addFlow(node.balance);
			// node.toParent = arc;
			// arc.index = arc.sister.index = -1;
			// allArcsForDebug.add(arc);
			// } else {
			// Arc arc = new Arc(root, node, LARGE_COST, -node.balance);
			// arc.addFlow(-node.balance);
			// node.toParent = arc.sister;
			// arc.index = arc.sister.index = -1;
			// allArcsForDebug.add(arc);
			// }
			
			// register infeasible nodes
			if (node.deltaBalance != 0) {
				infeasibleNodes.add(node);
			}
		}
		
		root.thread = nextOnThread;
		root.potential = 0;
		root.depth = 0;
		root.computePotentials();
		
		// Initialize adjacency counter
		for (Arc arc : allArcs) {
			incrementDegree(arc.head, arc);
			incrementDegree(arc.tail(), arc);
		}

		assert (checkFlow(this));
		assert (checkStructure(this));
	}
	
	private void incrementDegree(Node node, Arc myArc) {
//		System.out.println("INCR " + node.name);
		
		// TODO, CRUCIAL, BUG?, assert removed.
		//	assert(node != root);
		
		if (node.degree < 2) {
			node.adjacencyList[node.degree] = myArc.forward ? myArc : myArc.sister;
		}
	
		node.degree++;
	
	}
	
	private void decrementDegree(Node node) {
//		System.out.println("DECR " + node.name);
		assert(node != root);
		
		node.degree--;
		// build adjacency list
		if (node.degree == 2) {
			int i = 0;
			for (Arc arc : allArcs) {
				if (arc.index != DELETED_ARC && (arc.head == node || arc.tail() == node)) {
					assert(i<2) : node + " has extra arc " + arc;
					node.adjacencyList[i++] = arc;
				}
			}
			assert(i==2);
		}
		// update adjacency list
		if (node.degree < 2) {
//			System.out.println( node + "\n" + node.degree + ": " + Arrays.toString(node.adjacencyList) );
			
			Arc arc = node.adjacencyList[0]; 
			if (arc != null && arc.index == DELETED_ARC) {
				node.adjacencyList[0] = node.adjacencyList[1];
				node.adjacencyList[1] = null;
			}
			
			arc = node.adjacencyList[1]; 
			if (arc != null && arc.index == DELETED_ARC)
				node.adjacencyList[1] = null;
			
			assert(
					(node.degree == 1 && ((node.adjacencyList[0] == null) ^ (node.adjacencyList[1] == null)))
					||
					(node.degree == 0 && ((node.adjacencyList[0] == null) && (node.adjacencyList[1] == null)))
					
					) : node + "\n" + node.degree + ": " + Arrays.toString(node.adjacencyList);
		}
	}

	/******************/
	/** Graph update **/

	protected void addArc(Arc arc) {
		assert (arc.index == DELETED_ARC) : arc;
		int index = numArcs++;
		arc.index = arc.sister.index = index;
		if (arc.capacity == 0) {
			// arc at upper bound
			lower[index] = arc.sister;
		} else {
			// arc at lower bound
			lower[index] = arc;
			assert (arc.sister.capacity == 0);
		}
		
		if (arc.companion != null) {
			((Pruning)this).numActiveArcs++;
		}
		
		incrementDegree(arc.head, arc);
		incrementDegree(arc.tail(), arc);
//		System.out.println(numArcs+"  Added : " + arc);
	}
	
	public void addArcWithFlow(Arc arc) {
		assert (arc.index == DELETED_ARC) : arc;
		int index = numArcs++;
		arc.index = arc.sister.index = index;
		if (arc.capacity == 0) {
			// arc at upper bound
			lower[index] = arc.sister;
		} else {
			// arc at lower bound
			lower[index] = arc;
			
			if (arc.sister.capacity > 0) {
				primalStep(arc.sister);
			}
			assert (arc.sister.capacity == 0 || arc.index == TREE_ARC);
		}
		
		if (arc.companion != null) {
			((Pruning)this).numActiveArcs++;
		}
		
		incrementDegree(arc.head, arc);
		incrementDegree(arc.tail(), arc);
//		System.out.println(numArcs+"  Added2 : " + arc);
	}
	
	public void removeArc(Arc arc) {
		// Remove arc from graph
		int index = arc.index;
		assert (index >= 0) : arc.toString();
		if (index < --numArcs) {
			Arc last = lower[numArcs];
			lower[index] = last;
			last.index = last.sister.index = index;
		}
		lower[numArcs] = null;
		arc.index = arc.sister.index = DELETED_ARC;
		
		if (arc.companion != null) {
			((Pruning)this).numActiveArcs--;
		}
		
		decrementDegree(arc.head);
		decrementDegree(arc.tail());
//		System.out.println(numArcs+"  Removed : " + arc);
	}
	
	/****************************/
	/** Primal Network Simplex **/

	/**
	 * 
	 * @param maxPivots
	 * @return the number of pivots performed until optimality was reached, or
	 *         -1 if the maximum number of pivots was reached.
	 */
	public int networkSimplex(int maxPivots) {

		assert (checkFlow(this));
		assert (checkStructure(this));
//		infeasibleNodes.add(arc.tail());
//		infeasibleNodes.add(arc.head);

		// initialize artificial arcs
//		infeasibleNodes.addAll(Arrays.asList(nodes));
		Iterator<Node> it = infeasibleNodes.iterator();
		while (it.hasNext()) {
			Node node = it.next();
			int delta = node.deltaBalance;
			if (delta > 0) {
				// supply node
				Arc arc = node.artificial;
				arc.sister.set(-LARGE_COST, delta);
				if (arc.index == DELETED_ARC) {
					/*addArc(arc);*/ assert false;
				}
				if (arc.index != TREE_ARC)
					lower[arc.index] = arc.sister;
			} else if (delta < 0) {
				// demand node
				Arc arc = node.artificial;
				arc.set(-LARGE_COST, -delta);
				if (arc.index == DELETED_ARC) {
					/*addArc(arc);*/ assert false;
				}
				if (arc.index != TREE_ARC)
					lower[arc.index] = arc;
			} else {
				it.remove();
			}
		}
		root.computePotentials();
		assert(checkInfeasibleNodes(this));

		// Add violating arcs to the tree
		pivotRule.reset();
		int pivots = 0;
		Arc entering;
		while ((entering = pivotRule.next()) != null) {
			// stop when limit is reached
			if (pivots >= maxPivots) {
				pivots = -1;
				break;
			}

			// perform primal step
			primalStep(entering);
			pivots++;
		}

		// System.out.println("----");
		// print();
		// System.out.println("*****");

		// clear artificial arcs
		boolean failure = false;
		it = infeasibleNodes.iterator();
		while (it.hasNext()) {
			Node node = it.next();
			
			// Determine feasibility
			Arc arc = node.artificial;
			int delta = node.deltaBalance;
			int infeasibleFlow;
			if (delta > 0) {
				// supply node
				infeasibleFlow = arc.sister.capacity;
			} else {
				// demand node
				infeasibleFlow = -arc.capacity;
				assert (delta != 0);
			}

			// update node
			arc.clear();
			node.balance += delta - infeasibleFlow;
			node.deltaBalance = infeasibleFlow;
			if (infeasibleFlow != 0) {
				failure = true;
			} else {
//				removeArc(arc);
				it.remove();
			}
		}

		root.computePotentials();
		// if (!failure && pivots >= 0)
		// Assert.assertSame(null, rule.next());

		assert (checkFlow(this));
		assert (checkStructure(this));
		assert (pivots == -1 || failure || checkOptimality(this));

		if (DEBUG) {
			if (pivots == -1)
				System.out.println("Abort after " + maxPivots + " iterations");
			else if (failure)
				System.out.println("Failure after " + pivots + " iterations");
			else
				System.out.println(pivots + " iterations (" + numArcs
						+ " arcs)");
		}
		if (failure && pivots != -1)
			pivots = -2;
		return pivots;
	}

	/**
	 * Performs a primal pivot.
	 * 
	 * @param entering
	 *            a non-tree arc that violates optimality
	 */
	public void primalStep(Arc entering) {
		// entering arc (k,l)
		Node k = entering.tail();
		Node l = entering.head;
		int delta = entering.capacity;

		// augment flow
		delta = augmentFlow(l, k, delta);
		entering.addFlow(delta);

		// find leaving arc
		Arc leaving = this.blocking;

		if (DEBUG_ALL) {
			System.out.println("Entering: " + entering);
			System.out.println("Leaving : " + leaving);
			System.out.println("Delta   : " + delta);
			System.out.println();
		}

		// update tree
		if (leaving == null) {
			lower[entering.index] = entering.sister;
		} else {
			updateTree(leaving, entering);
		}
	}

	/***********************/
	/** Tree manipulation **/

	/**
	 * Augments the flow between two nodes by the maximum amount along the
	 * unique tree path that connects these nodes.
	 * 
	 * @param from
	 *            the source of the flow
	 * @param to
	 *            the sink of the flow
	 * @param delta
	 *            an upper limit on the flow to send
	 * @return the actual flow that was sent. the blocking arc is 'returned' in
	 *         the instance field 'blocking'.
	 */
	public int augmentFlow(Node from, Node to, int delta) {
		assert (delta >= 0);

		blocking = null; // default value
		if (delta == 0)
			return 0;

		// entering arc (k,l)
		Node k = to;
		Node l = from;
		Node apex = k.lca(l);

		// find leaving arc
		for (Node i = l; i != apex; i = i.parent) {
			int arcCapacity = i.toParent.capacity;
			if (delta >= arcCapacity) {
				delta = arcCapacity;
				blocking = i.toParent;
			}
		}
		for (Node i = k; i != apex; i = i.parent) {
			int arcCapacity = i.toParent.sister.capacity;
			if (delta > arcCapacity) {
				delta = arcCapacity;
				blocking = i.toParent.sister;
			}
		}

		// augment flow
		for (Node j = k; j != apex; j = j.parent)
			j.toParent.addFlow(-delta);
		for (Node i = l; i != apex; i = i.parent)
			i.toParent.addFlow(delta);

		return delta;
	}

	/**
	 * TODO prove (or disprove) correctness (and efficiency)
	 * 
	 * Both arcs must form a cycle in the tree and point in the same direction
	 * on that cycle.
	 * 
	 * @param leaving
	 *            the tree arc that leaves the tree
	 * @param entering
	 *            the non-tree arc that enters the tree
	 */
	public void updateTree(Arc leaving, Arc entering) {

		// reverse arcs, to make both point towards the root
		if (leaving.tail().parent != leaving.head) {
			leaving = leaving.sister;
		} else {
			entering = entering.sister;
		}

		Node lastParent = leaving.head;
		Node node = entering.tail();
		Node newParent = entering.head;

		if (DEBUG) {
			System.out.println("leaving  = " + leaving);
			System.out.println("entering = " + entering);
		}

		assert (checkBeforeUpdate(leaving, entering));

		// Let (p,q) and (k,l) be the leaving and entering arcs,
		// respectively
		// - Initially:
		//   o q is the parent of p
		//   o {q,l} are in the same subtree, rooted at the root
		//   o {p,k} are in the same subtree, rooted at p
		// - Make l the new parent of k
		// - Reverse parent/child relation along the path k -> p
		Arc arcToNewParent = entering;
		while (node != lastParent) {
			Node oldParent = node.parent;
			treeSwap(oldParent, node, newParent);

			Arc temp = node.toParent.sister;
			node.toParent = arcToNewParent;
			arcToNewParent = temp;

			newParent = node;
			node = oldParent;
		}

		// insert leaving arc to lower arcs list
		int index = entering.index;
		if (leaving.capacity == 0) {
			lower[index] = leaving.sister;
		} else {
			// here: leaving.sister.capacity == 0;
			
//			System.out.println("Leaving  : " + leaving);
//			System.out.println("Entering : " + entering);
//			System.out.println(leaving == entering);
//			assert (leaving.sister.capacity == 0);
			
			lower[index] = leaving;
		}
		leaving.index = index;
		leaving.sister.index = index;

		// recompute potentials of the modified subtree
		entering.index = TREE_ARC;
		entering.sister.index = TREE_ARC;
		entering.head.computePotentials();
	}

	/**
	 * TODO prove (or disprove) correctness
	 * 
	 * TODO can be 'inlined' in updateTree (but that would decrease readability)
	 * 
	 * Changes the parent of a node and updates the thread data structure (This
	 * operation invalidates the depth values in the subtree)
	 * 
	 * Runs in O(T2) amortized time over all treeSwaps performed by an
	 * updateTree operation where T2 is the size of the subtree that is being
	 * reversed.
	 * 
	 * @param a
	 *            the old parent of a
	 * @param b
	 *            the child node
	 * @param c
	 *            the new parent of a
	 */
	public void treeSwap(Node a, Node b, Node c) {
		// shortcut for multiple arcs (for performance, not correctness)
		if (a == c)
			return;

		Node i = b.predecessorOnThread();
		Node j = b.rightMostLeaf();

		i.thread = j.thread;
		j.thread = c.thread;
		c.thread = b;

		b.parent = c;
	}

	/***************************************/
	/** Parametric (Dual) Network Simplex **/

	/**
	 * Given an optimal flow that satisfies all feasibility constraints except
	 * mass balance on two nodes, the parametric simplex algorithm tries to
	 * achieve feasibility while keeping the solution optimal.
	 * 
	 * TODO do more tests TODO test whether non-feasibility can actually be
	 * detected due to the fact that we have 'artificial' arcs going to the
	 * root.
	 * 
	 * @param source
	 * @param sink
	 * @param balance
	 *            the flow to send from the source to the sink
	 * @param maxPivots
	 *            limits the number of dual pivots
	 * @return the number of pivots on success, -1 if the pivot limit was
	 *         reached, -2 if the problem is infeasible
	 */
	public int parametricStep(Node source, Node sink, int balance, int maxPivots) {
		// check input
		if (balance < 0) {
			Node temp = source;
			source = sink;
			sink = temp;
			balance = -balance;
		} else if (balance == 0) {
			return 1;
		}

		// Augment flow
		balance -= augmentFlow(source, sink, balance);

		int pivots = 0;
		while (balance > 0) {
			// stop when limit is reached
			if (pivots >= maxPivots) {
				if (DEBUG)
					System.out.println("Abort after " + pivots + " iterations");
				return -1;
			}

			// Perform dual pivot
			if (dualPivot(this.blocking)) {
				pivots++;
			} else {
				return -2; // infeasible, TODO define error code or exception
			}

			// Augment flow
			balance -= augmentFlow(source, sink, balance);
		}
		if (DEBUG)
			System.out.println(pivots + " iterations");
		return pivots;
	}

	public boolean dualPivot(Arc leaving) {
		// Perform dual pivot
		Node tree;
		boolean forward;
		if (leaving.tail().parent == leaving.head) {
			tree = leaving.tail();
			forward = true;
		} else {
			tree = leaving.head;
			forward = false;
		}

		// find entering arc
		Arc entering = null;
		int minimumCost = Integer.MAX_VALUE;
		tree.markTree(true);
		for (int i = 0; i < numArcs; i++) {
			Arc arc = lower[i];
//			if (arc.isInCut(forward)) {// && arc.capacity > 0) {
			if (arc.capacity > 0 && arc.isInCut(forward)) {
				
				assert(arc.capacity > 0) : "" + arc;
				
				int reducedCost = arc.reducedCost();
				if (minimumCost > reducedCost) {
					minimumCost = reducedCost;
					entering = arc;
				}
			}
		}
		tree.markTree(false);

		// update tree
		if (entering == null) {
			return false; // infeasible
		} else {
//			System.out.println(".Leaving  : " + leaving);
//			System.out.println(".Entering : " + entering);
//			System.out.println(leaving.sister == entering);
			
			updateTree(leaving.sister, entering);
			return true;
		}
	}

	public long cost(long cutoff) {
		long cost = 0;
		// non-tree arcs
		for (int i = 0; i < numArcs; i++) {
			Arc arc = lower[i];
			cost += arc.longCost();
			if (cost >= cutoff) {
//				throw Store.failException;
				return cutoff;
			}
		}
		// tree arcs
		for (Node node = root.thread; node != root; node = node.thread) {
			cost += node.toParent.longCost();
			if (cost >= cutoff) {
//				throw Store.failException;
				return cutoff;
			} 
		}
		return cost;
	}
	
	/***********/
	/** Debug **/

	// displays the state of the spanning tree and the flow
	public void print() {
	
		System.out.println("Nodes:");
		for (Node n : nodes) {
			System.out.println("\t" + n);
		}
		
		System.out.println("Arcs:");
		
		for (Arc a : allArcs) {
			System.out.println("\t" + a);
		}
		
		System.out.println("Tree:");
		
		for (Node i = root;; i = i.thread) {
			System.out.println("\t" + i + "\t\t" + i.toParent);
			if (i.thread == root)
				break;
		}
		
		System.out.println("Flow");
		int cost = 0;
		for (Arc a : allArcs) {
			if (!a.forward)
				a = a.sister;

			int flow = a.sister.capacity;
			if (a.companion != null)
				flow += a.companion.flowOffset;

			if (flow > 0) {
				System.out.println(flow + "\t" + a.toFlow());
				cost += flow * a.cost;
			}
		}
		System.out.println("Cost: " + cost);
		System.out.println();
	}
}
