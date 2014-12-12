/**
 *  Network.java 
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

import static org.jacop.constraints.netflow.Assert.checkFlow;
import static org.jacop.constraints.netflow.Assert.checkStructure;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;

import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.NetworkSimplex;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * 
 * This class extends the minimum-cost flow network by providing operations and
 * data structures for removal and modification of arcs.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class Network extends NetworkSimplex implements MutableNetwork {
	
	private static final boolean SHOW_CHANGES = false;

	// Data structure for arc removal
	
	/** List of deleted arcs (contains no duplicates) */
	public final List<Arc> deletedArcs;
	
	/** Number of deleted arcs at each level */
	public TimeStamp<Integer> deletedSize;
	
	/** Cost due to deleted arcs */
	public long costOffset;

	// Data structure for arc modification
	// (similar to geost constraint)

	/** List of modified arcs (may contain duplicates) */
	public final List<ArcCompanion> modifiedArcs;
	
	/** Number of modified arcs at each level */
	public TimeStamp<Integer> modifiedSize;
	
	/** Set of arcs modified at current level */
	public final LinkedHashSet<ArcCompanion> lastModifiedArcs;

	// Data structure for pruning
//	private final Pruning pruning;
	
	/** Whether the network is a minimum-cost or a maximum-gain problem */
	// public final boolean isMinimizing;

	/** The store */
	public Store store;

	public Network(List<Node> nodes, List<Arc> arcs) {
	
		super(nodes, arcs);
		this.deletedArcs = new ArrayList<Arc>();
		this.modifiedArcs = new ArrayList<ArcCompanion>();
		this.lastModifiedArcs = new LinkedHashSet<ArcCompanion>();
		this.costOffset = 0L;
		// this.isMinimizing = true;
	
	}

	public void initialize(Store store) {

		this.store = store;
		this.deletedSize = new TimeStamp<Integer>(store, 0);
		this.modifiedSize = new TimeStamp<Integer>(store, 0);
	
	}

	// adds an arc at its lower or upper bound
	private void add(Arc arc) {

		assert (arc.forward);
		
		assert (arc.capacity == 0 || arc.sister.capacity == 0);

		if (SHOW_CHANGES) {
			System.out.println("Adding arc :  " + arc);
		}

		// adjust node balance
		int flow = arc.sister.capacity;
		if (flow > 0) {
			arc.tail().balance += flow;
			arc.head.balance -= flow;
		}

		// add to non-tree arcs
		addArc(arc);
		costOffset -= arc.longCost();

		if (arc.companion != null) {
//			((Pruning)this).numActiveArcs++;
			if (arc.companion.structure != null) {
				arc.companion.structure.ungroundArc(arc.companion.arcID);
			}
		}
	}

	// removes an arc at its lower or upper bound
	public void remove(Arc arc) {
	
		if (!arc.forward)
			arc = arc.sister;

		assert (arc.capacity == 0 || arc.sister.capacity == 0) : "Arc not at lower or upper bound";
		assert (checkFlow(this));
		assert (checkStructure(this));

		if (SHOW_CHANGES) {
			// print();
			System.out.println("Before removing arc: " + arc);
			// System.out.println("  tail: " + arc.tail());
			// System.out.println("  head: " + arc.head);
		}

		// Remove arc from tree, if it is a tree arc
		// TODO perform dual pivot instead ?
		// (it is slower and may fail, but preserves optimality)
		
		if (arc.index == TREE_ARC /* && !dualPivot(arc) */) {
			Node tail = arc.tail();
			// pointing upwards
			if (tail.parent == arc.head) {
//				addArc(tail.artificial);
				updateTree(arc.sister, tail.artificial);
			}
			// pointing downwards
			else {
				assert (arc.head.parent == tail);
//				addArc(arc.head.artificial);
				updateTree(arc, arc.head.artificial);
			}
		}

		// Remove arc from graph
		removeArc(arc);

		// adjust node balance
		int flow = arc.sister.capacity;
		if (flow > 0) {
			arc.tail().balance -= flow;
			arc.head.balance += flow;
		}
		
		// register infeasible nodes
		if (arc.head.deltaBalance != 0) {
			infeasibleNodes.add(arc.head);
		}
		if (arc.tail().deltaBalance != 0) {
			infeasibleNodes.add(arc.tail());
		}

		// add arc to deleted arcs data structure
		costOffset += arc.longCost();
		arc.index = arc.sister.index = DELETED_ARC;
		deletedArcs.add(arc);
		deletedSize.update(deletedArcs.size());

		if (arc.companion != null) {
//			((Pruning)this).numActiveArcs--;
		}
		
		if (SHOW_CHANGES) {
			// System.out.println("After removing arc: " + arc);
			// System.out.println("  tail: " + arc.tail());
			// System.out.println("  head: " + arc.head);
		}
	}

	public void modified(ArcCompanion companion) {
		
		if (lastModifiedArcs.add(companion)) {
			modifiedArcs.add(companion);
			modifiedSize.update(modifiedArcs.size());
		}

		// register infeasible nodes
		Arc arc = companion.arc;
		if (arc.head.deltaBalance != 0) {
			infeasibleNodes.add(arc.head);
		}
		if (arc.tail().deltaBalance != 0) {
			infeasibleNodes.add(arc.tail());
		}
		
		if (SHOW_CHANGES) {
			System.out.println("  modified arc : " + companion.arc
					+ ", time = " + modifiedSize.stamp());
		}
	}

	public void increaseLevel() {

		// TODO does this solve the problem below ?
		if (modifiedSize.stamp() < store.level)
			lastModifiedArcs.clear();

		// TODO the same arc can be marked as modified
		// multiple times on the same level if the consistency
		// function is executed multiple times at that level.
		// (Geost has the same problem)
		// modifiedArcs.addAll(lastModifiedArcs);
		// modifiedSize.update(modifiedArcs.size());
		// lastModifiedArcs.clear();
	}

	public void backtrack() {
		
		// restore deleted arcs
		int size = deletedSize.value();
		for (int i = deletedArcs.size() - 1; i >= size; i--) {
			// System.out.println("Backtrack i=" + i + ", size=" + size +
			// ", ds=" + deletedSize.value() + ", da=" + deletedArcs.size());
			add(deletedArcs.remove(i));
		}

		// restore modified arcs
		size = modifiedSize.value();
		for (int i = modifiedArcs.size() - 1; i >= size; i--) {
			ArcCompanion companion = modifiedArcs.remove(i);
			restore(companion);
		}
		
	}

	// restores an arc that was modified
	private void restore(ArcCompanion companion) {
		
		Arc arc = companion.arc;
		
		if (SHOW_CHANGES) {
			System.err.println("Before restore: " + companion.arc + ", time = "
					+ modifiedSize.stamp());
		}
	
		// TODO, CRUCIAL, BUG, switched off. Is it ok?
		// assert (arc.index >= TREE_ARC);

		companion.restore(this);

		if (SHOW_CHANGES) {
			System.err.println("After restore: " + companion.arc);
		}

		// at upper bound
		if (arc.capacity == 0) {
			if (arc.index >= 0) {
				lower[arc.index] = arc.sister;
			}
		}
		
		// at lower bound
		else if (arc.sister.capacity == 0) {
			if (arc.index >= 0) {
				lower[arc.index] = arc;
			}
		}
		// at neither bound
		else {
			if (arc.index != TREE_ARC) {
				if (arc.reducedCost() <= 0) {
					primalStep(arc);
				} else {
					primalStep(arc.sister);
				}
			}
		}

		// TODO, CRUCIAL, BUG, switched off. Is it ok?
		// assert (arc.index >= TREE_ARC);
		
		assert (checkFlow(this));
		assert (checkStructure(this));
	}

	public void changeCostOffset(long delta) {
		costOffset += delta;
	}

	@Override
	public long cost(long cutoff) {
		return costOffset + super.cost(cutoff - costOffset);
	}

	public int getStoreLevel() {
		return store.level;
	}
	
	public boolean needsUpdate(int maxCost) {
		// Are there any infeasible node balances ?
		Iterator<Node> it = infeasibleNodes.iterator();
		while (it.hasNext()) {
			Node node = it.next();
			if (node.deltaBalance != 0)
				return true;
			it.remove();
		}
		// Is the current flow more expensive than allowed ?
		return (cost(maxCost + 1L) > maxCost);
	}

}
