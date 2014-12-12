/**
 *  ArcCompanion.java 
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

import static org.jacop.constraints.netflow.simplex.NetworkSimplex.DELETED_ARC;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.jacop.constraints.netflow.DomainStructure.Behavior;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * 
 * This class extends the definition of an arc by a lower bound on the capacity
 * and connects the arc to variables that constrain it.
 * 
 * The ArcCompanion plays the role of the VarHandler for X- and W-variables. It
 * also provides a hook for S-variables of any
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public final class ArcCompanion implements VarHandler, Comparable<ArcCompanion> {

	/** The (forward) arc */
	public final Arc arc;

	/** Current lower capacity of the arc */
	public int flowOffset;

	/** The FDV for lower and upper capacity */
	public IntVar xVar;
	
	/** The FDV for lower and upper cost */
	public IntVar wVar;

	/** The associated structure variable */
	public DomainStructure structure;
	
	/** Identifier for this arc in the structure variable */
	public int arcID;

	/** The pruningScore */
	public int pruningScore;
	
	public ArcCompanion(Arc arc, int offset) {
		this.arc = arc;
		this.flowOffset = offset;
	}
	
	public String toString() {
		String str = "[offset = " + flowOffset;
		if (xVar != null) str += ", xVar = " + xVar.id;
		if (wVar != null) str += ", wVar = " + wVar.id;
		if (structure != null) str += ", sVar = " + structure.variable.id;
		return str + "]";
	}
	
	/**
	 * Changes the lower and upper capacity of the arc in any way, performing
	 * the necessary changes to node balance and flow offset functions.
	 * 
	 * @param min
	 *            the new lower capacity
	 * @param max
	 *            the new upper capacity
	 */
	public void changeCapacity(int min, int max) {
		
		assert (min <= max) : "min value must be smaller or equal the maximum value";

		// the order only matters if intervals (before & after) are
		// non-overlapping
		// (this should never happen during a search or backtracking...)
		// (But let's be defensive about it)
		if (min < flowOffset) {
			changeMinCapacity(min);
			changeMaxCapacity(max);
		} else {
			changeMaxCapacity(max);
			changeMinCapacity(min);
		}

	}

	public void changeMinCapacity(int min) {
		
		assert (min >= 0);
		assert (min <= (flowOffset + arc.capacity + arc.sister.capacity));

		int delta = min - flowOffset;
		if (delta != 0) {
			// change bounds
			flowOffset = min;
			arc.sister.capacity -= delta;
			arc.tail().balance -= delta;
			arc.head.balance += delta;

			// repair flow if lower bound raises above current flow
			if (arc.sister.capacity < 0) {
				setFlow(min);
				assert (arc.sister.capacity == 0);
			}
		}
	}

	public void changeMaxCapacity(int max) {
		
		assert (max >= flowOffset);

		int residual = arc.capacity;
		int total = flowOffset + residual + arc.sister.capacity;

		int delta = total - max;
		if (delta != 0) {
			// change residual capacity
			arc.capacity -= delta;

			// repair flow if upper bound falls below current flow
			if (arc.capacity < 0) {
				setFlow(max);
				assert (arc.capacity == 0);
			}
		}
	}

	public List<IntVar> listVariables() {
		
		// It is called only in constructors, no need to make it extra efficient.
		
		if (xVar != null) {
			if (wVar != null) {
				return Arrays.asList(xVar, wVar);
			} else {
				return Arrays.asList(xVar);
			}
		} else if (wVar != null) {
			return Arrays.asList(wVar);
		} else {
			return Collections.emptyList();
		}
		
	}

	public void processEvent(IntVar variable, MutableNetwork network) {
		
		// arc already deleted ?
		// (This can happen if the arc is attached to an S-variable)
//		if (arc.index == DELETED_ARC)
//			return;

		// Capacity variable was bounded
		if (variable == xVar && arc.index != DELETED_ARC) {
			// Interaction with structure variable
			// Note: this may throw a failException
			
			boolean updated = false;
		
			if (structure != null && !structure.isGrounded(arcID)) {
				updated = updateSVar(network.getStoreLevel());
			}

			// since we listen only to bound events, capacity changes for sure
			changeCapacity(xVar.min(), xVar.max());
			network.modified(this);
			if (xVar.singleton()) {
				network.remove(arc);
			}
			
			// process changes on s-variable
			// TODO already done by queue variable ?
			if (updated) {
				structure.processEvent(structure.variable, network);
			}
			
		}
		// Weight variable was bounded
		else if (variable == wVar) {
			// get new cost
			// int newCost = network.isMinimizng() ? wVar.min() : -wVar.max();
			int newCost = wVar.min();

			// increase cost to new bound
			if (arc.cost != newCost) {

				// deleted arc, maintain costOffset
				if (arc.index == DELETED_ARC) {
					int deltaCost = newCost - arc.cost;
					int flow = flowOffset + arc.sister.capacity;
					network.changeCostOffset((long) flow * (long) deltaCost);
//					System.out.println(arc.name() + " : " + ((long) flow * (long) deltaCost));
//					throw new RuntimeException();
				} /*else if (flowOffset != 0) {
					int deltaCost = newCost - arc.cost;
					int flow = flowOffset;
					network.changeCostOffset((long) flow * (long) deltaCost);
				}*/

				arc.cost = newCost;
				arc.sister.cost = -newCost;
				network.modified(this);
			}
		}
	}

	/**
	 * Restores the capacity and weight of the arc after backtracking.
	 * 
	 * @param network
	 *            the network
	 */
	public void restore(MutableNetwork network) {

		if (wVar != null) {
			
			int newCost = wVar.min();

			// deleted arc, maintain costOffset
			if (arc.index == DELETED_ARC) {
				int deltaCost = newCost - arc.cost;
				int flow = flowOffset + arc.sister.capacity;
				network.changeCostOffset((long) flow * (long) deltaCost);
//				System.out.println(arc.name() + " : " + ((long) flow * (long) deltaCost));
//				throw new RuntimeException();
			} /*else if (flowOffset != 0) {
				int deltaCost = newCost - arc.cost;
				int flow = flowOffset;
				network.changeCostOffset((long) flow * (long) deltaCost);
			}*/
			arc.cost = newCost;
			arc.sister.cost = -newCost;
		}
		
		if (xVar != null) {
			changeCapacity(xVar.min(), xVar.max());
//			assert (!xVar.singleton()) : " " + xVar + ", " + xVar.domain;
		}
		
	}

	/**
	 * Forces the flow to a given value (within capacity bounds).
	 * 
	 * @param flow
	 *            the new flow value
	 */
	public void setFlow(int flow) {
		
		int currentFlow = flowOffset + arc.sister.capacity;
		assert (flowOffset <= flow);
		assert (flow <= currentFlow + arc.capacity);

		int delta = flow - currentFlow;
		
		if (delta != 0) {
			arc.capacity -= delta;
			arc.sister.capacity += delta;

			arc.tail().deltaBalance -= delta;
			arc.head.deltaBalance += delta;

			arc.tail().balance += delta;
			arc.head.balance -= delta;
		}
	}

	
	public int getPruningEvent(Var var) {
		return IntDomain.BOUND; // for X- and W-variables
	}

	/**
	 * interaction with structure variable
	 * @param level current store level
	 * @return whether the domain of the s-variable has been updated
	 */
	private boolean updateSVar(int level) {
		// lower and upper capacity bounds
		// they are assumed to be unchanged since the begin of the search
		int lower = flowOffset;
		int upper = lower + arc.capacity + arc.sister.capacity;
		boolean updated = false;
		
		// case: x > l
		if (xVar.min() > lower) {
			// apply ACTIVE rule to x variable
			// (d_i inter S = S) => (x = u)
			if (structure.behavior == Behavior.PRUNE_BOTH) {
				xVar.domain.in(level, xVar, upper, upper);
			}

			// apply INACTIVE rule to s variable
			// (x > l) => (d_i inter S = S)
			if (structure.behavior != Behavior.PRUNE_ACTIVE) {
				IntVar sVar = structure.variable;
				Domain arcDomain = structure.domains[arcID];
				sVar.domain.in(level, sVar, arcDomain);
				updated = true;
			}
		}
		// case: x < u
		if (xVar.max() < upper) {
			// apply INACTIVE rule on x variable
			// (d_i inter S = empty) => (x = l)
			if (structure.behavior == Behavior.PRUNE_BOTH) {
				xVar.domain.in(level, xVar, lower, lower);
			}

			// apply ACTIVE rule on s variable
			// (x < u) => (d_i inter S = empty)
			if (structure.behavior != Behavior.PRUNE_INACTIVE) {
				IntVar sVar = structure.variable;
				Domain arcDomainC = structure.domains[arcID].complement();
				sVar.domain.in(level, sVar, arcDomainC);
				updated = true;
			}
		}
		return updated;
	}


	public int compareTo(ArcCompanion that) {
		if (this.arc.index == DELETED_ARC)  {
			if (that.arc.index != DELETED_ARC)
				return 1;
		} else {
			if (that.arc.index == DELETED_ARC)
				return -1;
		}
		return that.pruningScore - this.pruningScore;
	}

	
}
