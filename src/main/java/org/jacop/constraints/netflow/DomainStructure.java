/**
 *  DomainStructure.java 
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
import java.util.List;

import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * A domain based structure variable.
 * 
 * Arcs can be associated to sub-domains of the structure variable. The state of
 * the arc is said to be active if the variable takes a value from its
 * sub-domain and it is inactive otherwise.
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class DomainStructure implements VarHandler {

	public enum Behavior {
		PRUNE_ACTIVE, PRUNE_INACTIVE, PRUNE_BOTH
	}

	public final IntVar variable;
	
	public final Arc[] arcs;
	
	public final IntDomain[] domains;
	
	// public final int[] supports;
	public final Behavior behavior;
	
	public int notGrounded;

	/**
	 * Creates an S-variable
	 * 
	 * @param variable
	 * @param domList
	 * @param arcList
	 */
	public DomainStructure(IntVar variable, List<Domain> domList, List<Arc> arcList) {
		
		this(variable, 
			 domList.toArray(new IntDomain[domList.size()]), 
			 arcList.toArray(new Arc[arcList.size()]));
	
	}

	public DomainStructure(IntVar variable, IntDomain[] domains, Arc[] arcs) {
		
		this(variable, domains, arcs, Behavior.PRUNE_BOTH);

	}

	public DomainStructure(IntVar variable, 
						   IntDomain[] domains, 
						   Arc[] arcs, 
						   Behavior behavior) {
	
		if (domains.length != arcs.length)
			throw new IllegalArgumentException("#domains != #arcs");

		this.variable = variable;
		this.arcs = arcs;
		this.domains = domains;
		// this.supports = new int[arcs.length];
		this.notGrounded = arcs.length;
		this.behavior = behavior;

		for (int id = 0; id < arcs.length; id++) {
			if (!arcs[id].forward)
				throw new IllegalArgumentException("Not a forward arc");

			ArcCompanion companion = arcs[id].companion;
			if (companion == null) {
				arcs[id].companion = companion = new ArcCompanion(arcs[id], 0);
			}
			arcs[id].companion.structure = this;
			arcs[id].companion.arcID = id;
			// supports[id] = domains[id].min();
		}
	}

	// updates the network after the structure variable changed
	public void processEvent(IntVar variable, MutableNetwork network) {
		
		IntDomain vardom = variable.domain;
		int size = vardom.getSize();

		// System.out.println("Event " + variable + " is " + vardom);

		for (int id = notGrounded - 1; id >= 0; id--) {

			// arc already deleted ?
			if (arcs[id].index == DELETED_ARC) {
				// TODO can this happen after we implement arc grounding?
				// if yes, ground arc now
				assert false;
				continue;
			}

			int inter = domains[id].intersect(vardom).getSize();
			// TODO is this a bug ? BoundDomain.emptyDomain.getSize() == -1
			// (The bug is being fixed.. until then we use a workaround)
			if (inter < 0) {
				inter = 0;
			}

			// make arc inactive ?
			if (inter == 0) {
				if (behavior != Behavior.PRUNE_ACTIVE) {
					groundArc(id, false, network);
				}
			}
			// make arc active ?
			else if (inter == size) {
				if (behavior != Behavior.PRUNE_INACTIVE) {
					groundArc(id, true, network);
				}
			}
		}
	}

	private void groundArc(int arcID, boolean active, MutableNetwork network) {
		
		assert (arcID < notGrounded);

		// prune domain of x variable

		Arc arc = arcs[arcID];
		ArcCompanion companion = arc.companion;
		IntVar xVar = companion.xVar;

		// active arc - ground flow at upper bound
		if (active) {
			
			int maxFlow = companion.flowOffset + arc.capacity
					+ arc.sister.capacity;

			if (xVar != null) {
				int level = network.getStoreLevel();
				xVar.domain.in(level, xVar, maxFlow, maxFlow);
			}
		
			// TODO else here ? if queueVar performs update

			companion.setFlow(maxFlow);
		
			if (arc.index >= 0) {
				// TODO this isn't nice
				((Network) network).lower[arc.index] = arc.sister;
			}

		}
		// inactive arc - ground flow at lower bound
		else {
			int minFlow = companion.flowOffset;

			if (xVar != null) {
				int level = network.getStoreLevel();
				xVar.domain.in(level, xVar, minFlow, minFlow);
			}
			// TODO else here ? if queueVar performs update

			companion.setFlow(minFlow);
			if (arc.index >= 0) {
				// TODO this isn't nice either
				((Network) network).lower[arc.index] = arc;
			}
		}

		// remove arc from graph
		network.remove(arcs[arcID]);

		// remove domain/arc pair
		swap(arcID, --notGrounded);
	}

	private void swap(int i, int j) {
		if (i == j)
			return;

		IntDomain temp1 = domains[i];
		domains[i] = domains[j];
		domains[j] = temp1;

		Arc temp2 = arcs[i];
		arcs[i] = arcs[j];
		arcs[j] = temp2;

		arcs[j].companion.arcID = j;
		arcs[i].companion.arcID = i;
	}

	public void ungroundArc(int arcID) {
		assert (arcID >= notGrounded);

		// add domain/arc pair
		// swap(arcID, notGrounded++);
		assert (arcID == notGrounded);
		notGrounded++;
	}

	
	public List<IntVar> listVariables() {
		return Arrays.asList(variable);
	}

	public boolean isGrounded(int arcID) {
		return (arcID >= notGrounded);
	}

	
	public int getPruningEvent(Var var) {
		return IntDomain.ANY; // for S-variables
	}
}
