/**
 *  NetworkFlow.java 
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * 
 * The network flow constraint. Use the NetworkBuilder to create a network and
 * instantiate the network.
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class NetworkFlow extends Constraint {

	private static final int QUEUE_INDEX = 2;
	private static final boolean DO_INSTRUMENTATION = false;
	private static final boolean SHOW_LEVEL = false;

	static {
		// fails if asserts are disabled
		// asserts.Assert.forceAsserts();
	}

	/** Instance counter */
	private static int nextID = 0;

	/** The network */
//	public final Network network;
	public final Pruning network;

	/** The cost variable */
	public IntVar costVariable;

	/** The variables and their handlers */
	public final Map<IntVar, VarHandler> map;

	/** The set of queued variables */
	public final Set<IntVar> queue;

	/** Disables the queue variable function during consistency */
	public boolean disableQueueVariable;

	public int previousLevel = -1;
	
	/********************/
	/** Initialization **/

	private NetworkFlow(List<Node> nodes, 
								  List<Arc> arcs,
								  List<VarHandler> flowVariables, 
								  IntVar costVariable) {
		
		this.network = new Pruning(nodes, arcs);
		this.map = new HashMap<IntVar, VarHandler>();
		this.queue = new HashSet<IntVar>();
		this.costVariable = costVariable;

		for (VarHandler ds : flowVariables) {
			for (IntVar var : ds.listVariables()) {
				VarHandler handler = map.get(var);
				if (handler == null) {
					map.put(var, ds);
				} else if (handler instanceof MultiVarHandler) {
					((MultiVarHandler)handler).add(ds);
				} else {
					map.put(var, new MultiVarHandler(var, handler, ds));
				}
			}
		}

		// fields in superclass
		this.queueIndex = QUEUE_INDEX;
		this.numberId = nextID++;
		this.numberArgs = (short) map.size();
	}

	public NetworkFlow(NetworkBuilder builder) {
		
		this(builder.nodeList, builder.arcList, builder.handlerList, builder.costVariable);
	
	}

	@Override
	public ArrayList<Var> arguments() {
		return new ArrayList<Var>(map.keySet());
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {
		return map.get(var).getPruningEvent(var);
	}

	@Override
	public void impose(Store store) {

		if (costVariable == null) {
			costVariable = new IntVar(store, "Cost", 0, 0);
			System.err.println("WARNING: No cost variable was set, using zero cost.");
		}

		network.initialize(store);
		costVariable.putConstraint(this);
		for (IntVar variable : map.keySet())
			variable.putConstraint(this);

		// register with store
		queueIndex = QUEUE_INDEX;
		store.registerRemoveLevelListener(this);
		store.registerRemoveLevelLateListener(this);
		store.addChanged(this);
		store.countConstraint();
	}

	/***************************/
	/** Search & Backtracking **/

	@Override
	public void queueVariable(int level, Var variable) {
		// DomainStructure structure = map.get(variable);

		if (!disableQueueVariable) {
//			System.out.println("\tQueue var : " + variable);
			if (variable == costVariable) {
				// System.out.println("** Cost var queued, abort");
				return;
			}
			queue.add((IntVar)variable);
		} else {
			// TODO remove
			// System.err.println("Can this actually happen ... " + variable);
		}
	}
	
	private void updateGraph() {
		// update graph
		network.increaseLevel();
		try {
			disableQueueVariable = true;
			for (IntVar variable : queue) {
				VarHandler handler = map.get(variable);
				handler.processEvent(variable, network);
			}
		} finally {
			queue.clear();
			disableQueueVariable = false;
			// network.increaseLevel();
		}
	}

	@Override
	public void consistency(Store store) {
		
		if (SHOW_LEVEL) {
			System.out.println();
			System.out.println("--------- Level " + store.level);
			System.out.println();
		}

		if (DO_INSTRUMENTATION) {Statistics.consistencyCalls++;}
		updateGraph();
		
		boolean first = true; //(previousLevel != store.level);
		//System.out.println(store.level + "   (" + first + ")");
		previousLevel = store.level;
		
		int iteration = 0;
		while (network.needsUpdate(costVariable.max()) || (first && iteration == 0)) {
		
			if (DO_INSTRUMENTATION) {Statistics.consistencyIterations++;}
			//System.out.println(iteration);
			
			iteration++;
			if (SHOW_LEVEL) {
				System.out.println("--------- => Iteration " + iteration);
			}
			
			// recompute flow
			int result = network.networkSimplex(9999999);
			// network.print();

			// is flow infeasible ?
			if (result == -2) {
				throw Store.failException;
			}

			// compute cost and throw failure on overflow
			int cost = (int) network.cost(costVariable.max() + 1);
			if (cost > costVariable.max()) {
				throw Store.failException;
			}
			// prune minimum cost
			if (cost > costVariable.min()) {
				costVariable.domain.inMin(store.level, costVariable, cost);
			}

			// perform domain pruning
			int costLimit = costVariable.max() - costVariable.min();
			
			network.pruneNodesWithSmallDegree();
			network.analyze(costLimit);
			
			assert (checkFlow(network));
			assert (checkStructure(network));
			
			updateGraph();
		}

		
		// compute cost and throw failure on overflow
		int cost = (int) network.cost(costVariable.max() + 1);
		if (cost > costVariable.max()) {
			throw Store.failException;
		}
		// prune minimum cost
		if (cost > costVariable.min()) {
			costVariable.domain.inMin(store.level, costVariable, cost);
		}
	}

	@Override
	public void removeLevel(int level) {
		queue.clear();
	}

	@Override
	public void removeLevelLate(int level) {

		if (SHOW_LEVEL) {
			System.out.println();
			System.out.println("######### Level " + level);
			System.out.println();
		}

		network.backtrack();
	
	}

	@Override
	public boolean satisfied() {
		// TODO Auto-generated method stub
		return false;
	}

	/*************/
	/** Cleanup **/

	@Override
	public void removeConstraint() {

		queue.clear();

		costVariable.removeConstraint(this);
		for (IntVar variable : map.keySet())
			variable.removeConstraint(this);

		// TODO Auto-generated method stub
		throw new AssertionError("Not implemented");
	}

	@Override
	public void increaseWeight() {
		// TODO Auto-generated method stub
		throw new AssertionError("Not implemented");
	}

	/*****************/
	/** Identifiers **/

	@Override
	public String id() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		return null;
	}

}
