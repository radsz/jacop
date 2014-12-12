/**
 *  NetworkBuilder.java 
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

import org.jacop.constraints.Constraint;
import org.jacop.constraints.Eq;
import org.jacop.constraints.In;
import org.jacop.constraints.Not;
import org.jacop.constraints.Sum;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.netflow.DomainStructure.Behavior;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * A builder class for the network flow constraints. Models should use or
 * inherit from this class to build a network.
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */


public class NetworkBuilder {

	private int nextNodeName = 1;

	public IntVar costVariable;
	
	public final List<Node> nodeList = new ArrayList<Node>();
	
	public final List<Arc> arcList = new ArrayList<Arc>();
	
	public final List<VarHandler> handlerList = new ArrayList<VarHandler>();

	public NetworkBuilder() {
		this.costVariable = null;
	}

	public NetworkBuilder(IntVar costVariable) {
		this.costVariable = costVariable;
	}

	/* cost variable */

	public void setCostVariable(IntVar costVariable) {
		this.costVariable = costVariable;
	}

	/* add node */

	public Node addNode() {
		return addNode(0);
	}

	public Node addNode(int balance) {
		String name = "(" + nextNodeName++ + ")";
		return addNode(name, balance);
	}

	public Node addNode(String name) {
		return addNode(name, 0);
	}

	public Node addNode(String name, int balance) {
		Node node = new Node(name, balance);
		nodeList.add(node);
		return node;
	}

	/* add arc */

	public Arc addArc(Node from, Node to, IntVar wVar, IntVar xVar) {

		Arc arc = addArc(from, to, wVar, xVar.min(), xVar.max());

		arc.companion.xVar = xVar;

		return arc;

	}

	public Arc addArc(Node from, Node to, int weight, IntVar xVar) {

		Arc arc = addArc(from, to, weight, xVar.min(), xVar.max());

		if (arc.companion == null)
			arc.companion = new ArcCompanion(arc, 0);
		
		arc.companion.xVar = xVar;
		handlerList.add(arc.companion);

		return arc;

	}

	public Arc addArc(Node from, Node to, IntVar wVar, int lowerCapacity, int upperCapacity) {

		int weight = wVar.min();
		Arc arc = addArc(from, to, weight, lowerCapacity, upperCapacity);

		if (arc.companion == null)
			arc.companion = new ArcCompanion(arc, 0);
		
		arc.companion.wVar = wVar;
		handlerList.add(arc.companion);

		return arc;
	}

	public Arc addArc(Node from, Node to, int weight, int lowerCapacity,
			int upperCapacity) {
		Arc arc = new Arc(from, to, weight, lowerCapacity, upperCapacity);
		arcList.add(arc);
		return arc;
	}

	public Arc addArc(Node from, Node to, int weight, int capacity) {
		return addArc(from, to, weight, 0, capacity);
	}

	public Arc addArc(Node from, Node to, int weight) {
		return addArc(from, to, weight, Integer.MAX_VALUE);
	}

	public Arc addArc(Node from, Node to) {
		return addArc(from, to, 0);
	}

	/* value graph */

	/**
	 * Returns two arrays containing the nodes for each variable and the nodes
	 * for each domain, respectively.
	 */
	public Node[][] valueGraph(IntVar[] vars, IntDomain[] domains) {
		
		int n = vars.length, m = domains.length;

		Node[] v = new Node[n], d = new Node[m];

		for (int i = 0; i < n; i++)
			v[i] = addNode(vars[i].id, 1);
		
		for (int i = 0; i < m; i++)
			d[i] = addNode(domains[i].toString(), 0);

		for (int i = 0; i < n; i++) {
		
			IntVar var = vars[i];

			List<Arc> arcs = new ArrayList<Arc>();
			List<Domain> doms = new ArrayList<Domain>();

			IntDomain vardom = var.domain;
			for (int j = 0; j < m; j++) {
				if (vardom.isIntersecting(domains[j])) {
					arcs.add(addArc(v[i], d[j], 0, 1));
					doms.add(domains[j]);
				}
			}
			handlerList.add(new DomainStructure(var, doms, arcs));
		}
		return new Node[][] { v, d };
	}

	/* list variables */

	// list of all variables, excluding the cost variable
	public ArrayList<IntVar> listVariables() {

		ArrayList<IntVar> list = new ArrayList<IntVar>();
	
		for (VarHandler handler : handlerList)
			list.addAll(handler.listVariables());

		return list;
	
	}

	/* build network */

	public NetworkFlow build() {
		return new NetworkFlow(this);
	}
	
	/**
	 * Generally speaking, especially in case of multiple arcs between 
	 * two nodes and structure constraints imposed on arcs makes it hard
	 * to decompose network flow constraint into primitive ones. Since, the
	 * decomposition introduces new variables and removal of artificial
	 * solutions is not practically achievable in all cases it is possible
	 * that decomposition will have more solutions due to the fact that
	 * decomposition may use more expensive arcs to transfer the flow.
	 * @param store
	 */
	public ArrayList<Constraint> primitiveDecomposition(Store store) {
		
		ArrayList<Constraint> result = new ArrayList<Constraint>();
		
		//@TODO, fix it? Check the remark above.
		for (Node node : nodeList) {
			ArrayList<IntVar> in = new ArrayList<IntVar>();
			ArrayList<IntVar> out = new ArrayList<IntVar>();
			
			for (Arc arc : arcList) {
			
				// This code replaces, the one below to handle 
				if (arc.head == node || arc.tail() == node) {
					
					if (arc.getCompanion() == null)
					// the above condition is satisfied sometimes.
						arc.companion = new ArcCompanion(arc, 0);

					IntVar var = arc.getCompanion().xVar;
					if (var == null)
						var = new IntVar(store, arc.getCompanion().flowOffset, arc.getCompanion().flowOffset + arc.capacity + arc.sister.capacity);
					if (arc.head == node)
						in.add(var);
					if (arc.tail() == node)
						out.add(var);
					arc.getCompanion().xVar = var;
				}
			//	if (arc.head == node) in.add(arc.getCompanion().xVar);
			//	if (arc.tail() == node) out.add(arc.getCompanion().xVar);
			}
			
			if (node.balance != 0) {
				IntVar balance = new IntVar(store, node.balance, node.balance);
				in.add(balance);
			}
			
			// added.
			if (in.size() == 0 || out.size() == 0)
				continue;
			
			if (in.size() == 1) {
				sumC(result, store, out, in.iterator().next());
			} else if (out.size() == 1) {
				sumC(result, store, in, out.iterator().next());
			} else {
				IntVar sum = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
				sumC(result, store, in, sum);
				sumC(result, store, out, sum);
			}
		}

		for (VarHandler handler : handlerList) {
			
			if (handler instanceof DomainStructure) {
				DomainStructure structure = (DomainStructure)handler;
				
				for (int i = 0; i < structure.arcs.length; i++) {
				
					Arc arc = structure.arcs[i];
					IntDomain dom = structure.domains[i];
					
					if (structure.behavior != Behavior.PRUNE_ACTIVE) {
						result.add(new Eq(new Not(new In(structure.variable, dom)), 
											new XeqC(arc.getCompanion().xVar, 
													 arc.getCompanion().flowOffset)));
					}

					if (structure.behavior != Behavior.PRUNE_INACTIVE) {
						int maxFlow = arc.getCompanion().flowOffset + arc.capacity + arc.sister.capacity;
						result.add(new Eq(new In(structure.variable, dom), new XeqC(arc.getCompanion().xVar, maxFlow)));
					
					}
				
				}

			}
		}
		
		ArrayList<IntVar> vars = new ArrayList<IntVar>();
		ArrayList<Integer> weights = new ArrayList<Integer>();
		
		boolean simpleSum = true;
		for (Arc arc : arcList) {
			if (arc.getCompanion().wVar != null) {
				IntVar var = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
				result.add(new XmulYeqZ(arc.getCompanion().xVar, arc.getCompanion().wVar, var));
				vars.add(var);
				weights.add(1);
			} else if (arc.cost == 1) {
				vars.add(arc.getCompanion().xVar);
				weights.add(1);
			} else if (arc.cost != 0) {
				
				simpleSum = false;
				vars.add(arc.getCompanion().xVar);
				weights.add(arc.cost);
				
			}
		}
		
		// @TODO, SumWeight could be used instead of Sum and auxiliary variables weight above.
		if (simpleSum)
			sumC(result, store, vars, costVariable);
		else
			result.add(new SumWeight(vars, weights, costVariable));
		
		return result;
		
	}
	
	private void sumC(ArrayList<Constraint> list, Store store, ArrayList<IntVar> vars, IntVar result) {
		
		if (result == null) 
			throw new AssertionError();
		
		if (vars.size() == 0) {
			list.add(new XeqY(result, new IntVar(store, 0, 0)));
		} else if (vars.size() == 1) {
			list.add(new XeqY(result, vars.iterator().next()));
		} else {
			list.add(new Sum(vars, result));
		}
	
	}

}
