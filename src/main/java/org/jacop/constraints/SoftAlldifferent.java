/**
 *  SoftAlldifferent.java 
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

package org.jacop.constraints;

import java.util.ArrayList;

import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.BooleanVar;
import org.jacop.core.BoundDomain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * 
 * This class provides soft-alldifferent constraint by decomposing it 
 * either into a network flow constraint or a set of primitive constraints. 
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class SoftAlldifferent extends DecomposedConstraint {

	public ArrayList<Constraint> decomposition;
	
	public final IntVar[] xVars;
	
	public final IntVar costVar;
	
	public final ViolationMeasure violationMeasure;

	public SoftAlldifferent(IntVar[] xVars, IntVar costVar, ViolationMeasure violationMeasure) {
		this.xVars = xVars;
		this.costVar = costVar;
		this.violationMeasure = violationMeasure;
	}

	public ArrayList<Constraint> primitiveDecomposition(Store store) {

		if (decomposition == null) {

			decomposition = new ArrayList<Constraint>();
			
			if (violationMeasure == ViolationMeasure.DECOMPOSITION_BASED) {

				int n = xVars.length;
				ArrayList<IntVar> costs = new ArrayList<IntVar>(n * (n - 1));
				for (int i = 0; i < n; i++) {
					for (int j = 0; j < i; j++) {
						IntVar v;
						costs.add(v = new BooleanVar(store));
						decomposition.add(new Reified(new XeqY(xVars[i], xVars[j]), v));
					}
				}
				decomposition.add(new Sum(costs, costVar));		

			} else {
				throw new UnsupportedOperationException("Unsupported violation measure " + violationMeasure);
			}

			return decomposition;
		}
		else {

			ArrayList<Constraint> result = new ArrayList<Constraint>();
			
			if (violationMeasure == ViolationMeasure.DECOMPOSITION_BASED) {

				int n = xVars.length;
				ArrayList<IntVar> costs = new ArrayList<IntVar>(n * (n - 1));
				for (int i = 0; i < n; i++) {
					for (int j = 0; j < i; j++) {
						IntVar v;
						costs.add(v = new BooleanVar(store));
						result.add(new Reified(new XeqY(xVars[i], xVars[j]), v));
					}
				}
				result.add(new Sum(costs, costVar));		

			} else {
				throw new UnsupportedOperationException("Unsupported violation measure " + violationMeasure);
			}

			return result;

		}
		
		// Do we have to add the cost-vars to the list of auxilary variables
		// auxilaryVariables.addAll(costs);
	}

	@Override
	public ArrayList<Constraint> decompose(Store store) {

		if (decomposition == null || decomposition.size() > 1) {

			decomposition = new ArrayList<Constraint>();
			
			// compute union of all domains	
			IntDomain all = new IntervalDomain();
			for (IntVar v : xVars)
				all.addDom(v.domain);

			// create values
			int d = all.getSize();
			IntDomain[] doms = new IntDomain[d];
			ValueEnumeration it = all.valueEnumeration();
			for (int i = 0; it.hasMoreElements(); i++) {
				int value = it.nextElement();
				doms[i] = new BoundDomain(value, value);
			}

			// create constraint
			decomposition.add(new SoftAlldiffBuilder(doms, violationMeasure).build());

			//	SoftAlldiffBuilder soft = new SoftAlldiffBuilder(doms, violationMeasure);
			//	soft.decompositionConstraints = new ArrayList<Constraint>();
			//	soft.primitiveDecomposition(store);

		}
		
		return decomposition;
	}

	private class SoftAlldiffBuilder extends NetworkBuilder {

		private SoftAlldiffBuilder(IntDomain[] doms, ViolationMeasure vm) {
			
			super(costVar);

			int n = xVars.length, m = doms.length;
			Node[] d = valueGraph(xVars, doms)[1];
			Node t = addNode("sink", -n);

			if (vm == ViolationMeasure.VARIABLE_BASED) {
				// connect values to sink
				for (int j = 0; j < m; j++) {
					addArc(d[j], t, 0, 1);
					addArc(d[j], t, 1);
				}
			} else if (vm == ViolationMeasure.DECOMPOSITION_BASED) {
				// connect values to sink
				for (int j = 0; j < m; j++)
					for (int cost = 0; cost < n; cost++)
						addArc(d[j], t, cost, 0, 1);
			} else {

				throw new UnsupportedOperationException("Unknown violation measure : " + vm);
			
			}
		}
	}

	@Override
	public void imposeDecomposition(Store store) {
		
		if (decomposition == null)
			decompose(store);
		
		for (Constraint c : decomposition)
			store.impose(c);
		
	}

}
