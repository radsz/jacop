/**
 *  SoftGCC.java 
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
import java.util.List;

import org.jacop.constraints.netflow.DomainStructure;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.BoundDomain;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * 
 * This class provides soft-gcc constraint by decomposing it 
 * either into a network flow constraint or a set of primitive constraints. 
 *
 * It is soft in a sense that every violation of softLower, softUpper bound or softCounter contributes
 * to the violation cost. It is hard in a sense that it does enforce hardLower, hardUpper bound or
 * hardCounter. It uses value based violation metric.
 *
 * @author Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class SoftGCC extends DecomposedConstraint {

	public ArrayList<Constraint> decomposition;
	
	public IntVar[] xVars;
	
	public IntVar[] hardCounters;
	public IntVar[] softCounters;
	
	public int[] countedValue;
	
	public int[] softLowerBound;	
	public int[] softUpperBound;

	public int[] hardLowerBound;	
	public int[] hardUpperBound;

	public IntVar costVar;
	
	public ViolationMeasure violationMeasure;

	/**
	 * It specifies soft-GCC constraint. 
	 * 
	 * @param xVars variables over which counting takes place.
	 * @param hardCounters counter variables for different values being counted. Their domain specify hard constraints on the occurrences.
	 * @param countedValue it specifies values which occurrence is being counted.
	 * @param softLowerBound it specifies constraint what is the minimal number of occurrences.
	 * @param softUpperBound it specifies constraint what is the maximal number of occurrences.
	 * @param costVar a cost variable specifying the cost of violations.
	 * @param violationMeasure it is only accepted to use Value_Based violation measure.
	 */
	public SoftGCC(IntVar[] xVars, 
			IntVar[] hardCounters, 
			int[] countedValue,
			int[] softLowerBound,
			int[] softUpperBound,
			IntVar costVar, 
			ViolationMeasure violationMeasure) {

		this.xVars = new IntVar[xVars.length];
		System.arraycopy(xVars, 0, this.xVars, 0, xVars.length);

		this.hardCounters = new IntVar[hardCounters.length];
		System.arraycopy(hardCounters, 0, this.hardCounters, 0, hardCounters.length);

		this.softLowerBound = new int[softLowerBound.length];
		System.arraycopy(softLowerBound, 0, this.softLowerBound, 0, softLowerBound.length);

		this.softUpperBound = new int[softUpperBound.length];
		System.arraycopy(softUpperBound, 0, this.softUpperBound, 0, softUpperBound.length);

		this.countedValue = new int[countedValue.length];
		System.arraycopy(countedValue, 0, this.countedValue, 0, countedValue.length);

		this.costVar = costVar;
		this.violationMeasure = violationMeasure;

	}	
	
	/**
	 * It specifies soft-GCC constraint. 
	 * 
	 * @param xVars variables over which counting takes place.
	 * @param hardLowerBound it specifies constraint what is the minimal number of occurrences. (hard)
	 * @param hardUpperBound it specifies constraint what is the maximal number of occurrences. (hard)
	 * @param countedValue it specifies values which occurrence is being counted.
	 * @param softCounters it specifies the number of occurrences (soft). 
	 * @param costVar a cost variable specifying the cost of violations.
	 * @param violationMeasure it is only accepted to use Value_Based violation measure.
	 */
	public SoftGCC(IntVar[] xVars, 
			int[] hardLowerBound,
			int[] hardUpperBound,
			int[] countedValue,
			IntVar[] softCounters, 
			IntVar costVar, 
			ViolationMeasure violationMeasure) {

		this.xVars = new IntVar[xVars.length];
		System.arraycopy(xVars, 0, this.xVars, 0, xVars.length);

		this.softCounters = new IntVar[softCounters.length];
		System.arraycopy(softCounters, 0, this.softCounters, 0, softCounters.length);

		this.hardLowerBound = new int[hardLowerBound.length];
		System.arraycopy(hardLowerBound, 0, this.hardLowerBound, 0, hardLowerBound.length);

		this.hardUpperBound = new int[hardUpperBound.length];
		System.arraycopy(hardUpperBound, 0, this.hardUpperBound, 0, hardUpperBound.length);

		this.countedValue = new int[countedValue.length];
		System.arraycopy(countedValue, 0, this.countedValue, 0, countedValue.length);

		this.costVar = costVar;
		this.violationMeasure = violationMeasure;

	}	

	
	/**
	 * It specifies soft-GCC constraint. 
	 * 
	 * @param xVars variables over which counting takes place.
	 * @param hardCounters counter variables for different values being counted. (hard)
	 * @param countedValue it specifies values which occurrence is being counted.
	 * @param softCounters counter variables for different values being counted. (soft)
	 * @param costVar a cost variable specifying the cost of violations.
	 * @param violationMeasure it is only accepted to use Value_Based violation measure.
	 */
	public SoftGCC(IntVar[] xVars, 
			IntVar[] hardCounters,
			int[] countedValue,
			IntVar[] softCounters, 
			IntVar costVar, 
			ViolationMeasure violationMeasure) {

		this.xVars = new IntVar[xVars.length];
		System.arraycopy(xVars, 0, this.xVars, 0, xVars.length);

		this.softCounters = new IntVar[softCounters.length];
		System.arraycopy(softCounters, 0, this.softCounters, 0, softCounters.length);

		this.hardCounters = new IntVar[hardCounters.length];
		System.arraycopy(hardCounters, 0, this.hardCounters, 0, hardCounters.length);

		this.countedValue = new int[countedValue.length];
		System.arraycopy(countedValue, 0, this.countedValue, 0, countedValue.length);

		this.costVar = costVar;
		this.violationMeasure = violationMeasure;

	}	
	
	
	/**
	 * It specifies soft-GCC constraint. 
	 * 
	 * @param xVars variables over which counting takes place.
	 * @param hardCounters counter variables for different values being counted. (hard)
	 * @param softLowerBound it specifies constraint what is the minimal number of occurrences. (soft)
	 * @param softUpperBound it specifies constraint what is the maximal number of occurrences. (soft)
	 * @param costVar a cost variable specifying the cost of violations.
	 * @param violationMeasure it is only accepted to use Value_Based violation measure.
	 */	
	public SoftGCC(IntVar[] xVars, 
				   IntVar[] hardCounters, 
				   int[] softLowerBound,
				   int[] softUpperBound,
				   IntVar costVar, 
				   ViolationMeasure violationMeasure) {

		IntDomain sum = new IntervalDomain();
		for (int i = 0; i < xVars.length; i++)
			sum.unionAdapt(xVars[i].domain);
		
		countedValue = new int[sum.getSize()];
		int i = 0;
		for (ValueEnumeration enumer = sum.valueEnumeration(); enumer.hasMoreElements();) {
			countedValue[i++] = enumer.nextElement();
		}
		
		this.xVars = new IntVar[xVars.length];
		System.arraycopy(xVars, 0, this.xVars, 0, xVars.length);
		
		this.hardCounters = new IntVar[hardCounters.length];
		System.arraycopy(hardCounters, 0, this.hardCounters, 0, hardCounters.length);
		
		this.softLowerBound = new int[softLowerBound.length];
		System.arraycopy(softLowerBound, 0, this.softLowerBound, 0, softLowerBound.length);

		this.softUpperBound = new int[softUpperBound.length];
		System.arraycopy(softUpperBound, 0, this.softUpperBound, 0, softUpperBound.length);

		
		this.costVar = costVar;
		this.violationMeasure = violationMeasure;
	
	}
	
	
	
	/**
	 * It specifies soft-GCC constraint. 
	 * 
	 * @param xVars variables over which counting takes place.
	 * @param hardLowerBound it specifies constraint what is the minimal number of occurrences. (hard)
	 * @param hardUpperBound it specifies constraint what is the maximal number of occurrences. (hard)
	 * @param softCounters counter variables for different values being counted. (soft)
	 * @param costVar a cost variable specifying the cost of violations.
	 * @param violationMeasure it is only accepted to use Value_Based violation measure.
	 */
	public SoftGCC(IntVar[] xVars, 
			int[] hardLowerBound,
			int[] hardUpperBound,
			IntVar[] softCounters, 
			IntVar costVar, 
			ViolationMeasure violationMeasure) {

		IntDomain sum = new IntervalDomain();
		for (int i = 0; i < xVars.length; i++)
			sum.unionAdapt(xVars[i].domain);
		
		countedValue = new int[sum.getSize()];
		int i = 0;
		for (ValueEnumeration enumer = sum.valueEnumeration(); enumer.hasMoreElements();) {
			countedValue[i++] = enumer.nextElement();
		}

		this.xVars = new IntVar[xVars.length];
		System.arraycopy(xVars, 0, this.xVars, 0, xVars.length);

		this.softCounters = new IntVar[softCounters.length];
		System.arraycopy(softCounters, 0, this.softCounters, 0, softCounters.length);

		this.hardLowerBound = new int[hardLowerBound.length];
		System.arraycopy(hardLowerBound, 0, this.hardLowerBound, 0, hardLowerBound.length);

		this.hardUpperBound = new int[hardUpperBound.length];
		System.arraycopy(hardUpperBound, 0, this.hardUpperBound, 0, hardUpperBound.length);

		this.costVar = costVar;
		this.violationMeasure = violationMeasure;

	}	

	
	/**
	 * It specifies soft-GCC constraint. 
	 * 
	 * @param xVars variables over which counting takes place.
	 * @param hardCounters counter variables for different values being counted. (hard)
	 * @param softCounters counter variables that may be violated.
	 * @param costVar a cost variable specifying the cost of violations.
	 * @param violationMeasure it is only accepted to use Value_Based violation measure.
	 */
	public SoftGCC(IntVar[] xVars, 
			IntVar[] hardCounters,
			IntVar[] softCounters, 
			IntVar costVar, 
			ViolationMeasure violationMeasure) {

		IntDomain sum = new IntervalDomain();
		for (int i = 0; i < xVars.length; i++)
			sum.unionAdapt(xVars[i].domain);
		
		countedValue = new int[sum.getSize()];
		int i = 0;
		for (ValueEnumeration enumer = sum.valueEnumeration(); enumer.hasMoreElements();) {
			countedValue[i++] = enumer.nextElement();
		}

		this.xVars = new IntVar[xVars.length];
		System.arraycopy(xVars, 0, this.xVars, 0, xVars.length);

		this.softCounters = new IntVar[softCounters.length];
		System.arraycopy(softCounters, 0, this.softCounters, 0, softCounters.length);

		this.hardCounters = new IntVar[hardCounters.length];
		System.arraycopy(hardCounters, 0, this.hardCounters, 0, hardCounters.length);

		this.costVar = costVar;
		this.violationMeasure = violationMeasure;

	}	
	
	
	public ArrayList<Constraint> primitiveDecomposition(Store store) {

		if (decomposition == null) {

			decomposition = new ArrayList<Constraint>();
			
			if (violationMeasure == ViolationMeasure.VALUE_BASED) {

				ArrayList<IntVar> costs = new ArrayList<IntVar>(countedValue.length);

				for (int i = 0; i < countedValue.length; i++) {
					
					if (hardCounters != null && softLowerBound != null) {
						
						decomposition.add( new Count(xVars, hardCounters[i], countedValue[i]) );

						assert (softLowerBound[i] >= 0 && softLowerBound[i] <= xVars.length) : "LowerBound for " + i + "-th element must be between 0 and number of variables";
						assert (softUpperBound[i] >= 0 && softUpperBound[i] <= xVars.length) : "UpperBound for " + i + "-th element must be between 0 and number of variables";

						int [][] table = new int[xVars.length+1][2];
						for (int j = 0; j <= xVars.length; j++) {
							table[j][0] = j;
							table[j][1] = 0;
							if (j < softLowerBound[i])
								table[j][1] = softLowerBound[i] - j;
							if (j > softUpperBound[i])
								table[j][1] = j - softUpperBound[i];
						}

						IntVar v = new IntVar(store, 0, xVars.length);
						costs.add(v);

						IntVar[] list = {hardCounters[i], v};
						decomposition.add( new ExtensionalSupportVA(list, table));
						
						continue;
					}
					
					if (softCounters != null) {
						
						IntVar hardCounter;
						
						if (hardLowerBound != null )
							hardCounter = new IntVar(store, hardLowerBound[i], hardUpperBound[i]);
						else
							hardCounter = hardCounters[i];
						
						decomposition.add( new Count(xVars, hardCounter, countedValue[i]) );

						ArrayList<int[]> tuples = new ArrayList<int[]>();
						
						for (ValueEnumeration hard = hardCounter.domain.valueEnumeration();
						 	 hard.hasMoreElements();) {

							int hardElement = hard.nextElement();
							
							for (ValueEnumeration soft = softCounters[i].domain.valueEnumeration();
						 	 soft.hasMoreElements();) {
								
								int softElement = soft.nextElement();
								int cost;
								
								if (hardElement > softElement)
									cost = hardElement - softElement;
								else
									cost = softElement - hardElement;
								
								int[] tuple = {hardElement, softElement, cost};
								tuples.add(tuple);
								
							}

							
						}
							
						IntVar v = new IntVar(store, 0, xVars.length);
						costs.add(v);

						IntVar[] list = {hardCounter, softCounters[i], v};
						decomposition.add( new ExtensionalSupportVA(list, tuples.toArray(new int[tuples.size()][3])));
						
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

			if (violationMeasure == ViolationMeasure.VALUE_BASED) {

				ArrayList<IntVar> costs = new ArrayList<IntVar>(countedValue.length);

				for (int i = 0; i < countedValue.length; i++) {
					
					if (hardCounters != null && softLowerBound != null) {
						
						result.add( new Count(xVars, hardCounters[i], countedValue[i]) );

						assert (softLowerBound[i] >= 0 && softLowerBound[i] <= xVars.length) : "LowerBound for " + i + "-th element must be between 0 and number of variables";
						assert (softUpperBound[i] >= 0 && softUpperBound[i] <= xVars.length) : "UpperBound for " + i + "-th element must be between 0 and number of variables";

						int [][] table = new int[xVars.length+1][2];
						for (int j = 0; j <= xVars.length; j++) {
							table[j][0] = j;
							table[j][1] = 0;
							if (j < softLowerBound[i])
								table[j][1] = softLowerBound[i] - j;
							if (j > softUpperBound[i])
								table[j][1] = j - softUpperBound[i];
						}

						IntVar v = new IntVar(store, 0, xVars.length);
						costs.add(v);

						IntVar[] list = {hardCounters[i], v};
						result.add( new ExtensionalSupportVA(list, table));
						
						continue;
					}
					
					if (softCounters != null) {
						
						IntVar hardCounter;
						
						if (hardLowerBound != null )
							hardCounter = new IntVar(store, hardLowerBound[i], hardUpperBound[i]);
						else
							hardCounter = hardCounters[i];
						
						result.add( new Count(xVars, hardCounter, countedValue[i]) );

						ArrayList<int[]> tuples = new ArrayList<int[]>();
						
						for (ValueEnumeration hard = hardCounter.domain.valueEnumeration();
						 	 hard.hasMoreElements();) {

							int hardElement = hard.nextElement();
							
							for (ValueEnumeration soft = softCounters[i].domain.valueEnumeration();
						 	 soft.hasMoreElements();) {
								
								int softElement = soft.nextElement();
								int cost;
								
								if (hardElement > softElement)
									cost = hardElement - softElement;
								else
									cost = softElement - hardElement;
								
								int[] tuple = {hardElement, softElement, cost};
								tuples.add(tuple);
								
							}

							
						}
							
						IntVar v = new IntVar(store, 0, xVars.length);
						costs.add(v);

						IntVar[] list = {hardCounter, softCounters[i], v};
						result.add( new ExtensionalSupportVA(list, tuples.toArray(new int[tuples.size()][3])));
						
					}
					
				}
				
				result.add(new Sum(costs, costVar));		

			} else {
				throw new UnsupportedOperationException("Unsupported violation measure " + violationMeasure);
			}

			return result;

		}
		
	}

	@Override
	public ArrayList<Constraint> decompose(Store store) {

		if (decomposition == null || decomposition.size() > 1) {

			decomposition = new ArrayList<Constraint>();
			
			// compute union of all domains	
			IntDomain all = new IntervalDomain();
			for (int value : countedValue)
				all.unionAdapt(value);

			// create values
			int d = all.getSize();
			IntDomain[] doms = new IntDomain[d];
			ValueEnumeration it = all.valueEnumeration();
			for (int i = 0; it.hasMoreElements(); i++) {
				int value = it.nextElement();
				doms[i] = new BoundDomain(value, value);
			}

			// create constraint
			decomposition.add(new SoftGCCBuilder(all, doms, violationMeasure).build());

		}
		
		return decomposition;
	}

	private class SoftGCCBuilder extends NetworkBuilder {

		private SoftGCCBuilder(IntDomain all, IntDomain[] doms, ViolationMeasure vm) {
			
			super(costVar);

			if (vm == ViolationMeasure.VALUE_BASED) {

			int n = xVars.length, m = doms.length;
			
			Node[] xNodes = new Node[n];
			Node[] valueNodes = new Node[m];
			Node[] countNodes = new Node[m];
			
			for (int i = 0; i < n; i++)
				xNodes[i] = addNode(xVars[i].id, 1);
			
			for (int i = 0; i < m; i++)
				valueNodes[i] = addNode(doms[i].toString(), 0);

			for (int i = 0; i < m; i++)
				countNodes[i] = addNode("c_" + doms[i].toString(), 0);

			Node s = addNode("source", 0);
			Node t = addNode("sink", -n);

			addArc(t, s, 0, 0, n*countedValue.length);
			
			for (int i = 0; i < n; i++) {
			
				// Arcs between x and d nodes.
				IntVar var = xVars[i];

				List<Arc> arcs = new ArrayList<Arc>();
				List<Domain> domains = new ArrayList<Domain>();

				IntDomain vardom = var.domain;
				for (int j = 0; j < m; j++) {
					if (vardom.isIntersecting(doms[j])) {
						arcs.add(addArc(xNodes[i], valueNodes[j], 0, 1));
						domains.add(doms[j]);
					}
					IntDomain notCounted = vardom.subtract(all);
					if (!notCounted.isEmpty()) {
						arcs.add(addArc(xNodes[i], t, 0, 1));
						domains.add(notCounted);
					}
				}
				handlerList.add(new DomainStructure(var, domains, arcs));
			}

			/*
			for (int i = 0; i < n; i++) {
				List<Arc> arcs = new ArrayList<Arc>();
				arcs.add( addArc(s, xNodes[i], 0, 0, 1) );
				List<Domain> domains = new ArrayList<Domain>();
				domains.add(all);
//				varList.add(new DomainStructure(xVars[i], domains, arcs));
			}
			*/
			
			for (int i = 0; i < doms.length; i++) {
				
				// shortage flow.
				if (softLowerBound != null)	
					addArc(s, countNodes[i], 1, 0, softLowerBound[i]);
				else
					addArc(s, countNodes[i], 1, 0, softCounters[i].max());
				
				if (softUpperBound != null) {
					if (n - softUpperBound[i] > 0) {
						// excess flow.
						addArc(countNodes[i], t, 1, 0, n - softUpperBound[i]);
					}
				} else {
					if (n - softCounters[i].min() > 0) {
						// excess flow.
						addArc(countNodes[i], t, 1, 0, n - softCounters[i].min());
					}
				}
				
				// Arcs, from value node to sink using flow equal counter.
				if (hardCounters != null)
					addArc(valueNodes[i], countNodes[i], 0, hardCounters[i]);
				else 
					addArc(valueNodes[i], countNodes[i], 0, hardLowerBound[i], hardUpperBound[i]);
				
				if (softLowerBound != null)
					addArc(countNodes[i], t, 0, softLowerBound[i], softUpperBound[i]);
				else
					addArc(countNodes[i], t, 0, softCounters[i]);
			}
			
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
