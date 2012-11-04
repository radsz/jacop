/**
 *  DomainHoles.java 
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
package org.jacop.constraints.geost;

import java.util.Arrays;
import java.util.Collection;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 * 
 * Internal constraint used to generate outboxes that correspond to holes in the 
 * feasible domain of the object origin.
 * 
 * Due to the amount of space it can cover, this constraint will probably cause
 * slower processing in case of domains with holes, when using the event point
 * series to prune the set of internal constraints
 * 
 * 
 * TODO implement outbox generation for time (if feasible)
 */

public class DomainHoles extends InternalConstraint {

	final static boolean debug = false;
	
	final GeostObject object;
	
	/**
	 * It creates Domain Holes internal constraint for a given object. This
	 * internal constraint reflects the holes in the domains of the objects 
	 * variables. 
	 * 
	 * @param object the object for which the domain holes internal constraint 
	 * is applied to.
	 */
	public DomainHoles(GeostObject object) {
		super();
		this.object = object;
	}

	@Override
	public int[] AbsInfeasible(Geost.SweepDirection minlex) {
		
		//don't allocate array for transient data
		int[] outPoint = DBox.getAllocatedInstance(object.dimension).origin;
		
		/*
		 * if for some dimension there is a hole, the hole will slice the 
		 * whole feasible domain; in other words, the minimal point is
		 * the extremum of the hole in its dimension, and the complete space
		 * in the other dimensions
		 * 
		 * A direct implication is that if there are holes in more than
		 * one dimension, the extrema are the whole space
		 */
		
		//counts the number of dimensions that have a hole
		int holeCount = 0;
		
		//the dimension that has a hole
		int holeDimension = 0;
		
		//the extremum of the hole in the dimension of interest
		int holeBound = 0;
		
		for(int i = 0; i < object.dimension; i++) {
			
			IntVar v = object.coords[i];
			
			if(v.domain.noIntervals() > 1) {
				
				holeCount++;
				
				if(holeCount > 1) 
					break; //stop here if we have already seen a hole
				
				holeDimension = i;
				
				//implies that there is at least one hole in the domain
				switch ( minlex ) {
				
					case PRUNEMAX:
						//last infeasible point is lower bound of last interval
						holeBound = v.domain.getInterval( v.domain.noIntervals() - 1).min;
						break;
					case PRUNEMIN:
						//first infeasible point is upper bound of first interval
						holeBound = v.domain.getInterval(0).max;
						break;
				}
				
			}
			
		}
		
		assert (holeCount == 0 || holeCount == 1 || holeCount == 2) : "bad number of holes";
		
		if(holeCount == 0) {
			//no hole: no infeasible area
			Arrays.fill(outPoint, 0);
			
		} else { 
			
			/*
			 * holes in at least 2 different dimensions, absolute max infeasible points are extrema
			 * of the domain
			 */
			switch (minlex){
			case PRUNEMAX:
				Arrays.fill(outPoint, Integer.MAX_VALUE);
				break;
			case PRUNEMIN:
				Arrays.fill(outPoint, Integer.MIN_VALUE);
				break;
			}
			
			if (holeCount == 1)
				//same thing as before, except that in the dimension with the hole, the extremum is the hole extremum
				outPoint[holeDimension] = holeBound;
				
		}
		
		return outPoint;
	}

	
	
	/**
	 * It specifies if still any domain variable of the object in focus by this domain holes constraint 
	 * has still any holes.
	 * 
	 * @return true if there are holes, false otherwise.
	 */
	public boolean stillHasHole() {
		
		assert (object.dimension == object.coords.length) : "object dimension is not equal to dimension indicated by coords.";
			
		IntVar[] vars = object.coords;
		
		for (IntVar v : vars)
			if(v.domain.noIntervals() > 1)
				return true;
		
		return false;
		
	}

	@Override
	public int cardInfeasible() {
		//priority is actually not defined here, but in findForbiddenDomain
		return 0;
	}

	@Override
	public Collection<Var> definingVariables() {
		return object.getVariables();
	}

	@Override
	public DBox isFeasible(Geost.SweepDirection min, LexicographicalOrder order,
						   GeostObject o, int currentShape, int[] c) {
		
		if(o != object) return null; //only need to work if this is the same object
		
		DBox forbiddenRegion = DBox.getAllocatedInstance(o.dimension+1);

		int[] forbiddenOrigin = forbiddenRegion.origin;	
		int[] forbiddenLength = forbiddenRegion.length;
		
		//TODO make sure which dimension ordering is the best
		/*
		 * give an outbox that advances the sweep most in its current dimension,
		 * in other words, begin with the less significant dimension.
		 * The forbidden domain may be seen again, but for a more significant dimension
		 * only.
		 * This still needs to be discussed.
		 */
		for(int i = 0; i < o.dimension+1; i++){
			
			int d = order.dimensionAt(i); 
			if(d == o.dimension) { 
				// ignore time for now //TODO implement if possible, to improve pruning.
				
			} else {
				IntDomain dom = o.coords[d].domain;
				if(dom.noIntervals() == 1) continue; //there are no domain holes in this dimension
				if(! dom.contains(c[d])) {
					
					assert dom.nextValue(c[d]) != c[d] && dom.previousValue(c[d]) != c[d] : "current point not located in a domain hole";

					if(debug)
						System.out.println(Arrays.toString(c) + " is in a hole of " + o.coords[d]);
					
					/*
					 * we found a hole, the infeasible slice is the whole domain, except in the
					 * dimension of the hole
					 */
					for(int j = 0; j < o.dimension + 1; j++){
						if(j==d) {
							forbiddenOrigin[j] = dom.previousValue(c[d])+1; //min bound not feasible
							forbiddenLength[j] = dom.nextValue(c[d]) - forbiddenOrigin[j]; // max bound feasible
						} else {
							forbiddenOrigin[j] = Integer.MIN_VALUE/2;
							forbiddenLength[j] = Integer.MAX_VALUE;
						}
					}

					if(debug){
						System.out.println("forbidden domain: " + forbiddenRegion);
					}

					assert forbiddenRegion.checkInvariants()  == null : forbiddenRegion.checkInvariants();

					assert forbiddenRegion.containsPoint(c) : "bad forbidden region, c is not contained";

					return forbiddenRegion;
				}
				if(debug){
					System.out.println(Arrays.toString(c) + " is not in a hole of " + o.coords[d]);
				}
			}
		}
		
		return null;
	}

	@Override
	public boolean isStatic() {
		return false;
	}

	@Override
	public boolean isSingleUse() {
		return false;
	}
}
