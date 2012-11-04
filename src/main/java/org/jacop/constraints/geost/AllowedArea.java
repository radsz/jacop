/**
 *  AllowedArea.java 
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import org.jacop.core.IntDomain;
import org.jacop.core.Var;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 * Constraint that represents a domain in which objects need to be contained
 *
 */
public class AllowedArea extends InternalConstraint {

	// TODO, What is the reason for using it? What are the limitation of using this solution?
	private static final int half_max = ( Integer.MAX_VALUE - 1 ) / 2;
		
	final Geost geost;
	
	final int[] origin, length;
	
	/**
	 * It constructs an internal Geost constraint that restricts an object
	 * to be within an allowed area.
	 * 
	 * @param geost the geost constraint for which the internal constraint is being created.
	 * @param origin it specifies the origin of the area in which objects have to be placed.
	 * @param length it specifies the length of the area in each dimension in which the objects have to be placed.
	 */
	public AllowedArea(Geost geost, int[] origin, int[] length) {
		
		this.geost = geost;
		this.origin = origin;
		this.length = length;
			
		assert (checkInvariants() == null) : checkInvariants();
		
	}

	
	/**
	 * It checks that this constraint has consistent data structures.
	 * 
	 * @return a string describing the consistency problem with data structures, null if no problem encountered.
	 */
	
	public String checkInvariants(){
	
		if(this.origin.length != this.length.length){
			return "dimension mismatch between origin and length array.";
		}
		
		for(int i = 0; i < length.length; i++)
			if(length[i] < 0)
				return "negative length on dimension " + i;
		
		return null;
	}

	@Override
	public int cardInfeasible() {
		// TODO, change it to Geost constant, capable of generating outboxes.
		return 10; //non zero since it can generate outboxes
	}

	@Override
	public DBox isFeasible(Geost.SweepDirection min, 
						   LexicographicalOrder order,
						   GeostObject o, 
						   int currentShape, 
						   int[] c) {
		
		/*
		 * TODO improve this implementation, which is slightly inefficient when c will 
		 * need to move next to the allowed area during a sweep. Indeed, this
		 * will cause (at least) 2 steps to be used, but a box could be created
		 * to skip it all in a single step.
		 * This is possible because the sweep direction is provided by the order parameter
		 * 
		 * current:
		 * 
		 *               |       
		 *    ------     ------       
		 *    |    |     |    | 
		 *    |    |   x |    | 
		 * - -------     ------ 
		 *  x |          |
		 *  
		 *  better:
		 *  
		 *    |      
		 *    ------        
		 *    |    |  
		 *    |    |  
		 *    ------  
		 *  x | 
		 */
		
		/* we can use the bounding box in this case, since the allowed area
		 * is a non complex box
		 */
		DBox constrainedBox = geost.getShape(currentShape).boundingBox();

		final int dimension = origin.length;
		DBox outbox = DBox.getAllocatedInstance(dimension+1);

		//counter for the number of times the point is in the allowed domain
		int inCount = 0;

		for(int i = 0; i < dimension; i++) {
			if(c[i] + constrainedBox.origin[i] < origin[i]){ 
				//beginning of other box is before beginning of area
				//point is before area, outbox covers all up to the area limit
				outbox.origin[i] = - half_max +  origin[i] - constrainedBox.origin[i]; 
				/*
				* this +1 is needed because of the definition of an outbox: the lexicographcally smallest
				* point of the outbox is not feasible (but the largest is)
				*/
				
				outbox.length[i] = half_max;
			} else if(c[i] + constrainedBox.length[i] + constrainedBox.origin[i] <= origin[i] + length[i] ){
				//point is inside area

				//increment inside count
				inCount++;

				//outbox covers everything
				outbox.origin[i] = origin[i] - half_max;
				outbox.length[i] = Integer.MAX_VALUE;
			} else {
				//point is after area, outbox covers everything from area boundary
				outbox.origin[i] = origin[i] + length[i] - constrainedBox.length[i] - constrainedBox.origin[i] + 1; //+1 for same reason as before
				outbox.length[i] = half_max;
			}
		}
		
		//the allowed area is the same at any time, thus the box covers the whole space in that dimension
		outbox.origin[dimension] = - half_max;
		outbox.length[dimension] = Integer.MAX_VALUE;

		if(inCount == dimension){
			//point is inside for all dimensions, no forbidden domain
			return null;
		} else {
			//point is outside for some of the domains, return the generated box
			return outbox;
		}
		
	}

	@Override
	public int[] AbsInfeasible(Geost.SweepDirection minlex) {
		
		//the point is at either extremum of the space, depending on the minlex parameter
		//avoid allocating space
		DBox dataBox = DBox.getAllocatedInstance(origin.length+1);
		
		switch (minlex){
		case PRUNEMAX:
			Arrays.fill(dataBox.origin, IntDomain.MaxInt);
			break;
		case PRUNEMIN:
			Arrays.fill(dataBox.origin, IntDomain.MinInt);
			break;
		}
		
		return dataBox.origin;
	}

	@Override
	public Collection<Var> definingVariables() {
		return new ArrayList<Var>(0);
	}

	@Override
	public String toString(){
		
		StringBuffer result = new StringBuffer();
		
		result.append("AllowedArea(").append( Arrays.toString(origin) );
		result.append(", ").append( Arrays.toString(length) ).append( ")" );
		
		return result.toString();
	}

	@Override
	public boolean isStatic() {
		return true;
	}
	
	@Override
	public boolean isSingleUse() {
		return true;
	}
	
	
}
