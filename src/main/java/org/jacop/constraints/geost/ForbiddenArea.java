/**
 *  ForbiddenArea.java 
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
import java.util.Collection;

import org.jacop.core.Var;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 * The simplest possible internal constraint: DBox defining a set of points
 * with which no object can overlap.
 * 
 */
public class ForbiddenArea extends InternalConstraint {

	//cache area, since it will make cardInfeasible() faster
	final int area;
	
	final int[] origin, length;
	
	final Geost geost;

	/**
	 * It constructs an internal constraint forbidding an object to be 
	 * placed within this aread.
	 * 
	 * @param geost the geost constraint in which this internal constraint exists. 
	 * @param origin the origin of the forbidden area.
	 * @param length the length of the forbidden area.
	 */
	public ForbiddenArea(Geost geost, int[] origin, int[] length) {
		this.origin = origin;
		this.length = length;
		
		this.geost = geost;
		
		int total = 1;
		for(int i = 0; i < origin.length; i++){
			total*=length[i];
		}
		area = total;
		
		
		assert (checkInvariants() == null) : checkInvariants();
		
	}

	/**
	 * It checks whether the ForbiddenArea is consistent.
	 * 
	 * @return It returns the string description of the problem, or null if no problem 
	 * with data structure consistency encountered. 
	 */
	public String checkInvariants() {
		
		if(origin.length != length.length)
			return "dimension mismatch";
		
		for(int i = 0; i < length.length; i++)
			if(length[i] < 0)
				return "negative length on dimension " + i;
		
		return null;
	}
	
	@Override
	public DBox isFeasible(Geost.SweepDirection min, 
						   LexicographicalOrder order,
						   GeostObject o, 
						   int currentShape, 
						   int[] c) {


		//avoid allocating new object if possible
		final int dimension = origin.length;
		DBox outBox = DBox.getAllocatedInstance(dimension+1);
		int[] outOrigin = outBox.origin;
		int[] outLength = outBox.length;


		/* 
		 * In the simplistic case where only d-boxes are considered, the only action needed
		 * is to shift the forbidden area according to the object's size (and internal shift),
		 * and adjust the size of the outbox
		 * 
		 * the lexicographical order has no influence
		 * the sweep direction has none either
		 */

		// TODO, are the dboxes within geost objects ordered according to its area? It may be useful as here we return 
		// the first dbox which generates useful outbox.
		for(DBox constrainedPiece : geost.getShape(currentShape).boxes){

			for(int i = 0; i < dimension; i++){
				//shift origin
				outLength[i] = length[i] + constrainedPiece.length[i]-1;
				//adjust size
				outOrigin[i] = origin[i]-(constrainedPiece.length[i]-1) - constrainedPiece.origin[i];
			}

			//the forbidden area is the same at any time, thus the box covers the whole space in that dimension
			// TODO, why -Integer.MAX_VALUE/2 and not Integer.MIN_VALUE for example?
			outOrigin[dimension] = - Integer.MAX_VALUE/2;
			outLength[dimension] = Integer.MAX_VALUE;

			assert(outBox.checkInvariants() == null) : outBox.checkInvariants();

			if(outBox.containsPoint(c))
				return outBox;
			
		}

		return null;
	}

	@Override
	public int[] AbsInfeasible(Geost.SweepDirection minlex) {
		//avoid allocating new object if possible
		final int dimension = origin.length;
		DBox outBox = DBox.getAllocatedInstance(dimension+1);
		int[] outOrigin = outBox.origin;
		
		if(minlex == Geost.SweepDirection.PRUNEMIN) {
			
			for(int i = 0; i < dimension; i++)
				outOrigin[i] = origin[i];
			
			outOrigin[dimension] = Integer.MIN_VALUE;
			return outOrigin;
			
		} else { // SweepDirection.PRUNEMAX
			
			for(int i = 0; i < dimension; i++)
				outOrigin[i] = origin[i] + length[i];
			
			outOrigin[dimension] = Integer.MAX_VALUE;
			return outOrigin;
			
		}
	}

	@Override
	public final int cardInfeasible() {
		return area;
	}

	@Override
	public Collection<Var> definingVariables() {
		return new ArrayList<Var>(0);
	}

	@Override
	public boolean isStatic() {
		return true;
	}
	
	@Override
	public boolean isSingleUse() {
		return false;
	}

}
