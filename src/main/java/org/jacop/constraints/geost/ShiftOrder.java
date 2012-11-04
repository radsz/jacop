/**
 *  ShiftOrder.java 
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

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 *
 * It provides a very simple lexicographical order based on the dimension
 * ordering, with the possibility to choose the most significant dimension
 */

public class ShiftOrder implements LexicographicalOrder {
	
	int mostSignificant;
	
	final int noOfDimensions;
	
	final int[] masterOrdering;
	
	final int[] orderingWithShiftConsidered;//stores precomputed results

	/**
	 * It creates a lexicographical order with the possibility 
	 * to shift the order according to the most significant dimension.
	 * 
	 * @param dimensions number of dimensions. 
	 * @param mostSignificant the position of the most significant dimension.
	 */
	public ShiftOrder(int dimensions, int mostSignificant){
		
		this.noOfDimensions = dimensions;
		this.mostSignificant = mostSignificant;
		
		orderingWithShiftConsidered = new int[noOfDimensions];
		adjustOrderingToShift();
		
		masterOrdering = new int[noOfDimensions];
		for(int i = 0; i < noOfDimensions; i++)
			masterOrdering[i] = i;

		assert  checkInvariants() == null : checkInvariants();
	}
	
	
	/**
	 * It checks that this order has consistent data structures.
	 * 
	 * @return a string describing the consistency problem with data structures, null if no problem encountered.
	 */
	public String checkInvariants(){
		
		if(noOfDimensions <= 0)
			return "invalid number of dimensions";
		
		if(mostSignificant < 0) 
			return "most significant dimension is negative";
		
		if(mostSignificant >= noOfDimensions) 
			return "most significant dimension larger than or equal to total number of dimensions";
		
		return null;
	}
	
	/**
	 * It adjust the ordering to the shift caused by most significant dimension which is no longer
	 * positioned at index 0.
	 */
	private void adjustOrderingToShift(){
		
		for(int i = 0; i < noOfDimensions; i++)
			orderingWithShiftConsidered[i] = (i+mostSignificant)%noOfDimensions;
			
	}
	
	
	public int compare(int[] p1, int[] p2) {
		
		assert (p1.length == p2.length) : "dimension mismatch";
		
		for(int i = 0; i < noOfDimensions; i++) {
			
			int lexI = orderingWithShiftConsidered[i];
			
			if (p1[lexI] < p2[lexI])
				return -1;
			else if(p1[lexI] > p2[lexI])
				return 1;
		
		}
		
		return 0;
	}

	
	public int dimensionAt(int precedenceLevel) {
		return orderingWithShiftConsidered[precedenceLevel];
	}

	
	public int precedenceOf(int dimension) {
		
		return (dimension - mostSignificant) % noOfDimensions;
	
	}
	
	
	public void setMostSignificantDimension(int dimension) {

		this.mostSignificant = dimension;
		adjustOrderingToShift();
		
		assert checkInvariants() == null : checkInvariants();
	
	}

	
	public int getMostSignificantDimension() {
		return mostSignificant;
	}

	
	public int[] masterOrdering() {
		return masterOrdering;
	}

	
}
