/**
 *  IndexDomainView.java 
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

package org.jacop.util;

import java.util.Arrays;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Defines index domain view for a variable and related operations on it.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class IndexDomainView {

	private static final boolean debugAll = false;

	IntVar var;
	
	/**
	 * It specifies mapping of the index value onto value in the domain of the variable.
	 */
	public int [] indexToValue;
	
	boolean [] forRemoval;
	
	boolean viewOfSparseDomain;
	
	/**
	 * It creates an index domain view for a given variable. It currently implements only
	 * sparse representation for index domain view.
	 * @param var variable for which the index domain view is created.
	 * @param forceSparse forces a sparse representation inside (one value has one entry within the mapping).
	 */
	public IndexDomainView(IntVar var, boolean forceSparse) {
		
		this.var = var;
		viewOfSparseDomain = var.domain.isSparseRepresentation() || var.domain.getSize() < 10 || forceSparse;
		
		if (viewOfSparseDomain) {
			
			indexToValue = new int[var.domain.getSize()];
			int i = 0;
			for(ValueEnumeration enumer = var.domain.valueEnumeration(); enumer.hasMoreElements();) {
				indexToValue[i++] = enumer.nextElement();
			}
			
		}
		else {
			
			indexToValue = new int[var.domain.noIntervals()];
			
			assert false : "Not implemented functionality. Only sparse index domain view is implemented.";
		}
		
		forRemoval = new boolean[indexToValue.length];
		
	}

	/**
	 * It creates an index domain view with only given values being in focus 
	 * of the index domain view. Only values in focus may end up being removed
	 * if no support is founded.
	 * 
	 * @param var variable for which the index domain view is created. 
	 * @param valuesInFocus values which are of interest.
	 */
	public IndexDomainView(IntVar var, int [] valuesInFocus) {
		
		this.var = var;
		viewOfSparseDomain = true;

		indexToValue = new int[valuesInFocus.length];

		System.arraycopy(valuesInFocus, 0, indexToValue, 0, valuesInFocus.length);

		Arrays.sort(indexToValue);
				
		forRemoval = new boolean[indexToValue.length];
		
	}
	
	/**
	 * It marks all values in focus of the index domain view as not supported and 
	 * requiring support to be established.
	 */
	public void intializeSupportSweep() {
		
		if (viewOfSparseDomain) {
			
			if (var.domain.getSize() <= indexToValue.length) {
				Arrays.fill(forRemoval, false);
			
				int index = 0;
				for(ValueEnumeration enumer = var.domain.valueEnumeration(); enumer.hasMoreElements();) {
					int value = enumer.nextElement();
					while (indexToValue[index] < value) {
						index++;
						if (index == indexToValue.length)
							return;
					}
				
					if (indexToValue[index] == value)
						forRemoval[index] = true;
				}
			}
			else {
				Arrays.fill(forRemoval, true);
				for (int i = 0; i < indexToValue.length; i++)
					if (!var.domain.contains(indexToValue[i]))
						forRemoval[i] = false;
			}
		}
		else {
			
			assert false : "Not yet implemented functionality for non sparse representation";
	
		}
		
	}

	
	/**
	 * It removes all values for which no support was found since the initialization of 
	 * the support sweep.
	 * @param store
	 */
	public void removeUnSupportedValues(Store store) {
		
		if (viewOfSparseDomain) {
			for (int i = 0; i < indexToValue.length; i++)
				if (forRemoval[i])
					var.domain.inComplement(store.level, var, indexToValue[i]);
		}
		
	}

	/**
	 * It checks if the value of a given index is still in the domain.
	 * @param i index which is being checked if it is still contained within a variable.
	 * @return true if the i-th value is still in the domain, false otherwise.
	 * 
	 */
	public boolean contains(int i) {
		// check if ith index is still int the domain 
		return var.domain.contains(indexToValue[i]);
	}

	/**
	 * 
	 * It returns true if the ith-value was supported before.
	 * @param i the position of the value which is being supported.
	 * @return false if value has not been supported before by other value, true otherwise.
	 */
	public boolean setSupport(int i) {

		if (viewOfSparseDomain) {
			// sets the boolean flag for ith index and returns if the index was supported before.
			if (forRemoval[i]) {
				forRemoval[i] = false;
				return false;
			}
			else {
				return true;
			}
		}
		else {
			assert false : "Not implemented yet";
			return false;
		}
	}

	/**
	 * It checks if all values are currently supported. 
	 * @return true if all values are supported, false otherwise.
	 */
	public boolean isSupported() {
		
		if (viewOfSparseDomain) {

			for (int i = 0; i < forRemoval.length; i++)
				if (forRemoval[i])
					return false;
			return true;
		}
		else {
			
			assert false : "Not yet implemented functionality";
			return false;
			
		}
	}
	
	/**
	 * It finds an index for a given value.
	 * @param value value for which the indexed is searched for.
	 * @return index for a given value.
	 */
	public int indexOfValue(int value) {
		
		if (!viewOfSparseDomain) {
			
			assert false : "Not yet implemented functionality";
			return 0;
			
		}
		
		int left = 0;
		int right = indexToValue.length - 1;

		int position = (left + right) >> 1;

		if (debugAll) {
			System.out.println("Looking for " + value);
			for (int v : indexToValue)
				System.out.print("val " + v);
			System.out.println("");
		}

		while (!(left + 1 >= right)) {

			if (debugAll)
				System.out.println("left " + left + " right " + right
						+ " position " + position);

			if (indexToValue[position] > value) {
				right = position;
			} else {
				left = position;
			}

			position = (left + right) >> 1;

		}

		if (indexToValue[left] == value)
			return left;

		if (indexToValue[right] == value)
			return right;

		return -1;

	}	
	

	/**
	 * It returns size of the variable for which the index domain view is being created.
	 * 
	 * @return number of values in the variable domain for 
	 * which the index domain view is being created.
	 */
	public int getSize() {
		return var.getSize();
	}
	
}
