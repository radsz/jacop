/**
 *  SparseSet.java 
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

/**
 * Sparse set representation of the set.
 *  
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class SparseSet {

	//@todo Is it possible to change the functions slightly so dense[0] = -1; is 
	// not really required to make it possible to add 0 at the first position. 
	
	/**
	 * Sparse array used within SparseSet functionality.
	 */
	public int [] sparse;
	
	/**
	 * Dense array used within SparseSet functionality.
	 */
	public int [] dense;
	
	/**
	 * It specifies number of elements in the SparseSet.
	 */
	public int members;

	/**
	 * It creates a SparseSet with given upper limit on the value
	 * of the biggest element in the set.
	 * @param size
	 */
	public SparseSet(int size) {

	    sparse = new int[size];
	    dense = new int[size];
	    members = 0;
	    
	    // Added so value 0 can be added first.
	    // TODO, test if that is still necessary after fixing a rare bug with addition.
	    dense[0] = -1;
	}

	/**
	 * It checks if the specified element belongs to the set.
	 * @param k element for which the membership in the given set is checked.
	 * @return true if k belongs to the sparse set, false otherwise.
	 */
	public boolean isMember(int k) {
	    
	    int a = sparse[k];

	    if (a < members && dense[a] == k) 
	    	return true;
	    else
	    	return false;

	}

	/**
	 * It adds an element to the set.
	 * @param value value being added.
	 * @return true if the value was not present before and was added to the set, false otherwise.
	 */
	public boolean addMember(int value) {
	    
	    int a = sparse[value];

	    if (a >= members || dense[a] != value) {
	    	sparse[value] = members;
	    	dense[members] = value;
	    	members++;
	    	return true;
	    }
	    else 
	    	return false;

	}

	/**
	 * It sets the size of the SparseSet.
	 * @param size the assigned size of the set.
	 */
	public void setSize(int size) {
	    members = size;
	}

	/**
	 * It returns true if the set is empty.
	 * @return true if the set is empty, false otherwise.
	 */
	public boolean isEmpty() {
		return members == 0;
	}
	
	/**
	 * It removes all the elements by setting the number of members to zero.
	 */
	public void clear() {
	    members = 0;
	    dense[0] = -1;
	}

	
	public String toString() {
	
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < members; i++)
			result.append(dense[i]).append(" ");
		
		return result.toString();
		
	}
	
	
}
