/**
 *  RegEdge.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2008 Polina Maakeva and Radoslaw Szymanek
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


package org.jacop.constraints.regular;

import org.jacop.core.TimeStamp;

/**
 * 
 * The class responsible for connecting two states in regular automaton
 * of Regular constraint. 
 * 
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 4.2
 */

public class RegEdge {

	/**
	 * The origin state.
	 */
	public RegState org;

	/**
	 * The destination state.
	 */
	public RegState dest;

	/**
	 * The constructor which creates an edge.
	 * @param org the origin state.
	 * @param dest the destination state.
	 */
	public RegEdge(RegState org, RegState dest) {
	    this.org = org;
	    this.dest = dest;
	}

	/**
	 * It checks if the edge is between active states.
	 * 
	 * @param activeLevels specifies last active states.
	 * @return true if both origin and destination state are active.
	 */
	public boolean check(TimeStamp<Integer>[] activeLevels) {

	    if ( org.isActive(activeLevels) && dest.isActive(activeLevels) )
	    	return true;

		return false;
	    

	}		
	
}		
