/**
 *  RegState.java 
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

import java.util.HashMap;

import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.TimeStamp;

/**
 * The state class representing a state in the regular automaton 
 * within Regular constraint. 
 * 
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 4.2
 */

public abstract class RegState {

    /**
     * It specifies the list of successor states for this state.
     */
    public RegState[] successors;
    
    /**
     * It specifies the number of edges outgoing from the state.
     */
    public int outDegree;
    
    
    /**
     * It specifies the number of edges incoming to the state.
     */
    public int inDegree;
    
    /**
     * The unique id of the state.
     */
    public int id;
    
    /**
     * It specifies the level, the variable position this state is associated with.
     */
    public int level;
    
    /**
     * The position of the state within a level.
     */
    public int pos;

    static final boolean debugAll = false;
    
    /**
     * It specifies that for a given values from an interval an automata
     * will move from the current state to the successor state.
     * @param suc successor state
     * @param val interval of accepting values.
     */
    
    public abstract void addTransitions(RegState suc, IntervalDomain val);

    /**
     * It specifies that for a given value an automata will move from the 
     * current state to the successor state.
     * @param suc successor state
     * @param val an accepting value
     */
    
    public abstract void addTransition(RegState suc, Integer val);

    /**
     * The function return if the state is still active. It depends on 
     * how many active levels remains for state level and the position of 
     * the state.
     * @param activeLevels - 
     * @return true is the state is still active.
     */
    
    public abstract boolean isActive(TimeStamp<Integer>[] activeLevels);
	
    /**
     * It informs the state that the edge on the given position is no longer
     * active.
     * 
     * @param pos position of the edge.
     */
    
    public abstract void removeTransition(int pos);
    
    /**
     * It checks if the accepting values associated with an edge intersect.
     * @param dom domain against which interesection is performed.
     * @param successorNo a position of the edge.
     * @return true if at least one value associated with an edge intersects with domain. 
     */

    public abstract boolean intersects(IntDomain dom, int successorNo);

    /**
     * 
     * @param hashMap It contains supports for all values of a given variable.
     * @param successorNo it specifies the edge position. 
     */
    
    public abstract void setSupports(HashMap<Integer, RegEdge> hashMap, int successorNo);
	
    /**
     * It updates a support if given state supports given value. 
     * 
     * @param edge information about support is stored here.
     * @param v value for which support is looked for.
     * @return It returns true if state has an edge which supports given value.
     */
    
    public abstract boolean updateSupport(RegEdge edge, int v);

    /**
     * It adds to domain values which are accepted by a given edge.
     * @param varDom - domain collecting suported values.
     * @param successorNo - position of an edge from which values are collected.
     */
    public abstract void add(IntDomain varDom, int successorNo);

    /**
     * 
     * @param successorNo - edge position.
     * @return It return the string representation of the values accepted by 
     * specified edge.
     */
    
    public abstract String sucDomToString(int successorNo);
    
}


