/**
 *  RegStateInt.java 
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
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.TimeStamp;

/**
 * It is an implementation of the Regular state which uses a separate successor for each 
 * value. Different values using different entries in the successor array can lead to the 
 * same successor. 
 * 
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 4.2
 */
public class RegStateInt extends RegState {

    private int[] toSucDom;
    
    /**
     * It constructs an integer based representation of the state.
     * @param level level of the state (position of the associated variable).
     * @param id id of the state.
     * @param sucNumber the number of successors.
     * @param posInArray the position within the array of states.
     */
    public RegStateInt(int level, int id, int sucNumber, int posInArray) {
    	
    	this.id = id;
    	this.level = level;	
    	this.successors = new RegState[sucNumber];
    	this.toSucDom = new int[sucNumber];
    	this.outDegree = 0;
    	this.inDegree = 0;
    	this.pos = posInArray;
    
    }
    
    @Override
	public void addTransitions(RegState suc, IntervalDomain val) {			
	
    	for (int h = 0; h < val.size ; h++) {
    		Interval inv = (val).intervals[h];
    		//for each interval of val
    		if (inv != null)
    			//For each value of the interval
    			for (int v = inv.min(); v <= inv.max(); v++)
    				addTransition(suc, v);
    	}						
    }
    

    @Override
	public void addTransition(RegState suc, Integer val) {
	
    	if (outDegree < this.successors.length) {				
    
    		this.successors[outDegree] = suc;
    		this.toSucDom[outDegree] = val;
    		this.outDegree++;
	    
    		suc.inDegree++;
    		return;
    	}
		
    	assert false : "no place in q_" + this.level + this.id + " for successor q_" + suc.level + suc.id;
	
    }

    @Override
	public boolean isActive(TimeStamp<Integer>[] activeLevels) {
	
    	return (pos <  activeLevels[level].value());
	
    }

	
    @Override
	public void removeTransition(int pos) {
	
    	if (pos < outDegree) {
    		
    		if (debugAll) 
    			System.out.println("remove the SUC arc q_"+level+"%"+id + " -> " + "q_"+this.successors[pos].level+"%"+this.successors[pos].id);
			    		
    		// must be first, before swap.
    		successors[pos].inDegree--;	
    		
    		// must be before other operation which use outDegree
    		outDegree--;
    		
    		RegState tmp = successors[outDegree];
    		successors[outDegree] = successors[pos];
    		successors[pos] = tmp;
	    
    		int tmpD = toSucDom[outDegree];
    		toSucDom[outDegree] = toSucDom[pos];
    		toSucDom[pos] = tmpD;
	    
    		return;
	    
    	}
    	
    	assert false : "State q_"+level+id+": Successors on position " + pos + " is already removed";
    	
    }
		    
    @Override
	public boolean intersects(IntDomain dom, int successorNo) {
	
    	return dom.isIntersecting(toSucDom[successorNo], toSucDom[successorNo]);
	
    }

    @Override
	public void setSupports(HashMap<Integer, RegEdge> hashMap, int i) {
		
    	if (hashMap.get(toSucDom[i]) == null)
    		hashMap.put(toSucDom[i], new RegEdge(this, successors[i]));
		
    }
	
	
    @Override
	public boolean updateSupport(RegEdge edge, int v) {
	
    	for (int suc = 0; suc < outDegree; suc++) {
    		if (toSucDom[suc] == v) {
    			edge.org = this; 
    			edge.dest = successors[suc];
    			return true;
    		}
    	}		
	
    	return false;
	
    }

    @Override
	public void add(IntDomain varDom, int successorNo) {
	
    	varDom.unionAdapt(toSucDom[successorNo], toSucDom[successorNo]);
	
    }

    @Override
	public String sucDomToString(int successorNo) {
	
    	return "" + toSucDom[successorNo];
    	
    }
    
    @Override
	public String toString() {
    	
    	return "id " + id + " level " + level + " inDegree " + inDegree + " outDegree" + outDegree + " position " + pos + " id " + id;
    	
    }
}


