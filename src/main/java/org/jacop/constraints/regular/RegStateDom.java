/**
 *  RegStateDom.java 
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
import org.jacop.core.ValueEnumeration;

/**
 * It is a state representation which uses a domain representation
 * to represent all integers which can transition from this state
 * to the given successor state.
 * 
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 4.2
 */

public class RegStateDom extends RegState {
    
    private IntDomain[] toSucDom;
		
    /**
     * It constructs a state.
     * @param level the position of the associated variable with the state.
     * @param id the state id.
     * @param sucNumber the number of successors for this state.
     * @param posInArray the position within a states array for the level of this state.
     */
    public RegStateDom(int level, int id, int sucNumber, int posInArray) {
	this.id = id;
	this.level = level;	
	this.successors = new RegState[sucNumber];
	this.toSucDom = new IntDomain[sucNumber];
	this.outDegree = 0;
	this.inDegree = 0;
	this.pos = posInArray;
    }

    @Override
	public boolean isActive(TimeStamp<Integer>[] activeLevels) {
	
	return (pos <  activeLevels[level].value());
    }
    
    @Override
	public void removeTransition(int pos) {
	
    	if (pos < outDegree) {
    		if (debugAll) 
    			System.out.println("remove the SUC arc q_"+level+id + " -> " + "q_"+this.successors[pos].level+this.successors[pos].id);
				
    		successors[pos].inDegree--;			
    		RegState tmp = successors[outDegree-1];
    		successors[outDegree-1] = successors[pos];
    		successors[pos] = tmp;
	    
	    
    		IntDomain tmpD = toSucDom[outDegree-1];
    		toSucDom[outDegree-1] = toSucDom[pos];
    		toSucDom[pos] = tmpD;
	    
    		outDegree--;
	    
    		return;
	    
    	}
	
    	if (debugAll)
    		System.err.println("State q_"+level+id+": Successors on position " + pos + " is already removed");
    
    	assert false;
    	
    }

	@Override
	public void addTransition(RegState suc, Integer val) {
		
		for (int i =  0; i < outDegree; i++)
			if (successors[i] == suc) {
				toSucDom[i].unionAdapt(val, val);
				return;
			}
				
		if (outDegree < successors.length) {				
			successors[outDegree] = suc;
			toSucDom[outDegree] = new IntervalDomain(val, val);
			outDegree++;
			suc.inDegree++;
			return;
		    }
		
		assert false;
	}

	@Override
	public void addTransitions(RegState suc, IntervalDomain val) {

		for (int i =  0; i < outDegree; i++)
			if (successors[i] == suc) {
				toSucDom[i].unionAdapt(val.min(), val.max());
				return;
			}
				
		if (outDegree < successors.length) {				
			successors[outDegree] = suc;
			toSucDom[outDegree] = new IntervalDomain(val.min(), val.max());
			outDegree++;
			suc.inDegree++;
			return;
		    }
		
		assert false;
		
	}

	@Override
	public boolean intersects(IntDomain dom, int successorNo) {
		
		return dom.isIntersecting(toSucDom[successorNo]);
		
	}

	@Override
	public void setSupports(HashMap<Integer, RegEdge> hashMap, int i) {
		
		for (ValueEnumeration enumer = toSucDom[i].valueEnumeration(); enumer.hasMoreElements();) {
			
			int v = enumer.nextElement();

			if (hashMap.get(v) == null)	
			    hashMap.put(v, new RegEdge(this, successors[i]));
			
		}
		
	}

	@Override
	public String sucDomToString(int successorNo) {

		return toSucDom[successorNo].toString();
	
	}

	@Override
	public void add(IntDomain varDom, int successorNo) {
		
    	varDom.addDom(toSucDom[successorNo]);
    	
	}

	@Override
	public boolean updateSupport(RegEdge edge, int v) {
		
	 	for (int suc = 0; suc < outDegree; suc++) {
    		if (toSucDom[suc].contains(v)) {
    			edge.org = this; 
    			edge.dest = successors[suc];
    			return true;
    		}
    	}		
	
    	return false;
	
	}

}
