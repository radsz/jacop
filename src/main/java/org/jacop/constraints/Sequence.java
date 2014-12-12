/**
 *  Sequence.java 
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.HashMap;

import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.util.fsm.FSM;
import org.jacop.util.fsm.FSMState;
import org.jacop.util.fsm.FSMTransition;

/**
 *
 * It constructs a Sequence constraint. The sequence constraint
 * establishes the following relationship: For a given list of 
 * variables (list) and the length of each sequence (q) it makes
 * sure that each subsequence of consecutive variables from the list
 * contains between min and max values from the given set.
 * 
 * @author Radoslaw Szymanek and Polina Makeeva
 * @version 4.2
 */

public class Sequence extends DecomposedConstraint {

	IntervalDomain set;
	int min;
	int max;
	int q;
	IntVar[] list;
	ArrayList<Constraint> constraints;
	
	/**
	 * It creates a Sequence constraint. 
	 * 
	 * @param list variables which assignment is constrained by Sequence constraint. 
	 * @param set set of values which occurrence is counted within each sequence.
	 * @param q the length of the sequence
	 * @param min the minimal occurrences of values from set within a sequence.
	 * @param max the maximal occurrences of values from set within a sequence.
	 */
	public Sequence(IntVar[] list, IntervalDomain set, int q, int min, int max) {
	
		this.min = min;
		this.max = max;

		this.list = new IntVar[list.length];
		for (int i = 0; i < list.length; i++) {
			assert (list[i] != null) : i + "-th element in the list is null";
			this.list[i] = list[i];
		}

		this.set = set.clone();
		this.q = q;
	}	

	@Override
	public void imposeDecomposition(Store store) {
			
		if (constraints == null)
			decompose(store);
		
		for (Constraint c : constraints)
			store.impose(c, queueIndex);
		
	}

	@Override
	public ArrayList<Constraint> decompose(Store store) {

		if (constraints != null)
			return constraints;
		
		IntDomain setComplement = new IntervalDomain();
		for (IntVar var : list)
			setComplement.addDom(var.domain);
		setComplement = setComplement.subtract(set);
		
		FSM fsm  = new FSM();

		fsm.initState =  new FSMState();
		fsm.allStates.add(fsm.initState);
		
		HashMap<FSMState, Integer> mappingQuantity = new HashMap<FSMState, Integer>();
		HashMap<String, FSMState> mappingString = new HashMap<String, FSMState>();
		
		mappingQuantity.put(fsm.initState, 0);
		mappingString.put("", fsm.initState);
		
		for (int i = 0; i < q; i++) {
			HashMap<String, FSMState> mappingStringNext = new HashMap<String, FSMState>();
			
			for (String stateString : mappingString.keySet()) {
				
				FSMState state = mappingString.get(stateString);
				
				if (mappingQuantity.get(state) < max) {
					// transition 1 (within a set) is allowed
					FSMState nextState = new FSMState();
					state.addTransition(new FSMTransition(set, nextState));
					mappingStringNext.put(stateString + "1", nextState);
					mappingQuantity.put(nextState, mappingQuantity.get(state) + 1);
				}
				
				if (mappingQuantity.get(state) + (q-i) > min) {
					// transition 0 (outside set) is allowed
					FSMState nextState = new FSMState();
					state.addTransition(new FSMTransition(setComplement, nextState));
					mappingStringNext.put(stateString + "0", nextState);
					mappingQuantity.put(nextState, mappingQuantity.get(state) );
				}
			}
			
			fsm.allStates.addAll( mappingString.values() );
			mappingString = mappingStringNext;
			
		}
		
		fsm.allStates.addAll( mappingString.values() );
		fsm.finalStates.addAll( mappingString.values() );
		
		for (String description : mappingString.keySet() ) {
			
			String one = description.substring(1) + "1";
			
			FSMState predecessor = mappingString.get(description);
			FSMState successor = mappingString.get(one);
			if (successor != null)
				predecessor.addTransition(new FSMTransition(set, successor));
			
			String zero = description.substring(1) + "0";
			successor = mappingString.get(zero);
			if (successor != null)
				predecessor.addTransition(new FSMTransition(setComplement, successor));
		}
				   
		fsm.resize();

		constraints = new ArrayList<Constraint>();
		constraints.add(new Regular(fsm, list));
		
		return constraints;
	}


}
