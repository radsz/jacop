/**
 *  FSMState.java 
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

package org.jacop.util.fsm;

import java.util.HashSet;

/**
 * @author Radoslaw Szymanek
 * @version 4.2
 */

public class FSMState {	
	
	/**
	 * Id of the state. There can be multiple copies of the same state with the same id.
	 */
	public int id;
	
	/**
	 * It specifies the list of transitions  outgoing from this state.
	 */
	public HashSet<FSMTransition> transitions;
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"transitions", "id"};

	/**
	 * It constructs a FSM state.
	 * 
	 * @param transitions it specifies transition 
	 * @param id
	 */
	public FSMState(HashSet<FSMTransition> transitions, int id) {
		this.transitions = transitions;
		this.id = id;
	}
	
	/**
	 * It creates a state with id equl to the number of instances FSMState created.
	 */
	public FSMState(){
		this.id = FSM.stateId++;
		transitions = new  HashSet<FSMTransition>();
	}
		
	
	/**
	 * It creates a state with an id as the id specified by a supplied state.
	 * @param a state from which id is taken while creating this state.
	 */
	public FSMState(FSMState a) {
		this.id = a.id;
		transitions = new  HashSet<FSMTransition>();
	}
	
	/**
	 * Performing deep clone unless this state has already a state with
	 * the same id in the array of states.
	 * @param states it contains the states which do not need to be created, only reused.
	 * @return a deep clone of the current state.
	 */
	public FSMState deepClone(HashSet<FSMState> states)
	{
		
		// replace by HashSet contains check.
		FSMState newFSM = null;
		for (FSMState s : states)
			if (s.id == this.id)
				newFSM = s;
		if (newFSM != null) return newFSM;
		
		newFSM = new FSMState(this);
		states.add(newFSM);
		for(FSMTransition t : this.transitions)
			newFSM.transitions.add(t.deepClone(states));
		return newFSM;
	}
	
	/**
	 * It adds transition to the list of transitions from 
	 * this state.
	 * @param transition the transition being added.
	 */
	public void addTransition(FSMTransition transition) {
		transitions.add(transition);
	}
	
	@Override
	public boolean equals(Object o) {
		return this.id == ((FSMState)o).id;
	}
	
	@Override
	public int hashCode() {
		return id;
	}
	
	@Override
	public String toString() {
		return "state_" + String.valueOf( id );		
	}
	
}
