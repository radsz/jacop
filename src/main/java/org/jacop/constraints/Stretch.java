/**
 *  Stretch.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Radoslaw Szymanek and Polina Makeeva
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
 * It constructs a Stretch constraint based on Regular constraint. An example
 * of a Stretch constraint is values = [1, 2], min = [1, 2], max = [2, 3], and
 * x = [x1, x2, x3, x4]. It specifies that variables x are equal to value 1 and 
 * 2, and any sequence of values 1 has to be of length between 1 and 2, and any 
 * sequence of values 2 has to be of length between 2 and 3.
 * 
 * @author Radoslaw Szymanek and Polina Makeeva
 * @version 4.2
 */

public class Stretch extends DecomposedConstraint {

	int[] values;
	int[] min;
	int[] max;
	IntVar[] x;
	ArrayList<Constraint> constraints;
	
	/**
	 * It creates a Stretch constraint. 
	 * 
	 * @param values a list of values which can be taken by variables.
	 * @param min the minimal sequence length for each value.
	 * @param max the maximal sequence length for each value.
	 * @param x variables which assignment is constrained by Stretch constraint. 
	 */
	public Stretch(int[] values, int[] min, int[] max, IntVar[] x) {
	
		assert (values != null) : "values argument is null";
		this.values = new int[values.length];
		System.arraycopy(values, 0, this.values, 0, values.length);

		assert (min != null) : "min argument is null";
		this.min = new int[min.length];
		System.arraycopy(min, 0, this.min, 0, min.length);

		assert (max != null) : "max argument is null";
		this.max = new int[max.length];
		System.arraycopy(max, 0, this.max, 0, max.length);

		assert (x != null) : "x argument is null";
		this.x = new IntVar[x.length];
		for (int i = 0; i < x.length; i++) {
			assert (x[i] != null) : i + "-th element of x list is null.";
			this.x[i] = x[i];
		}

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
		
		FSM fsm  = new FSM();

		fsm.initState =  new FSMState();
		
		fsm.allStates.add(fsm.initState);
		
		FSMState[] oneStep = new FSMState[this.values.length];
		
		for (int k = 0; k < this.values.length; k++)  {
			
			IntDomain d = new IntervalDomain(this.values[k], this.values[k]);
			
			FSMState current = new FSMState();
			
			fsm.initState.addTransition(new FSMTransition(d, current));
			
			fsm.allStates.add(current);
			
			oneStep[k] = current;
			
			if (min[k] <= 1) 
				fsm.finalStates.add(current); 
		
		}
	
		for (int vk = 0; vk < this.values.length; vk++) 
			if (min[vk] <= 1)
				for (int other = 0; other < this.values.length; other++)  
					if (other != vk)
						oneStep[vk].addTransition(new FSMTransition(new IntervalDomain(this.values[other],this.values[other]), oneStep[other]));	
		
		FSMState prev = null;
		
		for (int vk = 0; vk < this.values.length; vk++)  {
			prev = oneStep[vk];
			IntDomain d = new IntervalDomain(this.values[vk], this.values[vk]);
			for (int step = 2; step <= max[vk]; step ++) {
		
				FSMState cur1 = new FSMState();
				
				prev.addTransition(new FSMTransition(d,cur1));
				
				fsm.allStates.add(cur1);
				
				if (step >= min[vk]) {
					
					fsm.finalStates.add(cur1);
					for (int other = 0; other < this.values.length; other++)  
						if (other != vk)
							cur1.addTransition(new FSMTransition(new IntervalDomain(this.values[other],this.values[other]), oneStep[other]));					
					
				}
				
				prev = cur1;
			}
		}
		   
		fsm.resize();

		constraints = new ArrayList<Constraint>();
		constraints.add(new Regular(fsm, x));
		
		return constraints;
	}


}
