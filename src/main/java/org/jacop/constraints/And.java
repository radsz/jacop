/**
 *  And.java 
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
import java.util.Hashtable;

import org.jacop.core.Domain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.util.SimpleHashSet;

/**
 * Constraint c1 /\ c2 ... /\ cn
 * 
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class And extends PrimitiveConstraint {

	static int IdNumber = 1;

	Hashtable<Var, Integer> pruningEvents;

	/**
	 * It specifies a list of constraints which must be satisfied to keep And constraint satisfied.
	 */
	public PrimitiveConstraint listOfC[];

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"listOfC"};

	/**
	 * It constructs an And constraint based on primitive constraints. The 
	 * constraint is satisfied if all constraints are satisfied.
	 * @param listOfC arraylist of constraints
	 */
	public And(ArrayList<PrimitiveConstraint> listOfC) {
		
		assert (listOfC != null) : "List of constraints is empty";
		
		this.queueIndex = 1;
		numberId = IdNumber++;
		
		this.listOfC = new PrimitiveConstraint[listOfC.size()];
		
		int i = 0;
		
		for (PrimitiveConstraint cc : listOfC) {
			assert (cc != null) : (i+1) + "-th element of constraint list is insolvent";
			numberArgs += cc.numberArgs();
			this.listOfC[i++] = cc;
		}
	}

	/**
	 * It constructs a simple And constraint based on two primitive constraints.
	 * @param c1 the first primitive constraint
	 * @param c2 the second primitive constraint
	 */
	public And(PrimitiveConstraint c1, PrimitiveConstraint c2) {
		
		numberId = IdNumber++;
		
		this.listOfC = new PrimitiveConstraint[2];
		
		numberArgs += c1.numberArgs();
		this.listOfC[0] = c1;
		
		numberArgs += c2.numberArgs();
		this.listOfC[1] = c2;
	}

	/**
	 * It constructs an And constraint over an array of primitive constraints.
	 * @param c an array of primitive constraints constituting the And constraint.
	 */
	public And(PrimitiveConstraint[] c) {
		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.listOfC = new PrimitiveConstraint[c.length];
		for (int i = 0; i < c.length; i++) {
			this.numberArgs += c[i].numberArgs();
			this.listOfC[i] = c[i];
		}
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>();

		for (Constraint cc : listOfC)
			for (Var V : cc.arguments())
				variables.add(V);

		return variables;
	}

	boolean propagation;
	
	@Override
	public void consistency(Store store) {

		propagation = true;

		do {
			
			// Variable propagation can be set to true again if queueVariable function is being called. 
			propagation = false;
			
			for (Constraint cc : listOfC)
				cc.consistency(store);
			
		}
		while (propagation);
		
	}

	@Override
	public int getNestedPruningEvent(Var var, boolean mode) {

		return getConsistencyPruningEvent(var);

	}


	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
			if (pruningEvents != null) {
				Integer possibleEvent = pruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}

			int eventAcross = -1;

			for (int i = 0; i < listOfC.length; i++) {
				if (listOfC[i].arguments().contains(var)) {
					int event = listOfC[i].getNestedPruningEvent(var, true);
					if (event > eventAcross)
						eventAcross = event;
				}
			}

			if (eventAcross == -1)
				return Domain.NONE;
			else
				return eventAcross;

		}
	
	@Override
	public int getNotConsistencyPruningEvent(Var var) {

			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}

			int eventAcross = -1;

			for (int i = 0; i < listOfC.length; i++) {
				if (listOfC[i].arguments().contains(var)) {
					int event = listOfC[i].getNestedPruningEvent(var, false);
					if (event > eventAcross)
						eventAcross = event;
				}
			}

			if (eventAcross == -1)
				return Domain.NONE;
			else
				return eventAcross;

		}

	@Override
	public void impose(Store store) {

		SimpleHashSet<Var> variables = new SimpleHashSet<Var>();

		for (int i = 0; i < listOfC.length; i++)
			for (Var var : listOfC[i].arguments())
				variables.add(var);

		while (!variables.isEmpty()) {
			Var var = variables.removeFirst();
			var.putModelConstraint(this, getConsistencyPruningEvent(var));
		}

		for (PrimitiveConstraint c : listOfC)
		    c.include(store);

		store.addChanged(this);
		store.countConstraint(listOfC.length);
	}

        @Override
        public void include(Store store) {
		for (PrimitiveConstraint c : listOfC)
		    c.include(store);
	}

	@Override
	public void notConsistency(Store store) {

		int numberCertainNotSat = 0;
		int numberCertainSat = 0;
		int j = 0;
		int i = 0;

		while (numberCertainNotSat == 0 && i < listOfC.length) {
			if (listOfC[i].notSatisfied())
				numberCertainNotSat++;
			else {
				if (listOfC[i].satisfied())
					numberCertainSat++;
				else
					j = i;
			}
			i++;
		}

		if (numberCertainNotSat == 0) {
			if (numberCertainSat == listOfC.length - 1) {
				listOfC[j].notConsistency(store);
			} else if (numberCertainSat == listOfC.length)
		    	throw Store.failException;
		}
	}

	@Override
	public void queueVariable(int level, Var V) {
		propagation = true;
	}

	@Override
	public boolean notSatisfied() {
		boolean notSat = false;

		int i = 0;
		while (!notSat && i < listOfC.length) {
			notSat = notSat || listOfC[i].notSatisfied();
			i++;
		}
		return notSat;
	}

	@Override
	public void removeConstraint() {

		for (Constraint cc : listOfC)
			for (Var V : cc.arguments())
				V.removeConstraint(this);

	}

	@Override
	public boolean satisfied() {
		boolean sat = true;

		int i = 0;
		while (sat && i < listOfC.length) {
			sat = sat && listOfC[i].satisfied();
			i++;
		}
		return sat;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : And(");
		
		for (int i = 0; i < listOfC.length; i++) {
			result.append( listOfC[i] );
			if (i == listOfC.length - 1)
				result.append(",");
		}
		return result.toString();
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			for (Constraint c : listOfC) c.increaseWeight();
		}
	}
}
