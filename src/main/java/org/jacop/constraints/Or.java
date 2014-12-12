/**
 *  Or.java 
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

import org.jacop.core.Domain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.util.SimpleHashSet;

/**
 * Constraint c1 \/ c2 \/ ... \/ cn.
 * 
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Or extends PrimitiveConstraint {

	static int IdNumber = 1;

	/**
	 * It specifies a list of constraints from which one constraint must be satisfied.
	 */
	public PrimitiveConstraint listOfC[];

	/**
	 * It specifies if during the consistency execution a propagation has occurred.
	 */
	private boolean propagation;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"listOfC"};

	/**
	 * It constructs Or constraint.
	 * @param listOfC list of primitive constraints which at least one of them has to be satisfied.
	 */
	public Or(PrimitiveConstraint[] listOfC) {
		
		assert (listOfC != null) : "List of constraints is null";
		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.listOfC = new PrimitiveConstraint[listOfC.length];
		
		for (int i = 0; i < listOfC.length; i++) {
			assert (listOfC[i] != null) : i + "-th element of list of constraints is null";
			
			this.numberArgs += listOfC[i].numberArgs();
			this.listOfC[i] = listOfC[i];
		}
		
	}

	/**
	 * It constructs Or constraint.
	 * @param listOfC list of primitive constraints which at least one of them has to be satisfied.
	 */
	public Or(ArrayList<PrimitiveConstraint> listOfC) {
		
		this(listOfC.toArray(new PrimitiveConstraint[listOfC.size()]));
		
	}

	/**
	 * It constructs an Or constraint, at least one constraint has to be satisfied.
	 * @param c1 the first constraint which can be satisfied.
	 * @param c2 the second constraint which can be satisfied.
	 */
	public Or(PrimitiveConstraint c1, PrimitiveConstraint c2) {
		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.listOfC = new PrimitiveConstraint[2];
		this.numberArgs += c1.numberArgs();
		this.listOfC[0] = c1;
		this.numberArgs += c2.numberArgs();
		this.listOfC[1] = c2;

	}


	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>();

		for (Constraint cc : listOfC)
			variables.addAll(cc.arguments());

		return variables;
	}

	@Override
	public void consistency(Store store) {

		//@todo, why so much work? 
		// search for the first one which returns false for notSatisfied() call
		// use circular buffer approach to remember the last notSatisfied()== false to start checking from this one.  
		int numberSat = 0;
		int numberNotSat = 0;
		int j = 0;

		int i = 0;
		while (numberSat == 0 && i < listOfC.length) {
			if (listOfC[i].satisfied())
				numberSat++;
			else {
				if (listOfC[i].notSatisfied())
					numberNotSat++;
				else
					j = i;
			}
			i++;
		}

		if (numberSat == 0) {
		
			if (numberNotSat == listOfC.length - 1)
				listOfC[j].consistency(store);
			else if (numberNotSat == listOfC.length)
		    	throw Store.failException;
		
		}
		
	}

	@Override
	public int getNestedPruningEvent(Var var, boolean mode) {

		return getConsistencyPruningEvent(var);

	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
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
			
		// If notConsistency function mode
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
			for (Var V : listOfC[i].arguments())
				variables.add(V);

		while (!variables.isEmpty()) {
			Var V = variables.removeFirst();
			V.putModelConstraint(this, getConsistencyPruningEvent(V));
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
	public void queueVariable(int level, Var V) {
		propagation = true;
	}

	@Override
	public void notConsistency(Store store) {

		// From De'Morgan laws not(A or B) == not A and not B
		do {

			propagation = false;
			for (int i = 0; i < listOfC.length; i++)
				listOfC[i].notConsistency(store);

		} while (propagation);
		
	}

	@Override
	public boolean notSatisfied() {
		boolean notSat = true;

		int i = 0;
		while (notSat && i < listOfC.length) {
			notSat = notSat && listOfC[i].notSatisfied();
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
		boolean sat = false;

		int i = 0;
		while (!sat && i < listOfC.length) {
			sat = sat || listOfC[i].satisfied();
			i++;
		}
		return sat;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		result.append(" : Or( ");
		for (int i = 0; i < listOfC.length; i++) {
			result.append( listOfC[i] );
			if (i == listOfC.length - 1)
				result.append("),");
			else
				result.append(", ");
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
