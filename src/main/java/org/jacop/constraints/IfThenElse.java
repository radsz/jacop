/**
 *  IfThenElse.java 
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

/**
 * Constraint if constraint1 then constraint2 else constraint3
 *  * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class IfThenElse extends PrimitiveConstraint {

	static int counter = 1;

	/**
	 * It specifies constraint condC in the IfThenElse constraint. 
	 */
	public PrimitiveConstraint condC;

	/**
	 * It specifies constraint condC in the IfThenElse constraint. 
	 */
	public PrimitiveConstraint thenC;

	/**
	 * It specifies constraint elseC in the IfThenElse constraint. 
	 */
	public PrimitiveConstraint elseC;

	// imposed variable to manifest that constraint has been imposed (top-level)
	// constraint
	boolean imposed = false;

	Store store;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"condC", "thenC", "elseC"};

	/**
	 * It creates ifthenelse constraint.
	 * @param condC the condition of the constraint.
	 * @param thenC the condition which must be true if the constraint condition is true.
	 * @param elseC the condition which must be true if the constraint condition is not true.
	 */
	// Constructors
	public IfThenElse(PrimitiveConstraint condC, 
					  PrimitiveConstraint thenC,
					  PrimitiveConstraint elseC) {

		assert (condC != null) : "Constraint cond is null";
		assert (thenC != null) : "Constraint then is null";
		assert (elseC != null) : "Constraint elseC is null";

		numberId = counter++;
		numberArgs = (short) (condC.numberArgs + thenC.numberArgs + elseC.numberArgs);
		
		this.condC = condC;
		this.thenC = thenC;
		this.elseC = elseC;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(1);

		for (Var V : condC.arguments())
			variables.add(V);

		for (Var V : thenC.arguments())
			variables.add(V);

		for (Var V : elseC.arguments())
			variables.add(V);

		return variables;
	}

	@Override
	public void consistency(Store store) {

		if (condC.satisfied())
			thenC.consistency(store);
		else if (condC.notSatisfied())
			elseC.consistency(store);

		if (imposed) {

		    if (thenC.notSatisfied()) {
			condC.notConsistency(store);
			elseC.consistency(store);
		    }

		    if (elseC.notSatisfied()) {
			condC.consistency(store);
			thenC.consistency(store);
		    }
		}

		// if (imposed) {
			
		// 	if (thenC.notSatisfied())
		// 		condC.notConsistency(store);

		// 	if (elseC.notSatisfied())
		// 		condC.consistency(store);
			
		// }

	}

	@Override
	public boolean notSatisfied() {
		return (condC.satisfied() && thenC.notSatisfied())
				|| (condC.notSatisfied() && elseC.notSatisfied());
	}

	@Override
	public void notConsistency(Store store) {

		if (condC.notSatisfied())
			elseC.notConsistency(store);

		if (condC.satisfied())
			thenC.notConsistency(store);

	}

	@Override
	public int getNestedPruningEvent(Var var, boolean mode) {

		// If consistency function mode
		if (mode) {
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
		}
		// If notConsistency function mode
		else {
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
		}

		int eventAcross = -1;

		if (condC.arguments().contains(var)) {
			int event = condC.getNestedPruningEvent(var, true);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (condC.arguments().contains(var)) {
			int event = condC.getNestedPruningEvent(var, false);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (thenC.arguments().contains(var)) {
			int event = thenC.getNestedPruningEvent(var, true);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (thenC.arguments().contains(var)) {
			int event = thenC.getNestedPruningEvent(var, false);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (elseC.arguments().contains(var)) {
			int event = elseC.getNestedPruningEvent(var, true);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (elseC.arguments().contains(var)) {
			int event = elseC.getNestedPruningEvent(var, false);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (eventAcross == -1)
			return Domain.NONE;
		else
			return eventAcross;

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

			if (condC.arguments().contains(var)) {
				int event = condC.getNestedPruningEvent(var, true);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (condC.arguments().contains(var)) {
				int event = condC.getNestedPruningEvent(var, false);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (thenC.arguments().contains(var)) {
				int event = thenC.getNestedPruningEvent(var, true);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (thenC.arguments().contains(var)) {
				int event = thenC.getNestedPruningEvent(var, false);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (elseC.arguments().contains(var)) {
				int event = elseC.getNestedPruningEvent(var, true);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (elseC.arguments().contains(var)) {
				int event = elseC.getNestedPruningEvent(var, false);
				if (event > eventAcross)
					eventAcross = event;
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

		if (condC.arguments().contains(var)) {
			int event = condC.getNestedPruningEvent(var, true);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (condC.arguments().contains(var)) {
			int event = condC.getNestedPruningEvent(var, false);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (thenC.arguments().contains(var)) {
			int event = thenC.getNestedPruningEvent(var, true);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (thenC.arguments().contains(var)) {
			int event = thenC.getNestedPruningEvent(var, false);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (elseC.arguments().contains(var)) {
			int event = elseC.getNestedPruningEvent(var, true);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (elseC.arguments().contains(var)) {
			int event = elseC.getNestedPruningEvent(var, false);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (eventAcross == -1)
			return Domain.NONE;
		else
			return eventAcross;

	}

	@Override
	public void impose(Store store) {

		this.store = store;

		for (Var var : condC.arguments())
			var.putModelConstraint(this, getConsistencyPruningEvent(var));

		for (Var var : thenC.arguments())
			var.putModelConstraint(this, getConsistencyPruningEvent(var));

		for (Var var : elseC.arguments())
			var.putModelConstraint(this, getConsistencyPruningEvent(var));

		store.addChanged(this);
		store.countConstraint();

		condC.include(store);
		thenC.include(store);
		elseC.include(store);

		imposed = true;
	}

	@Override
	public void include(Store store) {
	    condC.include(store);
	    thenC.include(store);
	    elseC.include(store);
	}

	@Override
	public void removeConstraint() {

		for (Var var : condC.arguments())
			var.removeConstraint(this);

		for (Var var : thenC.arguments())
			var.removeConstraint(this);

		for (Var var : elseC.arguments())
			var.removeConstraint(this);

	}

	@Override
	public boolean satisfied() {

		if (imposed) {

			if (condC.satisfied()) {
				this.removeConstraint();
				store.impose(thenC);
				return false;
			}

			if (condC.notSatisfied()) {
				this.removeConstraint();
				store.impose(elseC);
				return false;
			}

		}

		return (condC.satisfied() && thenC.satisfied())
				|| (condC.notSatisfied() && elseC.satisfied());

	}

	@Override
	public String toString() {

		StringBuffer result = new StringBuffer( id() );
		result.append(" : IfThenElse(").append( condC ).append( ", " );
		result.append(thenC).append( ", " ).append( elseC ).append( " )" );
		
		return result.toString();
		
	}

    @Override
	public void increaseWeight() {
		if (increaseWeight) {
			condC.increaseWeight();
			thenC.increaseWeight();
			elseC.increaseWeight();
			}
	}

}
