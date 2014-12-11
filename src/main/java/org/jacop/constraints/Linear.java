/**
 *  Linear.java 
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * Linear constraint implements the weighted summation over several
 * variables . It provides the weighted sum from all variables on the list.
 * The weights are integers.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public class Linear extends PrimitiveConstraint {
    Store store;
	static int counter = 1;

    /**
     * Defines relations
     */
    final static byte eq=0, lt=1, le=2, ne=3, gt=4, ge=5;

    /**
     * Defines negated relations
     */
    final static byte[] negRel= {ne, //eq=0, 
				 ge, //lt=1, 
				 gt, //le=2, 
				 eq, //ne=3, 
				 le, //gt=4, 
				 lt  //ge=5;
    };

    /**
     * It specifies what relations is used by this constraint
     */

    public byte relationType;

	/**
	 * It specifies a list of variables being summed.
	 */
	public IntVar list[];

	/**
	 * It specifies a list of weights associated with the variables being summed.
	 */
	public int weights[];

	/**
	 * It specifies variable for the overall sum. 
	 */
	public int sum;

	int lMin;

	int lMax;

	int[] lMinArray;

	int[] lMaxArray;

	HashMap<Var, Integer> positionMaping;

	boolean backtrackHasOccured = false;

	/**
	 * The sum of grounded variables.
	 */
	private TimeStamp<Integer> sumGrounded;

	/**
	 * The position for the next grounded variable.
	 */
	private TimeStamp<Integer> nextGroundedPosition;	

    boolean reified = true;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list", "weights", "sum"};

	/**
	 * @param list
	 * @param weights
	 * @param sum
	 */
    public Linear(Store store, IntVar[] list, int[] weights, String rel, int sum) {

	commonInitialization(store, list, weights, sum);
	this.relationType = relation(rel);

	}
	
    private void commonInitialization(Store store, IntVar[] list, int[] weights, int sum) {
	this.store=store;
		queueIndex = 1;

		assert ( list.length == weights.length ) : "\nLength of two vectors different in Linear";

		numberArgs = (short) (list.length + 1);

		numberId = counter++;

		this.sum = sum;

		HashMap<IntVar, Integer> parameters = new HashMap<IntVar, Integer>();

		for (int i = 0; i < list.length; i++) {

		    assert (list[i] != null) : i + "-th element of list in Linear constraint is null";
			
		    if (weights[i] != 0) {
			if (list[i].singleton()) 
			    this.sum -= list[i].value() * weights[i];
			else
			    if (parameters.get(list[i]) != null) {
				// variable ordered in the scope of the Linear constraint.
				Integer coeff = parameters.get(list[i]);
				Integer sumOfCoeff = coeff + weights[i];
				parameters.put(list[i], sumOfCoeff);
			    }
			    else
				parameters.put(list[i], weights[i]);

		    }
		}

		this.list = new IntVar[parameters.size()];
		this.weights = new int[parameters.size()];

		int i = 0;
		for (IntVar var : parameters.keySet()) {
			this.list[i] = var;
			this.weights[i] = parameters.get(var);
			i++;
		}

		sumGrounded = new TimeStamp<Integer>(store, 0);
		nextGroundedPosition = new TimeStamp<Integer>(store, 0);
		int capacity = list.length*4/3+1;
		if (capacity < 16)
		    capacity = 16;
		positionMaping = new HashMap<Var, Integer>(capacity);

		store.registerRemoveLevelLateListener(this);

		lMinArray = new int[list.length];
		lMaxArray = new int[list.length];
		lMin = 0;
		lMax = 0;

		recomputeBounds();

		for (int j = 0; j < this.list.length; j++) {

			assert (positionMaping.get(this.list[j]) == null) : "The variable occurs twice in the list, not able to make a maping from the variable to its list index.";

			positionMaping.put(this.list[j], j);
			queueVariable(store.level, this.list[j]);

			
		}

		checkForOverflow();

	}

	/**
	 * It constructs the constraint Linear. 
	 * @param variables variables which are being multiplied by weights.
	 * @param weights weight for each variable.
	 * @param sum variable containing the sum of weighted variables.
	 */
    public Linear(Store store, ArrayList<? extends IntVar> variables,
			ArrayList<Integer> weights, String rel, int sum) {

		int[] w = new int[weights.size()];
		for (int i = 0; i < weights.size(); i++)
			w[i] = weights.get(i);
		
		commonInitialization(store, variables.toArray(new IntVar[variables.size()]),
							 w,
							 sum);
		this.relationType = relation(rel);
	}


	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(list.length + 1);

		for (Var v : list)
			variables.add(v);

		return variables;
	}


	@Override
	public void removeLevelLate(int level) {

	       backtrackHasOccured = true;

	}


	@Override
	public void consistency(Store store) {

	    pruneRelation(store, relationType);

	    if (relationType != eq)
	    	if (satisfied())
	    	    removeConstraint();
	}

	@Override
	public void notConsistency(Store store) {

	    pruneRelation(store, negRel[relationType]);

	    if (negRel[relationType] != eq)
	    	if (notSatisfied()) 
	    	    removeConstraint();
		
	}

    private void pruneRelation(Store store, byte rel) {

	 if (backtrackHasOccured) {

            backtrackHasOccured = false;

	    recomputeBounds();
	 }

	if (entailed(negRel[rel]))
	    throw Store.failException;

	do {

	    store.propagationHasOccurred = false;

	    int min = sum - lMax;
	    int max = sum - lMin;

	    int pointer1 = nextGroundedPosition.value();

	    for (int i = pointer1; i < list.length; i++) {

		IntVar v = list[i];

		float d1, d2;
		int divMin, divMax;

		switch (rel) {
		case eq : //============================================= 
		    if ((lMaxArray[i] > max + lMinArray[i]) || (lMinArray[i] < min + lMaxArray[i])) {

			d1 = ((float)(min + lMaxArray[i]) / weights[i]);
			d2 = ((float)(max + lMinArray[i]) / weights[i]);

			if (d1 <= d2) {
			    divMin = (int)( Math.round( Math.ceil ( d1 ) ) );
			    divMax = (int)( Math.round( Math.floor( d2 ) ) );
			}
			else {
			    divMin = (int)( Math.round( Math.ceil ( d2 ) ) );
			    divMax = (int)( Math.round( Math.floor( d1 ) ) );
			}

			if (divMin > divMax) 
			    throw Store.failException;

			v.domain.in(store.level, v, divMin, divMax);
		    }
		    break;
		case lt : //=============================================

		    if (lMaxArray[i] >= max + lMinArray[i]) {  // based on "Bounds Consistency Techniques for Long Linear Constraints", W. Harvey and J. Schimpf

			d1 = ((float)(min + lMaxArray[i]) / weights[i]);
			d2 = ((float)(max + lMinArray[i]) / weights[i]);

			if (weights[i] < 0) {
			    if (d1 <= d2) 
				divMin = (int)( Math.round( Math.floor ( d1 ) ) );
			    else
				divMin = (int)( Math.round( Math.floor( d2 ) ) );

			    v.domain.inMin(store.level, v, divMin + 1);
			}
			else {
			    if (d1 <= d2) 
				divMax = (int)( Math.round( Math.ceil( d2 ) ) );
			    else 
				divMax = (int)( Math.round( Math.ceil( d1 ) ) );

			    v.domain.inMax(store.level, v, divMax - 1);
			}
		    }
		    break;
		case le : //=============================================

		    if (lMaxArray[i] > max + lMinArray[i]) {  // based on "Bounds Consistency Techniques for Long Linear Constraints", W. Harvey and J. Schimpf

			d1 = ((float)(min + lMaxArray[i]) / weights[i]);
			d2 = ((float)(max + lMinArray[i]) / weights[i]);

			if (weights[i] < 0) {
			    if (d1 <= d2) 
				divMin = (int)( Math.round( Math.ceil ( d1 ) ) );
			    else
				divMin = (int)( Math.round( Math.ceil ( d2 ) ) );

			    v.domain.inMin(store.level, v, divMin);
			}
			else {
			    if (d1 <= d2)
				divMax = (int)( Math.round( Math.floor( d2 ) ) );
			    else
				divMax = (int)( Math.round( Math.floor( d1 ) ) );

			    v.domain.inMax(store.level, v, divMax);
			}
		    }
		    break;
		case ne : //=============================================

		    d1 = ((float)(min + lMaxArray[i]) / weights[i]);
		    d2 = ((float)(max + lMinArray[i]) / weights[i]);

		    if (d1 <= d2) {
			divMin = (int)( Math.round( Math.ceil ( d1 ) ) );
			divMax = (int)( Math.round( Math.floor( d2 ) ) );
		    }
		    else {
			divMin = (int)( Math.round( Math.ceil ( d2 ) ) );
			divMax = (int)( Math.round( Math.floor( d1 ) ) );
		    }

		    if ( divMin == divMax) 
			v.domain.inComplement(store.level, v, divMin);
		    break;
		case gt : //=============================================

		    if (lMinArray[i] <= min + lMaxArray[i]) { // based on "Bounds Consistency Techniques for Long Linear Constraints", W. Harvey and J. Schimpf


			d1 = ((float)(min + lMaxArray[i]) / weights[i]);
			d2 = ((float)(max + lMinArray[i]) / weights[i]);

			if (weights[i] < 0) {
			    if (d1 <= d2) 
				divMax = (int)( Math.round( Math.ceil( d2 ) ) );
			    else
				divMax = (int)( Math.round( Math.ceil( d1 ) ) );

			    v.domain.inMax(store.level, v, divMax - 1);
			}
			else {
			    if (d1 <= d2)
				divMin = (int)( Math.round( Math.floor ( d1 ) ) );
			    else
				divMin = (int)( Math.round( Math.floor( d2 ) ) );

			    v.domain.inMin(store.level, v, divMin + 1);
			}
		    }
		    break;
		case ge : //=============================================

		    if (lMinArray[i] < min + lMaxArray[i]) { // based on "Bounds Consistency Techniques for Long Linear Constraints", W. Harvey and J. Schimpf

			d1 = ((float)(min + lMaxArray[i]) / weights[i]);
			d2 = ((float)(max + lMinArray[i]) / weights[i]);

			if (weights[i] < 0) {
			    if (d1 <= d2)
				divMax = (int)( Math.round( Math.floor( d2 ) ) );
			    else
				divMax = (int)( Math.round( Math.floor( d1 ) ) );

			    v.domain.inMax(store.level, v, divMax);
			}
			else {
			    if (d1 <= d2)
				divMin = (int)( Math.round( Math.ceil ( d1 ) ) );
			    else
				divMin = (int)( Math.round( Math.ceil ( d2 ) ) );

			    v.domain.inMin(store.level, v, divMin);
			}
		    }
		    break;
		}
	    }

	} while (store.propagationHasOccurred);

	if (entailed(negRel[rel]))
	    throw Store.failException;

    }

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return IntDomain.BOUND;
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
			return IntDomain.BOUND;
		}

		// If notConsistency function mode
		else {
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.BOUND;
		}

	}

	@Override
	public int getNotConsistencyPruningEvent(Var var) {

		// If notConsistency function mode
		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return IntDomain.BOUND;
		
	}

	@Override
	public void impose(Store store) {

	    if (list == null)
		return;

	    reified = false;

	    for (Var V : list)
		V.putModelConstraint(this, getConsistencyPruningEvent(V));

	    store.addChanged(this);
	    store.countConstraint();
	}


	@Override
	public void queueVariable(int level, Var var) {

		if (var.singleton()) {

			int pointer = nextGroundedPosition.value();

			int i = positionMaping.get(var);

			if (i < pointer)
				return;

			int value = ((IntVar)var).min();

			int sumJustGrounded = 0;

			int weightGrounded = weights[i];

			if (pointer < i) {
				IntVar grounded = list[i];
				list[i] = list[pointer];
				list[pointer] = grounded;

				positionMaping.put(list[i], i);
				positionMaping.put(list[pointer], pointer);

				int temp = lMinArray[i];
				lMinArray[i] = lMinArray[pointer];
				lMinArray[pointer] = temp;

				temp = lMaxArray[i];
				lMaxArray[i] = lMaxArray[pointer];
				lMaxArray[pointer] = temp;

				weights[i] = weights[pointer];
				weights[pointer] = weightGrounded;

			}

			sumJustGrounded += value * weightGrounded;

			sumGrounded.update( sumGrounded.value() + sumJustGrounded );

			lMin += sumJustGrounded - lMinArray[pointer];
			lMax += sumJustGrounded - lMaxArray[pointer];
			lMinArray[pointer] = sumJustGrounded;
			lMaxArray[pointer] = sumJustGrounded;

			pointer++;
			nextGroundedPosition.update(pointer);

		}

		else {

			int i = positionMaping.get(var);

			int mul1 = ((IntVar)var).min() * weights[i];
			int mul2 = ((IntVar)var).max() * weights[i];

			if (mul1 <= mul2) {

			    lMin += mul1 - lMinArray[i];
			    lMinArray[i] = mul1;

			    lMax += mul2 - lMaxArray[i];
			    lMaxArray[i] = mul2;

			}
			else {

			    lMin += mul2 - lMinArray[i];
			    lMinArray[i] = mul2;

			    lMax += mul1 - lMaxArray[i];
			    lMaxArray[i] = mul1;

			}

		}

		// FailException cannot be thrown here since it will not be cought
		// in a situation when a DepthFirstSearch is defining a choice-point :(
		// In such situations the variable might be queued but there is not catching
		// of FailException.
		/*
		if (!reified) {
		    if (backtrackHasOccured) {
		    
			backtrackHasOccured = false;

			recomputeBounds();
		    }
		    
		    if (entailed(negRel[relationType])) 
		    	throw Store.failException;
		}
		*/
	}

	@Override
	public void removeConstraint() {
		for (Var v : list)
			v.removeConstraint(this);
	}

    @Override
    public boolean satisfied() {

	if (reified && backtrackHasOccured) {

	    backtrackHasOccured = false;

	    recomputeBounds();
	}

	return entailed(relationType);

    }

    @Override
    public boolean notSatisfied() {

	if (reified && backtrackHasOccured) {

	    backtrackHasOccured = false;

	    recomputeBounds();
	}

	return entailed(negRel[relationType]);

    }

    private boolean entailed(byte rel) {
	    
	switch (rel) {
	case eq : 
	    if (lMin == lMax && lMin == sum)
		return true;
	    break;
	case lt : 
	    if (lMax < sum)
		return true;
	    break;
	case le : 
	    if (lMax <= sum)
		return true;
	    break;
	case ne : 
	    if (lMin > sum || lMax < sum)
		return true;
	    break;
	case gt : 
	    if (lMin > sum)
		return true;
	    break;
	case ge : 
	    if (lMin >= sum)
		return true;
	    break;
	}

	return false;
    }

    void recomputeBounds() {

	int pointer = nextGroundedPosition.value();

	lMin = sumGrounded.value();
	lMax = lMin;

	for (int i = pointer; i < list.length; i++) {

	    IntDomain currentDomain = list[i].domain;

	    assert (!currentDomain.singleton()) : "Singletons should not occur in this part of the array";

	    int mul1 = currentDomain.min() * weights[i];
	    int mul2 = currentDomain.max() * weights[i];
				
	    if (mul1 <= mul2) {
		lMin += mul1;
		lMinArray[i] = mul1;

		lMax += mul2;
		lMaxArray[i] = mul2;
	    }
	    else {

		lMin += mul2;
		lMinArray[i] = mul2;

		lMax += mul1;
		lMaxArray[i] = mul1;
	    }
	}
    }

    void checkForOverflow() {

	int sumMin=0, sumMax=0;
	for (int i=0; i<list.length; i++) {
	    int n1 = IntDomain.multiply(list[i].min(), weights[i]);
	    int n2 = IntDomain.multiply(list[i].max(), weights[i]);

	    if (n1 <= n2) {
		sumMin = add(sumMin, n1);
		sumMax = add(sumMax, n2);
	    }
	    else {
		sumMin = add(sumMin, n2);
		sumMax = add(sumMax, n1);
	    }
	}
    }

    public byte relation(String r) {
	if (r.equals("==")) 
	    return eq;
	else if (r.equals("=")) 
	    return eq;
	else if (r.equals("<"))
	    return lt;
	else if (r.equals("<="))
	    return le;
	else if (r.equals("=<"))
	    return le;
	else if (r.equals("!="))
	    return ne;
	else if (r.equals(">"))
	    return gt;
	else if (r.equals(">="))
	    return ge;
	else if (r.equals("=>"))
	    return ge;
	else {
	    System.err.println ("Wrong relation symbol in Linear constraint " + r + "; assumed ==");
	    return eq;
	}
    }

    public String rel2String() {
	switch (relationType) {
	case eq : return "==";
	case lt : return "<";
	case le : return "<=";
	case ne : return "!=";
	case gt : return ">";
	case ge : return ">=";
	}

	return "?";
    }


	@Override
	public String toString() {

		StringBuffer result = new StringBuffer( id() );
		result.append(" : Linear( [ ");

		for (int i = 0; i < list.length; i++) {
			result.append(list[i]);
			if (i < list.length - 1)
				result.append(", ");
		}
		result.append("], [");

		for (int i = 0; i < weights.length; i++) {
			result.append( weights[i] );
			if (i < weights.length - 1)
				result.append( ", " );
		}

		result.append( "], ").append(rel2String()).append(", ").append(sum).append( " )" );

		return result.toString();

	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			for (Var v : list) v.weight++;
		}
	}
}
