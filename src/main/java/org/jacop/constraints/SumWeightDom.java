/**
 *  SumWeightDom.java
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
import java.util.LinkedHashSet;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;

/**
 * SumWeightDom constraint implements the weighted summation over several
 * variables . It provides the weighted sum from all variables on the list.
 * The weights are integers.
 *
 * The complexity of domain consistency is exponential in worst case. Use it carefully!
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public class SumWeightDom extends Constraint {

    static int counter = 1;

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

    /**
     * It specifies variable queue of grounded varibales since last run. 
     */
    LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();


    IntDomain[] lArray;

    HashMap<Var, Integer> positionMaping;

    boolean backtrackHasOccured = false;

    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"list", "weights", "sum"};

    /**
     * @param list  array of variables to be summed up
     * @param weights variables' weights
     * @param sum  resulting sum
     */
    public SumWeightDom(IntVar[] list, int[] weights, int sum) {

	commonInitialization(list, weights, sum);
		
    }
	
    /**
     * @param list array of variables to be summed up
     * @param weights variables' weights
     * @param sum resulting sum
     */
    public SumWeightDom(IntVar[] list, int[] weights, IntVar sum) {

	IntVar[] l = new IntVar[list.length + 1];	
	System.arraycopy(list, 0, l, 0, list.length);
	l[list.length] = sum;

	int[] w = new int[weights.length + 1];
	System.arraycopy(weights, 0, w, 0, weights.length);
	w[weights.length] = -1;

	commonInitialization(l, w, 0);
		
    }
	
    private void commonInitialization(IntVar[] list, int[] weights, int sum) {
		
	queueIndex = 4;

	assert ( list.length == weights.length ) : "\nLength of two vectors different in SumWeightDom";

	numberArgs = (short) (list.length + 1);

	numberId = counter++;

	this.sum = sum;

	HashMap<IntVar, Integer> parameters = new HashMap<IntVar, Integer>();

	for (int i = 0; i < list.length; i++) {

	    assert (list[i] != null) : i + "-th element of list in SumWeightDom constraint is null";
			
	    if (parameters.get(list[i]) != null) {
		// variable ordered in the scope of the Sum Weight constraint.
		Integer coeff = parameters.get(list[i]);
		Integer sumOfCoeff = coeff + weights[i];
		parameters.put(list[i], sumOfCoeff);
	    }
	    else
		parameters.put(list[i], weights[i]);

	}

	this.list = new IntVar[parameters.size()];
	this.weights = new int[parameters.size()];

	int i = 0;
	for (IntVar var : parameters.keySet()) {
	    this.list[i] = var;
	    this.weights[i] = parameters.get(var);
	    i++;
	}

	checkForOverflow();
    }

    /**
     * It constructs the constraint SumWeightDom.
     * @param variables variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted variables.
     */
    public SumWeightDom(ArrayList<? extends IntVar> variables,
                        ArrayList<Integer> weights, int sum) {

	int[] w = new int[weights.size()];
	for (int i = 0; i < weights.size(); i++)
	    w[i] = weights.get(i);
		
	commonInitialization(variables.toArray(new IntVar[variables.size()]),
			     w,
			     sum);

    }

    /**
     * It constructs the constraint SumWeightDom.
     * @param variables variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted variables.
     */
    public SumWeightDom(ArrayList<? extends IntVar> variables,
                        ArrayList<Integer> weights, IntVar sum) {

	IntVar[] l = new IntVar[variables.size() + 1];	
	System.arraycopy(variables.toArray(new IntVar[variables.size()]), 0, l, 0, variables.size());
	l[variables.size()] = sum;

	int[] w = new int[weights.size() + 1];
	for (int i = 0; i < weights.size(); i++)
	    w[i] = weights.get(i);
	w[weights.size()] = -1;
		
	commonInitialization(l, w, 0);

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

	variableQueue = new LinkedHashSet<IntVar>();

    }


    /**
     * The sum of grounded variables.
     */
    private TimeStamp<Integer> sumGrounded;

    /**
     * The position for the next grounded variable.
     */
    private TimeStamp<Integer> nextGroundedPosition;	

    @Override
	public void consistency(Store store) {

	if (backtrackHasOccured) {

	    backtrackHasOccured = false;

	    int pointer = nextGroundedPosition.value();

	    // update lArray domains after backtrack
	    for (int i = pointer; i < list.length; i++) {

		IntDomain currentDomain = list[i].domain;

		assert (!currentDomain.singleton()) : "Singletons should not occur in this part of the array";

		lArray[i] = multiplyDom(currentDomain, weights[i]);

	    }

	}

	do {
			
	    store.propagationHasOccurred = false;

	    int pointer = nextGroundedPosition.value();

	    LinkedHashSet<IntVar> fdvs = variableQueue;
	    variableQueue = new LinkedHashSet<IntVar>();

	    // check recently grounded variables
	    for (IntVar q : fdvs) {

		int i = positionMaping.get(q);

		if (weights[i] == 0)
		    continue;

		int valGround = sum - sumGrounded.value() + q.min()*weights[i];
		IntDomain vDom = new IntervalDomain(valGround, valGround);

		for (int j=pointer; j<list.length; j++)
			vDom = subtractDom(vDom, lArray[j]);

		vDom = divDom(vDom, weights[i]);

		q.domain.in(store.level, q, vDom);

	    }

	    // check still not ground variables
	    for (int i = pointer; i < list.length; i++) {
			
		if (weights[i] == 0)
		    continue;

		IntVar v = list[i];

		int pointer1 = nextGroundedPosition.value();

		int sGround = sumGrounded.value();
		IntDomain vDom = new IntervalDomain(sum-sGround, sum-sGround);
		for (int j=pointer1; j<list.length; j++)
		    if (j != i) 
			vDom = subtractDom(vDom, lArray[j]);

		vDom = divDom(vDom, weights[i]);

		v.domain.in(store.level, v, vDom);

	    }
		
	} while (store.propagationHasOccurred);
		
    }

    @Override
	public int getConsistencyPruningEvent(Var var) {

	// If consistency function mode
	if (consistencyPruningEvents != null) {
	    Integer possibleEvent = consistencyPruningEvents.get(var);
	    if (possibleEvent != null)
		return possibleEvent;
	}
	return IntDomain.ANY;
    }

    @Override
	public void impose(Store store) {

	sumGrounded = new TimeStamp<Integer>(store, 0);
	nextGroundedPosition = new TimeStamp<Integer>(store, 0);
	positionMaping = new HashMap<Var, Integer>();

	store.registerRemoveLevelLateListener(this);

	for (Var V : list)
	    V.putModelConstraint(this, getConsistencyPruningEvent(V));

	lArray = new IntDomain[list.length];

	for (int i = 0; i < list.length; i++) {

	    assert (positionMaping.get(list[i]) == null) : "The variable occurs twice in the list, not able to make a maping from the variable to its list index.";

	    positionMaping.put(list[i], new Integer(i));
	    queueVariable(store.level, list[i]);
	}

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

		IntDomain temp = lArray[i];
		lArray[i] = lArray[pointer];
		lArray[pointer] = temp;


		weights[i] = weights[pointer];
		weights[pointer] = weightGrounded;

	    }

	    sumJustGrounded += value * weightGrounded;

	    sumGrounded.update( sumGrounded.value() + sumJustGrounded );

	    lArray[pointer] = new IntervalDomain(sumJustGrounded, sumJustGrounded);

	    variableQueue.add((IntVar)var);

	    pointer++;
	    nextGroundedPosition.update(pointer);

	}

	else {

	    int i = positionMaping.get(var);

	    lArray[i] = multiplyDom(((IntVar)var).dom(), weights[i]);

	}

    }

    @Override
	public void removeConstraint() {

	for (Var v : list)
	    v.removeConstraint(this);
    }

    @Override
	public boolean satisfied() {

        return nextGroundedPosition.value() == list.length && sumGrounded.value() == sum;

    }

    @Override
	public String toString() {

	StringBuffer result = new StringBuffer( id() );
	result.append(" : sumWeightDom( [ ");

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

	result.append( "], ").append(sum).append( " )" );

	return result.toString();

    }

    @Override
	public void increaseWeight() {
	if (increaseWeight) {

	    for (Var v : list) v.weight++;
	}
    }

    IntDomain multiplyDom(IntDomain d, int c) {
	IntDomain temp;
	// System.out.println (d + " * " + c);

	if (c == 1) 
	    return d;
	else if ( c == -1) temp = invertDom(d);
	else {
	    temp = new IntervalDomain();
	    for (IntervalEnumeration e1 = d.intervalEnumeration(); e1.hasMoreElements();) {
		Interval i = e1.nextElement();

		IntervalDomain mulDom = new IntervalDomain();
		if ( c > 0) 
		    for (int k=i.min(); k<=i.max(); k++) {
		    	// mulDom.addDom(new IntervalDomain(k*c, k*c));
		    	mulDom.unionAdapt(k*c, k*c);
		    }
		else // c < 0
		    for (int k=i.max(); k>=i.min(); k--) {	
			// mulDom.addDom(new IntervalDomain(k*c, k*c));
			mulDom.unionAdapt(k*c, k*c);
		    }

		// temp.addDom(mulDom);
		temp.unionAdapt(mulDom);

	    }
	}

	// System.out.println ("result* = " + temp);

	return temp;

    }

    IntDomain invertDom(IntDomain d) {
	IntervalDomain temp = new IntervalDomain();

	if (d.domainID() == IntDomain.IntervalDomainID) {
	    int n = ((IntervalDomain)d).size;
	    temp.size = n;
	    temp.intervals = new Interval[n];
	    int k=0;
	    for (int i = n-1; i >= 0; i--) {
		Interval e = ((IntervalDomain)d).intervals[i];
		temp.intervals[k++] = new Interval(-e.max(), -e.min());
	    }
	}
	else 
	    for (IntervalEnumeration e = d.intervalEnumeration(); e.hasMoreElements();) {
		Interval i = e.nextElement();
		temp.addDom(new IntervalDomain(-i.max(), -i.min()));
	    }

	return temp;
    }

    IntDomain divDom(IntDomain d, int c) {

	IntDomain temp;
	// System.out.println (d + " / " + c);

	if (c == 1) 
	    return d;
	else if ( c == -1) temp = invertDom(d);
	else {

	    temp = new IntervalDomain();

	    for (IntervalEnumeration e1 = d.intervalEnumeration(); e1.hasMoreElements();) {
		Interval i = e1.nextElement();
		int iMin = i.min();
		int iMax = i.max();

		IntervalDomain divDom = new IntervalDomain();

		    if ( c > 0) {

			int k = (int)Math.round( Math.ceil( (float)iMin/c ) );

		    	while (k*c <= iMax) {
		    	    divDom.unionAdapt(k, k);
		    	    k++;
		    	}

			/*
		    	for (int k=iMin; k<=iMax; k++) {

		    	    if (k % c == 0)
		    		// divDom.addDom(new IntervalDomain(k/c, k/c));
		    		divDom.unionAdapt(k/c, k/c);
		    	}
			*/
		    }
		    else {// c <= 0

			int k = (int)Math.round( Math.ceil( (float)iMax/c ) );

		    	while (k*c >= iMin) {
		    	    divDom.unionAdapt(k, k);
		    	    k++;
		    	}

			/*
			for (int k=iMax; k>=iMin; k--) {	

			    if (k % c == 0)
				// divDom.addDom(new IntervalDomain(k/c, k/c));
				divDom.unionAdapt(k/c, k/c);
			}
			*/
		    }

		// temp.addDom(divDom);
		temp.unionAdapt(divDom);

	    }
	}

	// System.out.println ("result/ = " + temp);

	return temp;
    }

    /*
    IntDomain plusDom(IntDomain d1, IntDomain d2) {
	IntDomain temp;
	// System.out.println (d1 + " + " + d2);
	
	temp = new IntervalDomain();

	for (IntervalEnumeration e1 = d1.intervalEnumeration(); e1.hasMoreElements();) {
	    Interval i1 = e1.nextElement(); 
	    int i1min = i1.min(), i1Max = i1.max();

	    for (IntervalEnumeration e2 = d2.intervalEnumeration(); e2.hasMoreElements();) {
		Interval i2 = e2.nextElement();
		// temp.addDom(new IntervalDomain(i1min+i2.min(), i1Max+i2.max()));
		temp.unionAdapt(i1min+i2.min(), i1Max+i2.max());
	    }
	}

	// System.out.println ("result+ = " + temp);

	return temp;
    }
    */

    IntDomain subtractDom(IntDomain d1, IntDomain d2) {

	IntDomain temp;
	temp = new IntervalDomain();

	int d1Min = d1.min();
	int d1Max = d1.max();

	for (IntervalEnumeration e1 = d1.intervalEnumeration(); e1.hasMoreElements();) {
	    Interval i1 = e1.nextElement(); 
	    int i1min = i1.min(), i1max = i1.max();

		for (IntervalEnumeration e2 = d2.intervalEnumeration(); e2.hasMoreElements();) {
		    Interval i2 = e2.nextElement();

		    // temp.addDom(new IntervalDomain(i1min-i2.max(), i1max-i2.min()));
		    temp.unionAdapt(i1min-i2.max(), i1max-i2.min());
		}
	}

	// System.out.println ("result- = " + temp);

	return temp;

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

}
