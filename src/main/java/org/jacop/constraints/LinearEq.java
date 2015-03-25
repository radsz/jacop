/**
 *  LinearEq.java 
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
 * LinearEq constraint implements the weighted summation over several
 * variables . 
 *
 * sum(i in 1..N)(ai*xi) = b
 *
 * It provides the weighted sum from all variables on the list.
 * The weights are integers.
 *
 * This implementaiton is based on 
 * "Bounds Consistency Techniques for Long Linear Constraints"
 * by Warwick Harvey and Joachim Schimpf
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

public class LinearEq extends Constraint {
    Store store;
    static int counter = 1;

    /**
     * It specifies a list of variables being summed.
     */
    IntVar x[];

    /**
     * It specifies a list of weights associated with the variables being summed.
     */
    int a[];

    /**
     * It specifies variable for the overall sum. 
     */
    int b;

    /**
     * It specifies the index of the last positive coefficient. 
     */
    int pos;
    
    /**
     * It specifies the number of varibales/coefficients. 
     */
    int l;

    /**
     * It specifies "variability" of each variable
     */
    int[] I;
    
    /**
     * It specifies sum of lower bounds (min values) and sum of upper bounds (max values)
     */
    int sumMin, sumMax;

    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"list", "weights", "sum"};

    /**
     * It constructs the constraint LinearEq. 
     * @param list variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted variables.
     */
    public LinearEq(Store store, IntVar[] list, int[] weights, int sum) {

	this.store = store;
	this.b = sum;

	commonInitialization(list, weights, sum);
    }
	
    private void commonInitialization(IntVar[] list, int[] weights, int sum) {

	queueIndex = 1;

	assert ( x.length == a.length ) : "\nLength of two vectors different in LinearEq";

	numberArgs = (short) (list.length);
	
	numberId = counter++;

	HashMap<IntVar, Integer> parameters = new HashMap<IntVar, Integer>();

	for (int i = 0; i < list.length; i++) {

	    assert (list[i] != null) : i + "-th element of list in LinearEq constraint is null";
			
	    if (weights[i] != 0) {
		if (list[i].singleton()) 
		    this.b -= list[i].value() * weights[i];
		else
		    if (parameters.get(list[i]) != null) {
			// variable ordered in the scope of the LinearEq constraint.
			Integer coeff = parameters.get(list[i]);
			Integer sumOfCoeff = coeff + weights[i];
			parameters.put(list[i], sumOfCoeff);
		    }
		    else
			parameters.put(list[i], weights[i]);

	    }
	}

	this.x = new IntVar[parameters.size()];
	this.a = new int[parameters.size()];

	int i = 0;
	for (IntVar var : parameters.keySet()) {
	    int coeff = parameters.get(var);
	    if (coeff > 0) {
		    this.x[i] = var;
		    this.a[i] = coeff;
		    i++;
	    }
	}
	pos = i;
	for (IntVar var : parameters.keySet()) {
	    int coeff = parameters.get(var);
	    if (coeff < 0) {
		    this.x[i] = var;
		    this.a[i] = coeff;
		    i++;
	    }
	}

	this.l = x.length;
	this.I = new int[l];
	    
	checkForOverflow();

    }

    /**
     * It constructs the constraint LinearEq. 
     * @param variables variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted variables.
     */
    public LinearEq(Store store, ArrayList<? extends IntVar> variables,
		    ArrayList<Integer> weights, int sum) {

	int[] w = new int[weights.size()];
	for (int i = 0; i < weights.size(); i++)
	    w[i] = weights.get(i);
		
	commonInitialization(variables.toArray(new IntVar[variables.size()]),
			     w,
			     sum);
    }


    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(x.length + 1);

	for (Var v : x)
	    variables.add(v);

	return variables;
    }


    @Override
    public void consistency(Store store) {

	computeInit();

	do {

	    store.propagationHasOccurred = false;

	    pruneLtEq();
	    pruneGtEq();

	    isEntailed();
	    
	} while (store.propagationHasOccurred);
    }

    protected void isEntailed() {
        if (sumMax <= b && sumMin >= b) {
            removeConstraint();
        }
    }

    private void pruneLtEq() {

        if (b - sumMin < 0) {
            throw store.failException;
        }
        int lb, ub;
	int i = 0;
        // positive weights
        for (; i < pos; i++) {
            if (I[i] - (b - sumMin) > 0) {
                lb = x[i].min() * a[i];
                ub = lb + I[i];
                if (pruneMax(x[i], divFloor(b - sumMin + lb, a[i]))) {
                    int nub = x[i].max() * a[i];
                    sumMax -= ub - nub;
                    I[i] = nub - lb;
                }
            }
        }
        // negative weights
        for (; i < l; i++) {
            if (I[i] - (b - sumMax) > 0) {
                lb = x[i].max() * a[i];
                ub = lb + I[i];
                if (pruneMin(x[i], divCeil(-(b - sumMin + lb), -a[i]))) {
                    int nub = x[i].min() * a[i];
                    sumMax -= ub - nub;
                    I[i] = nub - lb;
                }
            }
        }
    }

    private void pruneGtEq() {

        if (b - sumMax > 0) {
            throw store.failException;
        }
        int lb, ub;
	int i = 0;
        // positive weights
        for (; i < pos; i++) {
            if (I[i] > -(b - sumMax)) {
                ub = x[i].max() * a[i];
                lb = ub - I[i];
                if (pruneMin(x[i], divCeil(b - sumMax + ub, a[i]))) {
                    int nlb = x[i].min() * a[i];
                    sumMin += nlb - lb;
                    I[i] = ub - nlb;
                }
            }
        }
        // negative weights
        for (; i < l; i++) {
            if (I[i] > - (b - sumMax)) {
                ub = x[i].min() * a[i];
                lb = ub - I[i];
                if (pruneMax(x[i], divFloor(-(b - sumMax + ub), -a[i]))) {
                    int nlb = x[i].max() * a[i];
                    sumMin += nlb - lb;
                    I[i] = ub - nlb;
                }
            }
        }
    }

    private void computeInit() {
        int f = 0, e = 0;
        int min, max;
	int i = 0;
	// positive weights
        for (; i < pos; i++) {
            min = x[i].min() * a[i];
            max = x[i].max() * a[i];
            f += min;
            e += max;
            I[i] = (max - min);
        }
	// negative weights
        for (; i < l; i++) { 
            min = x[i].max() * a[i];
            max = x[i].min() * a[i];
            f += min;
            e += max;
            I[i] = (max - min);
        }
        sumMin = f;
        sumMax = e;
    }

    private boolean pruneMin(IntVar x, int min) {
	if (min > x.min()) {
	    x.domain.inMin(store.level, x, min);
	    return true;
	}
	else
	    return false;
    }

    private boolean pruneMax(IntVar x, int max) {
	if (max < x.max()) {
	    x.domain.inMax(store.level, x, max);
	    return true;
	}
	else
	    return false;
    }

    private int divFloor(int a, int b) {
        if (a >= 0) {
            return (a / b);
        } else {
            return (a - b + 1) / b;
        }
    }

    private int divCeil(int a, int b) {
        if (a >= 0) {
            return ((a + b - 1) / b);
        } else {
            return a / b;
        }
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
    public void impose(Store store) {

	if (x == null)
	    return;

	for (Var V : x)
	    V.putModelConstraint(this, getConsistencyPruningEvent(V));

	store.addChanged(this);
	store.countConstraint();
    }



    @Override
    public void removeConstraint() {
	for (Var v : x)
	    v.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {

	return false;

    }

    void checkForOverflow() {

	int sMin=0, sMax=0;
	for (int i=0; i<x.length; i++) {
	    int n1 = IntDomain.multiply(x[i].min(), a[i]);
	    int n2 = IntDomain.multiply(x[i].max(), a[i]);

	    if (n1 <= n2) {
		sMin = add(sMin, n1);
		sMax = add(sMax, n2);
	    }
	    else {
		sMin = add(sMin, n2);
		sMax = add(sMax, n1);
	    }
	}
    }
    @Override
    public String toString() {

	StringBuffer result = new StringBuffer( id() );
	result.append(" : LinearEq( [ ");

	for (int i = 0; i < x.length; i++) {
	    result.append(x[i]);
	    if (i < l - 1)
		result.append(", ");
	}
	result.append("], [");

	for (int i = 0; i < a.length; i++) {
	    result.append( a[i] );
	    if (i < l - 1)
		result.append( ", " );
	}

	result.append( "], ").append(", ").append(b).append( " )" );

	return result.toString();

    }

    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    for (Var v : x) v.weight++;
	}
    }
}
