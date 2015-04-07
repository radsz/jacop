/**
 *  LinearInt.java 
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

import org.jacop.core.IntVar;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * LinearInt constraint implements the weighted summation over several
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

public class LinearInt extends PrimitiveConstraint {

    Store store;
    
    static int counter = 1;

    boolean reified = true;

    /**
     * Defines relations
     */
    final static byte eq=0, le=1, lt=2, ne=3, gt=4, ge=5;

    /**
     * Defines negated relations
     */
    final static byte[] negRel= {ne, //eq=0, 
				 gt, //le=1, 
				 ge, //lt=2, 
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
     * @param list
     * @param weights
     * @param sum
     */
    public LinearInt(Store store, IntVar[] list, int[] weights, String rel, int sum) {

	commonInitialization(store, list, weights, sum);
	this.relationType = relation(rel);
	

    }
	
    /**
     * It constructs the constraint LinearInt. 
     * @param variables variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted variables.
     */
    public LinearInt(Store store, ArrayList<? extends IntVar> variables,
			ArrayList<Integer> weights, String rel, int sum) {

		int[] w = new int[weights.size()];
		for (int i = 0; i < weights.size(); i++)
			w[i] = weights.get(i);

		commonInitialization(store, variables.toArray(new IntVar[variables.size()]), w, sum);
		this.relationType = relation(rel);
    }


    private void commonInitialization(Store store, IntVar[] list, int[] weights, int sum) {

	assert ( list.length == weights.length ) : "\nLength of two vectors different in Propagations";

	this.store = store;
	this.b = sum;

	HashMap<IntVar, Integer> parameters = new HashMap<IntVar, Integer>();

	for (int i = 0; i < list.length; i++) {

	    assert (list[i] != null) : i + "-th element of list in Propagations constraint is null";
			
	    if (weights[i] != 0) {
		if (list[i].singleton()) 
		    this.b -= list[i].value() * weights[i];
		else
		    if (parameters.get(list[i]) != null) {
			// variable ordered in the scope of the Propagations constraint.
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

	if (l <= 3)
	    queueIndex = 0;
	else
	    queueIndex = 1;

    }

    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(x.length);

	for (Var v : x)
	    variables.add(v);

	return variables;
    }


    @Override
    public void consistency(Store store) {

	computeInit();

	do {

	    store.propagationHasOccurred = false;

	    switch (relationType) {
	    case eq:

		pruneLtEq();
		pruneGtEq();

		if (sumMax <= b && sumMin >= b) 
		    removeConstraint();

		break;

	    case le:
		pruneLtEq();

		if (sumMax <= b) 
		    removeConstraint();
		break;

	    case lt:
		pruneLt();

		if (sumMax < b) 
		    removeConstraint();
		break;
	    case ne:
		pruneNeq();

		if (sumMin == sumMax && sumMin != b)
		    removeConstraint();
		break;
	    case gt:

		pruneGt();

		if (sumMin > b)
		    removeConstraint();		
		break;
	    case ge:

		pruneGtEq();

		if (sumMin >= b)
		    removeConstraint();

		break;
	    }

	} while (store.propagationHasOccurred);
    }

    @Override
    public void notConsistency(Store store) {
		
	computeInit();

	do {

	    store.propagationHasOccurred = false;

	    switch (negRel[relationType]) {
	    case eq:

		pruneLtEq();
		pruneGtEq();
		
		if (sumMax <= b && sumMin >= b) 
		    removeConstraint();

		break;

	    case le:
		pruneLtEq();

		if (sumMax <= b) 
		    removeConstraint();
		break;

	    case lt:
		pruneLt();

		if (sumMax < b) 
		    removeConstraint();
		break;
	    case ne:
		pruneNeq();

		if (sumMin > b || sumMax < b)
		    removeConstraint();
		break;
	    case gt:

		pruneGt();

		if (sumMin > b)
		    removeConstraint();		
		break;
	    case ge:

		pruneGtEq();

		if (sumMin >= b)
		    removeConstraint();

		break;
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

	if (x == null)
	    return;

	reified = false;

	for (Var V : x)
	    V.putModelConstraint(this, getConsistencyPruningEvent(V));

	store.addChanged(this);
	store.countConstraint();
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

    private void pruneLtEq() {

        if (sumMin > b)
            throw store.failException;
	
        int min, max;
	int i = 0;
        // positive weights
        for (; i < pos; i++) {
            if (I[i] > b - sumMin) {
                min = x[i].min() * a[i];
                max = min + I[i];
                if (pruneMax(x[i], divRoundDown(b - sumMin + min, a[i]))) {
                    int newMax = x[i].max() * a[i];
                    sumMax -= max - newMax;
                    I[i] = newMax - min;
                }
            }
        }
        // negative weights
        for (; i < l; i++) {
            if (I[i] > b - sumMax) {
                min = x[i].max() * a[i];
                max = min + I[i];
                if (pruneMin(x[i], divRoundUp(-(b - sumMin + min), -a[i]))) {
                    int newMax = x[i].min() * a[i];
                    sumMax -= max - newMax;
                    I[i] = newMax - min;
                }
            }
        }
    }

    private void pruneGtEq() {

        if (sumMax < b) 
            throw store.failException;

        int min, max;
	int i = 0;
        // positive weights
        for (; i < pos; i++) {
            if (I[i] > -(b - sumMax)) {
                max = x[i].max() * a[i];
                min = max - I[i];
                if (pruneMin(x[i], divRoundUp(b - sumMax + max, a[i]))) {
                    int nmin = x[i].min() * a[i];
                    sumMin += nmin - min;
                    I[i] = max - nmin;
                }
            }
        }
        // negative weights
        for (; i < l; i++) {
            if (I[i] > - (b - sumMax)) {
                max = x[i].min() * a[i];
                min = max - I[i];
                if (pruneMax(x[i], divRoundDown(-(b - sumMax + max), -a[i]))) {
                    int newMin = x[i].max() * a[i];
                    sumMin += newMin - min;
                    I[i] = max - newMin;
                }
            }
        }
    }

    private void pruneLt() {

        if (sumMin >= b)
            throw store.failException;

        int min, max;
	int i = 0;
        // positive weights
        for (; i < pos; i++) {
            if (I[i] >= b - sumMin) {
                min = x[i].min() * a[i];
                max = min + I[i];
                if (pruneMax(x[i], divRoundDown(b - sumMin + min, a[i]))) {
                    int newMax = x[i].max() * a[i];
                    sumMax -= max - newMax;
                    I[i] = newMax - min;
                }
            }
        }
        // negative weights
        for (; i < l; i++) {
            if (I[i] >= b - sumMax) {
                min = x[i].max() * a[i];
                max = min + I[i];
                if (pruneMin(x[i], divRoundUp(-(b - sumMin + min), -a[i]))) {
                    int newMax = x[i].min() * a[i];
                    sumMax -= max - newMax;
                    I[i] = newMax - min;
                }
            }
        }
    }

    private void pruneGt() {

        if (sumMax <= b) 
            throw store.failException;

        int min, max;
	int i = 0;
        // positive weights
        for (; i < pos; i++) {
            if (I[i] >= -(b - sumMax)) {
                max = x[i].max() * a[i];
                min = max - I[i];
                if (pruneMin(x[i], divRoundUp(b - sumMax + max, a[i]))) {
                    int nmin = x[i].min() * a[i];
                    sumMin += nmin - min;
                    I[i] = max - nmin;
                }
            }
        }
        // negative weights
        for (; i < l; i++) {
            if (I[i] >= - (b - sumMax)) {
                max = x[i].min() * a[i];
                min = max - I[i];
                if (pruneMax(x[i], divRoundDown(-(b - sumMax + max), -a[i]))) {
                    int newMin = x[i].max() * a[i];
                    sumMin += newMin - min;
                    I[i] = max - newMin;
                }
            }
        }
    }

    private void pruneNeq() {

        if (sumMin == sumMax && b == sumMin) 
            throw store.failException;

        int min, max;
	int i = 0;
        // positive weights
        for (; i < pos; i++) {
	    min = x[i].min() * a[i];
	    max = min + I[i];

	    if (pruneNe(x[i], b - sumMax + max, b - sumMin + min, a[i])) {
		int newMin = x[i].min() * a[i];
		int newMax = x[i].max() * a[i];
		sumMin += newMin - min;
		sumMax += newMax - max;
		I[i] = newMax - newMin;
	    }
        }
        // negative weights
        for (; i < l; i++) {
	    min = x[i].max() * a[i];
	    max = min + I[i];

	    if (pruneNe(x[i], -(b - sumMin + min), -(b - sumMax + max), a[i])) {
		int newMin = x[i].max() * a[i];
		int newMax = x[i].min() * a[i];
		sumMin += newMin - min;
		sumMax += newMax - max;
		I[i] = newMax - newMin;
	    }
	}
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

    private boolean pruneNe(IntVar x, int min, int max, int a) {

	if (min == max) {
	    int low = divRoundUp(min, a);
	    int high = divRoundDown(max, a);
	    if (low == high) {
		boolean boundsChanged = false;
		if (low == x.min() || high == x.max())
		    boundsChanged = true;

		x.domain.inComplement(store.level, x, low);

		return boundsChanged;
	    }
	}

	return false;
    }

    public boolean satisfiedEq() {

        int sMin = 0, sMax = 0;
	int i = 0;
        for (; i < pos; i++) {
            sMin += x[i].min() * a[i];
            sMax += x[i].max() * a[i];
        }
        for (; i < l; i++) {
            sMin += x[i].max() * a[i];
            sMax += x[i].min() * a[i];
        }

        return sMin == sMax && sMin == b;
    }

    public boolean satisfiedNeq() {

        int sMax = 0, sMin = 0;
	int i = 0;
        for (; i < pos; i++) {
            sMin += x[i].min() * a[i];
            sMax += x[i].max() * a[i];
        }
        for (; i < l; i++) {
            sMin += x[i].max() * a[i];
            sMax += x[i].min() * a[i];
        }

        return sMin > b || sMax < b;
    }

    public boolean satisfiedLtEq() {

	int sMax = 0;
	int i = 0;
        for (; i < pos; i++) {
            sMax += x[i].max() * a[i];
        }
        for (; i < l; i++) {
            sMax += x[i].min() * a[i];
        }

        return  sMax <= b;
    }

    public boolean satisfiedLt() {

	int sMax = 0;
	int i = 0;
        for (; i < pos; i++) {
            sMax += x[i].max() * a[i];
        }
        for (; i < l; i++) {
            sMax += x[i].min() * a[i];
        }

        return  sMax < b;
    }

    public boolean satisfiedGtEq() {

	int sMin = 0;
	int i = 0;
        for (; i < pos; i++) {
            sMin += x[i].min() * a[i];
        }
        for (; i < l; i++) {
            sMin += x[i].max() * a[i];
        }

        return  sMin >= b;
    }

    public boolean satisfiedGt() {

	int sMin = 0;
	int i = 0;
        for (; i < pos; i++) {
            sMin += x[i].min() * a[i];
        }
        for (; i < l; i++) {
            sMin += x[i].max() * a[i];
        }

        return  sMin > b;
    }

    @Override
    public void removeConstraint() {
	for (Var v : x)
	    v.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {

	return entailed(relationType);

    }

    @Override
    public boolean notSatisfied() {

	return entailed(negRel[relationType]);

    }

    private boolean entailed(int rel) {

	switch (rel) {
	case eq:
	    return satisfiedEq();
	case le:
	    return satisfiedLtEq();
	case lt:
	    return satisfiedLt();
	case ne:
	    return satisfiedNeq();
	case gt:
	    return satisfiedGt();
	case ge:
	    return satisfiedGtEq();
	}

	return false;
    }

    private int divRoundDown(int a, int b) {
        if (a >= 0) 
            return a / b;
        else // a < 0
            return (a - b + 1) / b;
    }

    private int divRoundUp(int a, int b) {
        if (a >= 0) 
            return (a + b - 1) / b;
        else // a < 0
            return a / b;
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
	    System.err.println ("Wrong relation symbol in LinearInt constraint " + r + "; assumed ==");
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
	result.append(" : LinearInt( [ ");

	for (int i = 0; i < x.length; i++) {
	    result.append(x[i]);
	    if (i < x.length - 1)
		result.append(", ");
	}
	result.append("], [");

	for (int i = 0; i < a.length; i++) {
	    result.append( a[i] );
	    if (i < a.length - 1)
		result.append( ", " );
	}

	result.append( "], ").append(rel2String()).append(", ").append(b).append( " )" );

	return result.toString();

    }

    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    for (Var v : x) v.weight++;
	}
    }
}
