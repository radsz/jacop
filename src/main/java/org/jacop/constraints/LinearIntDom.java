/**
 *  LinearIntDom.java 
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
import java.util.LinkedHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Interval;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * LinearIntDom constraint implements the weighted summation over several
 * variables. 
 *
 * sum(i in 1..N)(ai*xi) = b
 *
 * It provides the weighted sum from all variables on the list.
 * The weights are integers. Domain consistency is used.
 *
 *
 * @author Krzysztof Kuchcinski
 * @version 4.4
 */

public class LinearIntDom extends LinearInt {

	static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * Defines support (valid values) for each variable
     */
    IntervalDomain[] support;

    /**
     * Collects support (valid assignments) for variables
     */
    int[] assignments;

    /**
     * Limit on the product of sizes of domains when domain consistency
     * is carried out.
     */
    double limitDomainPruning = 1e+7;

    /**
     * It constructs the constraint LinearIntDom. 
     * @param store current store
     * @param list variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum the sum of weighted variables.
     */
    public LinearIntDom(Store store, IntVar[] list, int[] weights, String rel, int sum) {

			commonInitialization(store, list, weights, sum);
			this.relationType = relation(rel);
			numberId = idNumber.incrementAndGet();
			queueIndex = 4;
    }
	
    /**
     * It constructs the constraint LinearIntDom. 
     * @param store current store
     * @param list variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum variable containing the sum of weighted variables.
     */
    public LinearIntDom(Store store, IntVar[] list, int[] weights, String rel, IntVar sum) {

			queueIndex = 4;
			IntVar[] vars = new IntVar[list.length + 1];
			System.arraycopy(list, 0, vars, 0, list.length);
			vars[list.length] = sum;
			int[] ws = new int[weights.length + 1];
			System.arraycopy(weights, 0, ws, 0, weights.length);
			ws[list.length] = -1;

			commonInitialization(store, vars, ws, 0);
			this.relationType = relation(rel);
			numberId = idNumber.incrementAndGet();

    }
	
    /**
     * It constructs the constraint LinearIntDom. 
     * @param store current store
     * @param variables variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum variable containing the sum of weighted variables.
     */
    public LinearIntDom(Store store, ArrayList<? extends IntVar> variables,
			ArrayList<Integer> weights, String rel, int sum) {
			int[] w = new int[weights.size()];
			for (int i = 0; i < weights.size(); i++)
				w[i] = weights.get(i);

			commonInitialization(store, variables.toArray(new IntVar[variables.size()]), w, sum);
			numberId = idNumber.incrementAndGet();
			this.relationType = relation(rel);

			queueIndex = 4;
    }

    @Override
    public void consistency(Store store) {
	propagate(relationType);
    }

    @Override
    public void notConsistency(Store store) {
	propagate(negRel[relationType]);
    }

    public void propagate(int rel) {

	computeInit();

	do {

	    store.propagationHasOccurred = false;

	    switch (rel) {
	    case eq:

		if (domainSize() < limitDomainPruning)
		    pruneEq(); // domain consistency
		else {
		    // bound consistency
		    pruneLtEq(b);
		    pruneGtEq(b);
		}

		if (!reified && sumMax <= b && sumMin >= b) 
		    removeConstraint();

		break;

	    case ne:
		if (domainSize() < limitDomainPruning)
		    pruneNeq();
		else
		    super.pruneNeq();

	    	// if (!reified && sumMin == sumMax && sumMin != b)
	    	if (!reified && (sumMin > b || sumMax < b))
	    	    removeConstraint();
	    	break;
	    default:
		System.out.println("Not implemented relation in LinearIntDom; implemented == and != only.");
		break;
	    }

	} while (store.propagationHasOccurred);
    }

    double domainSize() {

	double s = 1;
	for (int i = 0; i < l; i++) 
	    s *= (double)x[i].domain.getSize();

	// System.out.println("s = " + s);

	return s;
    }
    
    void pruneEq() {

	if (sumMin > b || sumMax < b)
	    throw store.failException;

	// System.out.println("check " + this);
	assignments = new int[l];
	support = new IntervalDomain[l];
	for (int i = 0; i < l; i++) 
	    support[i] = new IntervalDomain();

	findSupport(0, 0);

	// System.out.println("Variables: "+java.util.Arrays.asList(x)+" have valid assignments: " + java.util.Arrays.asList(support));
	int f = 0, e = 0;
	for (int i = 0; i < pos; i++) {
	    x[i].domain.in(store.level, x[i], support[i]);

	    f += x[i].min()*a[i];
	    e += x[i].max()*a[i];
	}
	for (int i = pos; i < l; i++) {
	    x[i].domain.in(store.level, x[i], support[i]);

	    f += x[i].max()*a[i];
	    e += x[i].min()*a[i];
	}
	sumMin = f;
	sumMax = e;
    }

    void pruneNeq() {

	assignments = new int[l];
	support = new IntervalDomain[l];
	for (int i = 0; i < l; i++) 
	    support[i] = new IntervalDomain();

	findSupport(0, 0);

	// System.out.println("valid assignments: " + java.util.Arrays.asList(support));

	int f = 0, e = 0;
	for (int i = 0; i < pos; i++) {
	    if (support[i].singleton())
		x[i].domain.inComplement(store.level, x[i], support[i].value());

	    f += x[i].min()*a[i];
	    e += x[i].max()*a[i];
	}
	for (int i = pos; i < l; i++) {
	    if (support[i].singleton())
		x[i].domain.inComplement(store.level, x[i], support[i].value());

	    f += x[i].max()*a[i];
	    e += x[i].min()*a[i];
	}
	sumMin = f;
	sumMax = e;
    }

    void findSupport(int index, int sum) {

	findSupportPositive(index, sum);

    }
    
    void findSupportPositive(int index, int partialSum) {

	int newIndex = index + 1;
	
	if (index == l - 1) {

	    int element = b - partialSum;
	    int val = element / a[index];
	    int rest = element % a[index];
	    if (rest == 0 && x[index].domain.contains(val)) {
		assignments[index] = val;

		// store assignments
		for (int i = 0; i < l; i++) {
		    int a = assignments[i];
		    if (support[i].getSize() == 0)
			support[i] = new IntervalDomain(a, a);
		    else if (support[i].max() < a)
			support[i].addLastElement(a);
		    else if (support[i].max() > a)
			support[i].unionAdapt(a, a);
		}
	    }
	    return;
	}
	
	IntDomain currentDom = x[index].dom();
	int newPartialSum = partialSum;
	int w = a[index];
	
	int lb = b - sumMax + currentDom.max()*w;
	int ub = b - sumMin + currentDom.min()*w;
	    
	if (currentDom.domainID() == IntDomain.IntervalDomainID) {
	    int n = ((IntervalDomain)currentDom).size;

	    outerloop:
	    for (int k = 0; k < n; k++) {
		Interval e = ((IntervalDomain)currentDom).intervals[k];
		int eMin = e.min();
		int eMax = e.max();

		for (int element = eMin; element <= eMax; element++) {
		
		    int elementValue = element*w;
		    if (elementValue  < lb) 
			continue; // value too low
		    else if (elementValue > ub)
		      	break outerloop; // value too large
		    else
			newPartialSum = partialSum + elementValue;

		    assignments[index] = element;

		if (newIndex < pos)
		    findSupportPositive(newIndex, newPartialSum);
		else
		    findSupportNegative(newIndex, newPartialSum);
		}
	    }
	}
	else

	    for (ValueEnumeration val = currentDom.valueEnumeration(); val.hasMoreElements();) {
		int element = val.nextElement();

		int elementValue = element*w;
		if (elementValue  < lb) 
		    continue; // value too low
		else if (elementValue > ub)
		    break; // value too large
		else
		    newPartialSum = partialSum + elementValue;

		assignments[index] = element;

		if (newIndex < pos)
		    findSupportPositive(newIndex, newPartialSum);
		else
		    findSupportNegative(newIndex, newPartialSum);
	    }
    }


    void findSupportNegative(int index, int partialSum) {

	int newIndex = index + 1;
	
	if (index == l - 1) {

	    int element = b - partialSum;
	    int val = element / a[index];
	    int rest = element % a[index];
	    if (rest == 0 && x[index].domain.contains(val)) {
		assignments[index] = val;

		// store assignments
		for (int i = 0; i < l; i++) {
		    int a = assignments[i];
		    if (support[i].getSize() == 0)
			support[i] = new IntervalDomain(a, a);
		    else if (support[i].max() < a)
			support[i].addLastElement(a);
		    else if (support[i].max() > a)
			support[i].unionAdapt(a, a);
		}
	    }
	    return;
	}

	IntDomain currentDom = x[index].dom();
	int newPartialSum = partialSum;
	int w = a[index];
	
	int lb = b - sumMax + currentDom.min()*w;
	int ub = b - sumMin + currentDom.max()*w;
	    
	if (currentDom.domainID() == IntDomain.IntervalDomainID) {
	    int n = ((IntervalDomain)currentDom).size;

	    outerloop:
	    for (int k = 0; k < n; k++) {
		Interval e = ((IntervalDomain)currentDom).intervals[k];
		int eMin = e.min();
		int eMax = e.max();
			
		for (int element = eMin; element <= eMax; element++) {
		
		    int elementValue = element*w;
		    if (elementValue  < lb) 
			break outerloop; // value too low
		    else if (elementValue > ub)
		     	continue; // value too large
		    else
			newPartialSum = partialSum + elementValue;

		    assignments[index] = element;

		    findSupportNegative(newIndex, newPartialSum);
		}
	    }
	}
	else
	    for (ValueEnumeration val = currentDom.valueEnumeration(); val.hasMoreElements();) {
		int element = val.nextElement();

		int elementValue = element*w;
		if (elementValue  < lb) 
		    break; // value too low
		else if (elementValue > ub)
		    continue; // value too large
		else
		    newPartialSum = partialSum + elementValue;

		assignments[index] = element;

		findSupportNegative(newIndex, newPartialSum);
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
	return IntDomain.ANY;
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
	    return IntDomain.ANY;
	}

	// If notConsistency function mode
	else {
	    if (notConsistencyPruningEvents != null) {
		Integer possibleEvent = notConsistencyPruningEvents.get(var);
		if (possibleEvent != null)
		    return possibleEvent;
	    }
	    return IntDomain.ANY;
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
	return IntDomain.ANY;	
    }

    @Override
    public String toString() {

	StringBuffer result = new StringBuffer( id() );
	result.append(" : LinearIntDom( [ ");

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

}
