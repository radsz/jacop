/**
 *  SumBool.java 
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
 * SumBool constraint implements the summation over several
 * 0/1 variables. 
 *
 * sum(i in 1..N)(xi) = sum
 *
 * It provides the sum from all variables on the list.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.3
 */

public class SumBool extends Constraint {

    Store store;
    
    static int idNumber = 1;

    /**
     * It specifies a list of variables being summed.
     */
    IntVar x[];

    /**
     * It specifies variable for the overall sum. 
     */
    IntVar sum;

    /**
     * It specifies the number of variables. 
     */
    int l;

    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"list", "sum"};

    /**
     * @param list
     * @param weights
     * @param sum
     */
    public SumBool(Store store, IntVar[] list, IntVar sum) {

	commonInitialization(store, list, sum);
	

    }
	
    /**
     * It constructs the constraint SumBool. 
     * @param variables variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted variables.
     */
    public SumBool(Store store, ArrayList<? extends IntVar> variables,
			IntVar sum) {

		commonInitialization(store, variables.toArray(new IntVar[variables.size()]), sum);
    }


    private void commonInitialization(Store store, IntVar[] list, IntVar sum) {


	this.store = store;
	this.sum = sum;
	this.x = list;
	numberId = idNumber++;

	for (IntVar v : list) 
	    if (v.min() < 0 || v.max() > 1)
		throw new IllegalArgumentException("\nArguments of SumBool must have domains 0/1; variable "+v+" is incorrect.");
	
	this.l = x.length;
	    
	checkForOverflow();

	if (l <= 2)
	    queueIndex = 0;
	else
	    queueIndex = 1;

    }

    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(x.length+1);

	for (Var v : x)
	    variables.add(v);

	variables.add(sum);

	return variables;
    }


    @Override
    public void consistency(Store store) {
        int min=0, max=0;

        for (int i = 0; i < l; i++) {
	    IntDomain xd = x[i].dom();
            min += xd.min();
            max += xd.max();
	}
	
	sum.domain.in(store.level, sum, min, max);

        if (sum.singleton() && min != max) {
	    int sumValue = sum.value();
            if (sumValue == min) 
                for (IntVar v : x) 
                    if (! v.singleton()) 
                        v.domain.in(store.level, v, 0, 0);

            if (sumValue == max) 
                for (IntVar v : x) 
                    if (! v.singleton()) 
                        v.domain.in(store.level, v, 1, 1);
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

	sum.putModelConstraint(this, getConsistencyPruningEvent(sum));

	store.addChanged(this);
	store.countConstraint();
    }

    @Override
    public void removeConstraint() {
	for (Var v : x)
	    v.removeConstraint(this);
	sum.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {

        int min=0, max=0;

        for (int i = 0; i < l; i++) {
	    IntDomain xd = x[i].dom();
            min += xd.min();
            max += xd.max();
	}

	return sum.singleton(min) && min == max; 

    }

    void checkForOverflow() {

	int sMin=0, sMax=0;
	for (int i=0; i<x.length; i++) {
	    int n1 = x[i].min();
	    int n2 = x[i].max();

	    sMin = add(sMin, n1);
	    sMax = add(sMax, n2);
	}
    }

    @Override
    public String toString() {

	StringBuffer result = new StringBuffer( id() );
	result.append(" : SumBool( [ ");

	for (int i = 0; i < l; i++) {
	    result.append(x[i]);
	    if (i < l - 1)
		result.append(", ");
	}
	result.append("], ");
	
	result.append(sum).append( " )" );

	return result.toString();

    }

    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    for (Var v : x) v.weight++;
	}
	sum.weight++;
    }
}
