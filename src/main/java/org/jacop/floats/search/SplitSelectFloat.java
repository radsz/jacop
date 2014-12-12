/**
 *  SplitSelectFloat.java 
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


package org.jacop.floats.search;

import org.jacop.constraints.PrimitiveConstraint;

import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PgtC;
import org.jacop.floats.constraints.PltC;
import org.jacop.floats.constraints.PlteqC;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;

import org.jacop.core.Var;
import org.jacop.core.Store;

import org.jacop.search.SimpleSelect;
import org.jacop.search.ComparatorVariable;
// import org.jacop.search.Indomain;
import org.jacop.core.TimeStamp;

/**
 * It is simple and customizable selector of decisions (constraints) which will
 * be enforced by search. However, it does not use P=c as a search decision 
 * but rather P <= c (potentially splitting the domain), unless c is equal to 
 * the maximal value in the domain of P then the constraint P < c is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 * @param <T> type of variable being used in the search.
 */

public class SplitSelectFloat<T extends Var> extends SimpleSelect<T> {


    /**
     * Select parameters are kept here sicne we use floats ansd Simple select uses int
     */

	/**
	 * It specifies if the left branch (values smaller or equal to the value selected) 
	 * are first considered.
	 */
	public boolean leftFirst = true;
	
	public boolean roundRobin = true;

	TimeStamp<Integer> currentIndex;

	/**
	 * The constructor to create a simple choice select mechanism.
	 * @param variables variables upon which the choice points are created.
	 * @param varSelect the variable comparator to choose the variable.
	 */
	public SplitSelectFloat(Store store, T[] variables, 
				ComparatorVariable<T> varSelect) {

	    super(variables, varSelect, null);

	    currentIndex = new TimeStamp<Integer>(store, 0);

	}

	/**
	 * It constructs a simple selection mechanism for choice points.
	 * @param variables variables used as basis of the choice point.
	 * @param varSelect the main variable comparator.
	 * @param tieBreakerVarSelect secondary variable comparator employed if the first one gives the same metric.
	 */
	public SplitSelectFloat(Store store, T[] variables, 
				ComparatorVariable<T> varSelect,
				ComparatorVariable<T> tieBreakerVarSelect) {
				// , 
				// 	   Indomain<T> indomain) {

	    super(variables, varSelect, tieBreakerVarSelect, null);

	    currentIndex = new TimeStamp<Integer>(store, 0);

	}
	
	@Override 
	public T getChoiceVariable(int index) {
		return null;
	}
	
	@Override
	public PrimitiveConstraint getChoiceConstraint(int index) {
			    
	    T var = super.getChoiceVariable(index);

	    if (variableOrdering == null && roundRobin)
		    var = roundRobinVarSelection(index);
	    else
		var = super.getChoiceVariable(index);

	    if (var == null)
		return null;
		
	    assert (index >= 0);
	    // assert (index < searchVar.length);
	    // assert (searchVar[index].dom() != null);

	    double value = (((FloatVar)var).min() + ((FloatVar)var).max()) / 2.0;

	    // System.out.println (var + ", value = " + value);

	    if (leftFirst)
		if ( ((FloatVar)var).max() > value )
		    return new PlteqC((FloatVar)var, value);
		else 
		    return new PltC((FloatVar)var, value);
	    else
		if ( ((FloatVar)var).max() > value)
		    return new PgtC((FloatVar)var, value);
		else
		    return new PeqC((FloatVar)var, value);
	}
	

	T roundRobinVarSelection(int index) {

		assert (index < searchVariables.length);

		int N = searchVariables.length;

		int n = 0;
		int i = currentIndex.value();
		int ii = i;
		do {

		    if (!searchVariables[i].singleton()) {
			currentIndex.update( (i+1) % N );

			return searchVariables[i];
		    }

		    ii = i;
		    i = (i + 1 ) % N;
		    n++;

		} while (searchVariables[ii].singleton() && n < N);

		return null;
	}
	
}
