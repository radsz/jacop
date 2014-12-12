/**
 *  Lex.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2010 Krzysztof Kuchcinski and Radoslaw Szymanek
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

import org.jacop.constraints.regular.Regular;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.util.fsm.FSM;
import org.jacop.util.fsm.FSMState;
import org.jacop.util.fsm.FSMTransition;

/**
 *
 * It constructs a Lex (lexicographical order) constraint. 
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Lex extends DecomposedConstraint {

    /**
     * A two dimensional array containing arrays which have to be lexicographically ordered.
     */
    public IntVar[][] x;

    /**
     * It contains constraints of the lex constraint decomposition. 
     */
    ArrayList<Constraint> constraints;

    /**
     * Is the lex enforcing lower then relationship?
     */
    public final boolean lexLT;

    /**
     * It creates a lexicographical order for vectors x[i], i.e. 
     * forall i, exists j : x[i][k] = x[i+1][k] for k < j and x[i][k] <= x[i+1][k]
     * for k >= j
     *
     * vectors x[i] does not need to be of the same size.
     * boolea lt defines if we require Lex_{<} (lt = false) or Lex_{=<} (lt = true)
     *
     * @param x vector of vectors which assignment is constrained by Lex constraint. 
     */
    public Lex(IntVar[][] x) {

	this(x, false);
		
    }


    public Lex(IntVar[][] x, boolean lt) {
		
	assert (x != null) : "x list is null.";
	this.x = new IntVar[x.length][];
		
	lexLT = lt;
		
	for (int i = 0; i < x.length; i++) {
			
	    assert (x[i] != null) : i + "-th vector in x is null";
	    this.x[i] = new IntVar[x[i].length];
			
	    for (int j = 0; j < x[i].length; j++) {
		assert (x[i][j] != null) : j + "-th element of " + i + "-th vector in x is null";
		this.x[i][j] = x[i][j];
	    }
			
	}
		
    }


    @Override
	public void imposeDecomposition(Store store) {

	if (constraints == null)
	    decompose(store);

	for (Constraint c : constraints) 
	    store.impose(c, queueIndex);

    }

    @Override
	public ArrayList<Constraint> decompose(Store store) {

	if (constraints != null)
	    return constraints;

	if (x.length == 2) // && x[0].length > 100)
	    if (lexLT)
		return decomposeLT(store);
	    else
		return decomposeLE(store);

	// smaller Lex with several lists can be decompose with Regular
	if (lexLT)
	    return decomposeLTRegular(store);
	else
	    return decomposeLERegular(store);

    }


    public ArrayList<Constraint> decomposeLERegular(Store store) {

	if (constraints == null)
	    constraints = new ArrayList<Constraint>();
	else
	    return constraints;
		
	// first index represents compared vectors and the second variables within vectors
	//		int numberStates = 0;
	int numberVar = 0;
		
	BooleanVar[][] lt = new BooleanVar[x.length - 1][];
	BooleanVar[][] eq = new BooleanVar[x.length - 1][];
	FSMState[][][] state = new FSMState[x.length - 1][][];
	FSMState[][] addState = new FSMState[x.length - 2][];

	for (int i = 0; i < x.length-1; ++i) {

	    int sizeToCompare = (x[i].length < x[i+1].length) ? x[i].length : x[i+1].length;

	    lt[i] = new BooleanVar[sizeToCompare];
	    eq[i] = new BooleanVar[sizeToCompare];
	    state[i] = new FSMState[sizeToCompare][];

	    for (int j = 0; j < sizeToCompare; j++) {
		lt[i][j] = new BooleanVar(store, "lt_"+i+"_"+j);
		eq[i][j] = new BooleanVar(store, "eq_"+i+"_"+j);

		constraints.add(new Reified(new XltY(x[i][j], x[i+1][j]), lt[i][j]));
		constraints.add(new Reified(new XeqY(x[i][j], x[i+1][j]), eq[i][j]));

		if (x[i].length > x[i+1].length && j == sizeToCompare -1 )
		    constraints.add(new XeqC(eq[i][j], 0));

		state[i][j] = new FSMState[2];
		state[i][j][0] = new FSMState();
		state[i][j][1] = new FSMState();
		numberVar += 2;
		//				numberStates += 2;

		if (i < x.length - 2 ) {
		    //					numberStates += 2*(sizeToCompare-j) - 1;
		    if ( j == 0) {
			addState[i] = new FSMState[2*(sizeToCompare-j) - 1];

			for (int k = 0; k < addState[i].length; k++) 
			    addState[i][k] = new FSMState();
		    }
		}
	    }
	}
	//		numberStates++;

	IntVar[] var = new IntVar[numberVar];
	FSM g = new FSM();
	int k=0;
	for (int i = 0; i < lt.length; i++) {
	    for (int j = 0; j < lt[i].length; j++) {
		var[k++] = lt[i][j];
		var[k++] = eq[i][j];

		g.allStates.add(state[i][j][0]);
		g.allStates.add(state[i][j][1]);
	    }
	}
	for (int i = 0; i < addState.length; i++) 
	    for (int j = 0; j < addState[i].length; j++)
		g.allStates.add(addState[i][j]);


	g.initState = state[0][0][0];
	FSMState terminate = new FSMState(); 
	g.allStates.add(terminate);
	g.finalStates.add(terminate);

	for (int i = 0; i < state.length; i++) {
	    for (int j = 0; j < state[i].length; j++) {

		if ( i != state.length - 1) {
		    // cannot go directly- must go through other states :(
		    if ( addState[i].length !=0 ) {
			if ( j == 0 ) {
			    state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(1,1), addState[i][0])); 

			    for (int s = 1; s < addState[i].length; s++)
				addState[i][s-1].transitions.add(new FSMTransition(new IntervalDomain(0,1), addState[i][s]));
			    addState[i][addState[i].length-1].transitions.add(new FSMTransition(new IntervalDomain(0,1), state[i+1][0][0]));
			}
			else 
			    state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(1,1), addState[i][2*j])); 

			state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(0,0), state[i][j][1]));
		    }
		}
		else {  // i == state.length
		    state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(1,1), terminate));
		    state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(0,0), state[i][j][1]));
		}

		if ( i != state.length - 1) {
		    if ( j != state[i].length - 1 )
			state[i][j][1].transitions.add(new FSMTransition(new IntervalDomain(1,1), state[i][j+1][0]));
		    else 
			state[i][j][1].transitions.add(new FSMTransition(new IntervalDomain(1,1), state[i+1][0][0]));
		}
		else { // i == state.length
		    if ( j != state[i].length - 1 )
			state[i][j][1].transitions.add(new FSMTransition(new IntervalDomain(1,1), state[i][j+1][0]));
		    else {
			state[i][j][1].transitions.add(new FSMTransition(new IntervalDomain(1,1), terminate));
		    }
		}
	    }
	}

	terminate.transitions.add(new FSMTransition(new IntervalDomain(0, 1), terminate));

	constraints.add(new Regular(g, var));

	return constraints;
    }


    public ArrayList<Constraint> decomposeLTRegular(Store store) {

	if (constraints == null)
	    constraints = new ArrayList<Constraint>();
	else
	    return constraints;

	// first index represents compared vectors and the second varinbales within vectors
	//		int numberStates = 0;
	int numberVar = 0;
	BooleanVar[][] lt = new BooleanVar[x.length - 1][];
	BooleanVar[][] eq = new BooleanVar[x.length - 1][];
	FSMState[][][] state = new FSMState[x.length - 1][][];
	FSMState[][] addState = new FSMState[x.length - 2][];

	for (int i = 0; i < x.length-1; ++i) {

	    int sizeToCompare = (x[i].length < x[i+1].length) ? x[i].length : x[i+1].length;

	    lt[i] = new BooleanVar[sizeToCompare];
	    eq[i] = new BooleanVar[sizeToCompare - 1];
	    state[i] = new FSMState[sizeToCompare][];

	    for (int j = 0; j < sizeToCompare; j++) {

		if (x[i].length < x[i+1].length)
		    if ( j < sizeToCompare - 1) {
			lt[i][j] = new BooleanVar(store, "lt_"+i+"_"+j);
			numberVar++;
			constraints.add(new Reified(new XltY(x[i][j], x[i+1][j]), lt[i][j]));
		    }
		    else { // j == sizeToCompare - 1 , i.e., last check
			lt[i][j] = new BooleanVar(store, "le_"+i+"_"+j);
			numberVar++;
			constraints.add(new Reified(new XlteqY(x[i][j], x[i+1][j]), lt[i][j]));
		    }
		else {
		    lt[i][j] = new BooleanVar(store, "lt_"+i+"_"+j);
		    numberVar++;
		    constraints.add(new Reified(new XltY(x[i][j], x[i+1][j]), lt[i][j]));
		}

		if ( j < sizeToCompare - 1 ) {
		    eq[i][j] = new BooleanVar(store, "eq_"+i+"_"+j);
		    numberVar++;
		    constraints.add(new Reified(new XeqY(x[i][j], x[i+1][j]), eq[i][j]));
		}

		state[i][j] = new FSMState[2];
		state[i][j][0] = new FSMState();
		//				numberStates++;
		if ( j < sizeToCompare - 1 ) {
		    state[i][j][1] = new FSMState();
		    //					numberStates++;
		}

		if (i < x.length - 2 ) {
		    //					numberStates += 2*(sizeToCompare-j) - 2;

		    if ( j == 0 ){
			addState[i] = new FSMState[2*(sizeToCompare-j) - 2];

			for (int k = 0; k < addState[i].length; k++) 
			    addState[i][k] = new FSMState();
		    }
		}
	    }
	}
	//		numberStates++;

	IntVar[] var = new IntVar[numberVar];
	FSM g = new FSM();
	int k=0;
	for (int i = 0; i < lt.length; i++) {
	    for (int j = 0; j < lt[i].length; j++) {
		var[k++] = lt[i][j];
		if ( j < eq[i].length)
		    var[k++] = eq[i][j];

		g.allStates.add(state[i][j][0]);
		if ( j < eq[i].length)
		    g.allStates.add(state[i][j][1]);
	    }
	}
	for (int i = 0; i < addState.length; i++) 
	    for (int j = 0; j < addState[i].length; j++)
		g.allStates.add(addState[i][j]);


	g.initState = state[0][0][0];
	FSMState terminate = new FSMState(); 
	g.allStates.add(terminate);
	g.finalStates.add(terminate);

	for (int i = 0; i < state.length; i++) {
	    for (int j = 0; j < state[i].length; j++) {

		if ( i != state.length - 1) {
		    // cannot go directly - must go through other states :(
		    if ( addState[i].length != 0 )
			if ( j == 0 ) {
			    state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(1,1), addState[i][0])); 

			    for (int s = 1; s < addState[i].length; s++)
				addState[i][s-1].transitions.add(new FSMTransition(new IntervalDomain(0,1), addState[i][s]));
			    addState[i][addState[i].length-1].transitions.add(new FSMTransition(new IntervalDomain(0,1), state[i+1][0][0]));
			}
			else
			    if ( j != state[i].length - 1) {
				state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(1,1), addState[i][2*j]));
			    }
			    else
				state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(1,1), state[i+1][0][0]));
		    else
			state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(1,1), state[i+1][0][0]));
		    if (j != state[i].length - 1)
			state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(0,0), state[i][j][1]));
		}
		else { 
		    state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(1,1), terminate));
		    if (j != state[i].length - 1)
			state[i][j][0].transitions.add(new FSMTransition(new IntervalDomain(0,0), state[i][j][1]));
		}

		if ( i != state.length - 1) {
		    if ( j != state[i].length - 1 )
			state[i][j][1].transitions.add(new FSMTransition(new IntervalDomain(1,1), state[i][j+1][0]));
		}
		else {
		    if ( j != state[i].length - 1 )
			state[i][j][1].transitions.add(new FSMTransition(new IntervalDomain(1,1), state[i][j+1][0]));
		}
	    }
	}

	terminate.transitions.add(new FSMTransition(new IntervalDomain(0,1), terminate));

	constraints.add(new Regular(g, var));

	return constraints;
    }

    public ArrayList<Constraint> decomposeLT(Store store) {

	if (constraints == null)
	    constraints = new ArrayList<Constraint>();
	else
	    return constraints;

	int sizeToCompare = (x[0].length < x[1].length) ? x[0].length : x[1].length;

	BooleanVar[] b = new BooleanVar[sizeToCompare+1];
	for (int i=0; i < b.length; i++)
	    b[i] = new BooleanVar(store, "_b["+i+"]");

	constraints.add(new XeqC(b[0], 1));

	for (int i=0; i < sizeToCompare; i++) {
	    Constraint c = new Reified(new And(new XlteqY(x[0][i], x[1][i]), new Or(new XltY(x[0][i], x[1][i]), new XeqC(b[i+1], 1))), b[i]);

	    constraints.add(c);
	}
	if (x[0].length < x[1].length)
	    constraints.add(new XeqC(b[sizeToCompare], 1));
	else
	    constraints.add(new XeqC(b[sizeToCompare], 0));

	return constraints;
    }

    public ArrayList<Constraint> decomposeLE(Store store) {

	if (constraints == null)
	    constraints = new ArrayList<Constraint>();
	else
	    return constraints;

	int sizeToCompare = (x[0].length < x[1].length) ? x[0].length : x[1].length;

	BooleanVar[] b = new BooleanVar[sizeToCompare];
	for (int i=0; i < b.length; i++)
	    b[i] = new BooleanVar(store, "_b["+i+"]");

	constraints.add(new XeqC(b[0], 1));

	for (int i=0; i < sizeToCompare; i++) {
	    if (i == sizeToCompare - 1)
		constraints.add( new Reified(new XlteqY(x[0][i], x[1][i]), b[i]) );
	    else
		constraints.add( new Reified(new And(new XlteqY(x[0][i], x[1][i]), new Or(new XltY(x[0][i], x[1][i]), new XeqC(b[i+1], 1))), b[i]) );
	}

	return constraints;
    }

}
