/**
 *  Derivative.java 
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


package org.jacop.floats.constraints;

import java.util.Set;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Stack;
import java.util.ArrayList;

import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;
import org.jacop.constraints.Constraint;

/**
 * Derivative for float constraints
 * 
 * The derivative of f with respect to x
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Derivative {

    public final static double MIN_FLOAT = -1e+150;
    public final static double MAX_FLOAT =  1e+150;

    static Stack<Constraint> eval;

    public static Set<Constraint> derivateConstraints;

    static HashMap<FloatVar, Constraint> definitionConstraint;

    static Store store;

    // static FloatVar zero;
    // static FloatVar one;

    public static void init(Store s) {	
	store = s;

	// zero = new FloatVar(store, 0.0, 0.0);
	// one  = new FloatVar(store, 1.0, 1.0);

	derivateConstraints = new HashSet<Constraint>();
	eval = new Stack<Constraint>();
	definitionConstraint = new HashMap<FloatVar, Constraint>();
    }

    public final static FloatVar getDerivative(Store store, FloatVar f, Set<FloatVar> vars, FloatVar x) {

	// System.out.println ("Var = " + f);

	ArrayList<Constraint> constraints = new ArrayList<Constraint>();

	if (f == x)
	    return new FloatVar(store, 1.0, 1.0);
	else if (vars.contains(f))
	    return new FloatVar(store, 0.0, 0.0);
	else
	    for (int i = 0; i < f.dom().modelConstraints.length; i++) 
		if  (f.dom().modelConstraints[i] != null)
		    for (int j = 0; j < f.dom().modelConstraints[i].length; j++) {
			if (f.dom().modelConstraints[i][j] != null) {

			    Constraint currentConstraint = f.dom().modelConstraints[i][j];
			    if ( eval.search(currentConstraint) == -1 ) {
				
				// System.out.println ("["+i+"]["+j+"]" + f.dom().modelConstraints[i][j]);

				if ( ! derivateConstraints.contains(currentConstraint))
				    constraints.add(currentConstraint);

			    }
			}

		    }

	if (constraints.size() == 1) {

	    Constraint currentConstraint = constraints.get(0);

	    // System.out.println ("Evaluate " + currentConstraint);

	    eval.push(currentConstraint);
	    FloatVar v = currentConstraint.derivative(store, f, vars, x);
	    eval.pop();

	    return v;
	}

	else if (constraints.size() == 0 && f.singleton())
	    return new FloatVar(store, 0.0, 0.0);
	else {

	    Constraint c = resolveConstraint(f, constraints);
	    if ( c != null) {
		eval.push(c);
		FloatVar v = c.derivative(store, f, vars, x);
		eval.pop();

		return v;
	    }

	    System.out.println ("!!! " + constraints.size() + " constraints define a function for variable " + f + "\n" + constraints);
	    System.exit(0);
	    return null;
	}
    }

    final static void poseDerivativeConstraint(Constraint c) {

	// System.out.println (c);

	store.impose(c);

	derivateConstraints.add(c);
    }

    static Constraint resolveConstraint(FloatVar f, ArrayList<Constraint> cs) {

	// resolve based on definitions given by a programmer
	Constraint c =  definitionConstraint.get(f);
	
	// if there is no definition use heuristic to resolve it
	// basically we look for a constraint on a list of possibel constraints
	// that has output equal variable defining the function
	ArrayList<Constraint> resolved = new ArrayList<Constraint>();
	if (c == null)
	    for (Constraint cc : cs) {
		if (cc instanceof PmulQeqR) {
		    if ( f.equals(((PmulQeqR)cc).r) )
			resolved.add(cc);
		}
		if (cc instanceof PmulCeqR) {
		    if ( f.equals(((PmulCeqR)cc).r) )
			resolved.add(cc);
		}
		else if (cc instanceof PplusQeqR) {
		    if ( f.equals(((PplusQeqR)cc).r) )
			resolved.add(cc);
		}
		else if (cc instanceof PplusCeqR) {
		    if ( f.equals(((PplusCeqR)cc).r) )
			resolved.add(cc);
		}
		else if (cc instanceof PminusQeqR) {
		    if ( f.equals(((PminusQeqR)cc).p) )
			resolved.add(cc);
		}
		else if (cc instanceof PdivQeqR) {
		    if ( f.equals(((PdivQeqR)cc).p) )
			resolved.add(cc);
		}
		else if (cc instanceof LinearFloat) {
		    if ( ((LinearFloat)cc).relationType == LinearFloat.eq) {
			double[] ws = ((LinearFloat)cc).weights;		    
			FloatVar[] ls = ((LinearFloat)cc).list;
			for (int i=0; i<ls.length; i++) {
			    if (f.equals(ls[i]) && ws[i] == -1.0)
				resolved.add(cc);
			}
		    }
		}
		else if (c instanceof EquationSystem)
		    ;
	    }

	if (resolved.size() == 1)
	    return resolved.get(0);

	return c;
    }

    public static void defineConstraint(FloatVar f, Constraint c) {
	definitionConstraint.put(f, c);
    }

    public final static int numberDerivativeConstraints() {
	return derivateConstraints.size();
    }

    public final static Set<Constraint> derivativeConstraints() {
	return derivateConstraints;
    }

}
