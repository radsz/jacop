/**
 *  MultivariateIntervalNewton.java 
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

import java.util.Arrays;
import java.util.Set;
import java.util.HashSet;
import java.util.HashMap;
import java.util.ArrayList;
import java.util.Stack;

import org.jacop.core.Store;
import org.jacop.util.SimpleHashSet;

import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatVar;

import org.jacop.constraints.Constraint;
//import org.jacop.floats.constraints.PmulQeqR;

/**
 * MultivariateIntervalNewton implements multivariate interval Newton
 * method for solving a system of non linear equations.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class MultivariateIntervalNewton {

    final static boolean debug = false;

    Store store;

    FloatVar[] f;
    FloatVar[] x;
    FloatVar[][] fprime;

    double[] xInit;

    FloatInterval[][] A;
    double[] b;

    HashMap<FloatVar,Double> map;
    Stack<Constraint> eval;

    public MultivariateIntervalNewton(Store store, FloatVar[] f, FloatVar[] x) {

	this.store = store;

	this.f = f;
	this.x = x;

	eval = new Stack<Constraint>();

	Set<FloatVar> vars = new HashSet<FloatVar>();
	for (FloatVar v : x)
	    vars.add(v);

	fprime = new FloatVar[f.length][x.length];
	Derivative.init(store);
	for (int i = 0; i < f.length; i++) 
	    for (int j = 0; j < x.length; j++) {

		if (debug)
		    System.out.println ("Derivative of " + f[i] +" on " + x[j] + " primitive variables = " + vars);

		fprime[i][j] = Derivative.getDerivative(store, f[i], vars, x[j]);

		if (debug)
		    System.out.println ("\t derivate = " + fprime[i][j]);
	    }

    }

    public FloatInterval[]  solve() {

	A = new FloatInterval[fprime.length][];
	for (int i = 0; i < fprime.length; i++) {
	    A[i] = new FloatInterval[fprime[i].length];
	    for (int j = 0; j < fprime[i].length; j++) {
		A[i][j] = new FloatInterval(fprime[i][j].min(), fprime[i][j].max());
	    }
	}

	xInit = new double[x.length];
	for (int i = 0; i < x.length; i++) 
	    xInit[i] = (x[i].max() + x[i].min())/2.0;

	b = values();

	if (debug) {
	    System.out.println ("Middle values for x");
	    for (int i = 0; i < xInit.length; i++) 
		System.out.print (xInit[i] + " ");
	    System.out.println ();

	    System.out.println ("Middle values for f");
	    for (int i = 0; i < b.length; i++) 
		System.out.print (b[i] + ", ");
	    System.out.println ();
	}

	IntervalGaussSeidel igs = new IntervalGaussSeidel(A, b);

	if (debug)
	    System.out.println (igs);
	
	FloatInterval[] v = igs.solve();

	if (v == null)
	    return null;

	FloatInterval[] result = new FloatInterval[v.length];
	for (int i = 0; i < v.length; i++) {
	    FloatIntervalDomain r = FloatDomain.addBounds(v[i].min(), v[i].max(), xInit[i], xInit[i]);
	    result[i] = new FloatInterval(r.min(), r.max());
	}

	return result;

    }

    // computes -f(xInit), RHS of equation for Gauss-Seidler method a
    // little bit tricky since we need to use constraints and their
    // consistency methods to compute the values; therefore playing
    // with store levels...
    double[] values() {

	map = new HashMap<FloatVar,Double>();

	double[] b = new double[xInit.length];

	// need also -f(xInit)
	for (int i = 0; i < xInit.length; i++) 
	    map.put(x[i], xInit[i]);

	for (int i = 0; i < f.length; i++) 
	    b[i] = -value(f[i]);

	// if (debug) {
	//     for (int i = 0; i < b.length; i++) 
	// 	System.out.print (b[i] + ", ");
	//     System.out.println ();
	// }

	return b;
    }

    double value(FloatVar f) {

	if (map.get(f) != null)
	    return map.get(f);
	// else if (f.singleton())
	//     return f.value();

	Constraint c = constraint(f);
	if (c != null)
	    eval.push(c);
	else 
	    if (f.singleton())
		return f.value();

	// if (debug)
	//      System.out.println ("current constraint for variable " + f + " is " + c);

	double result = 0.0;

	if (c instanceof PmulQeqR) {
	    if (f.equals(((PmulQeqR)c).r)) {
		result =  value(((PmulQeqR)c).p) * value(((PmulQeqR)c).q);
	    }
	    else {
		System.out.println ("!!! Anable to compute middle value for " + f + "; + Constraint " + c + " does not define a function for variable\n");
		System.exit(0);
	    }
	}
	else if (c instanceof PmulCeqR) {
	    if (f.equals(((PmulCeqR)c).r))
		result = value(((PmulCeqR)c).p) * ((PmulCeqR)c).c;
	    else {
		System.out.println ("!!! Anable to compute middle value for " + f + "; + Constraint " + c + " does not define a function for variable\n");
		System.exit(0);
	    }
	}
	else if (c instanceof PdivQeqR) {
	    if (f.equals(((PdivQeqR)c).r)) {
		result =  value(((PdivQeqR)c).p) / value(((PdivQeqR)c).q);
	    }
	    else {
		System.out.println ("!!! Anable to compute middle value for " + f + "; + Constraint " + c + " does not define a function for variable\n");
		System.exit(0);
	    }
	}
	else if (c instanceof PplusQeqR) {
	    if (f.equals(((PplusQeqR)c).r))
		result = value(((PplusQeqR)c).p) + value(((PplusQeqR)c).q);
	    else {
		System.out.println ("!!! Anable to compute middle value for " + f + "; + Constraint " + c + " does not define a function for variable\n");
		System.exit(0);
	    }   
	}
	else if (c instanceof PplusCeqR) {
	    if (f.equals(((PplusCeqR)c).r))
		result = value(((PplusCeqR)c).p) + ((PplusCeqR)c).c;
	    else {
		System.out.println ("!!! Anable to compute middle value for " + f + "; + Constraint " + c + " does not define a function for variable\n");
		System.exit(0);
	    }   
	}
	else if (c instanceof PminusQeqR) {
	    if (f.equals(((PminusQeqR)c).r))
		result = value(((PminusQeqR)c).p) - value(((PminusQeqR)c).q);
	    else {
		System.out.println ("!!! Anable to compute middle value for " + f + "; + Constraint " + c + " does not define a function for variable\n");
		System.exit(0);
	    }   
	}
	else if (c instanceof LinearFloat) {

	    FloatVar[] v = ((LinearFloat)c).list;
	    double[] w = ((LinearFloat)c).weights;
	    double sum =  ((LinearFloat)c).sum;

	    FloatVar vOut = null;
	    double wOut =  1000.0;

	    for (int i = 0; i < v.length; i++) {
		if ( ! v[i].equals(f)) 
		    sum -= value(v[i])*w[i];
		else {
		    vOut = v[i];
		    wOut = w[i];
		}
	    }

	    if (vOut != null) 
		result = sum/wOut;
	    else {
		System.out.println ("!!! Anable to compute middle value for " + f + "; + Constraint " + c + " does not define a function for variable\n");
		System.exit(0);
	    }
	}
	else {
	    System.out.println ("!!! Constraint " + c + " is not yet supported in Newtoen method\n");
	    System.exit(0);
	}

	eval.pop();

	// if (debug)
	//     System.out.println ("returns " + result);

	return result;
    }

    Constraint constraint(FloatVar v) {

	ArrayList<Constraint> list = new ArrayList<Constraint>();

	for (int i = 0; i < v.dom().modelConstraints.length; i++) 
	    if  (v.dom().modelConstraints[i] != null)
		for (int j = 0; j < v.dom().modelConstraints[i].length; j++) {
		    if (v.dom().modelConstraints[i][j] != null) {

			Constraint c = v.dom().modelConstraints[i][j];

			if ( eval.search(c) == -1 ) {
			    if ( Derivative.derivateConstraints.contains(c))
				continue;

			    if (!list.contains(c))
				list.add(c);
			}
		    }
		}

	// if (debug)
	//     System.out.println ("Possible constraints for variable " + v + " are " + list);

	Constraint c;
	if (list.size() == 1)
	    c = list.get(0);
	else
	    c = Derivative.resolveConstraint(v, list);

	return c;

    }

    boolean contains(FloatVar[] fs, FloatVar r) {

	for (FloatVar f : fs) 
	    if (f.equals(r))
		return true;

	return false;
    }

    public String toString() {
	String s = "MultivariateIntervalNewton:\n";
	
	s += Arrays.asList(f) + "\n";
	s += Arrays.asList(x) + "\n";
	for (int i = 0; i < fprime.length; i++) 
	    for (int j = 0; j < fprime[i].length; j++) 
		s += "f"+i+"/d"+x[j]+" = " +fprime[i][j] + "\n";
	// for (int i = 0; i < xInit.length; i++)
	//     s += xInit[i] + ", ";
	s += "\n";

	return s;
    }
}
