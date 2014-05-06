/**
 *  LinearFloat.java 
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

import java.util.ArrayList;
import java.util.HashMap;

import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.constraints.PrimitiveConstraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatInterval;

/**
 * LinearFloat constraint implements the weighted summation over several
 * Variable's . It provides the weighted sum from all Variable's on the list.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.1
 */

public class LinearFloat extends PrimitiveConstraint {
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
    public FloatVar list[];

    /**
     * It specifies a list of weights associated with the variables being summed.
     */
    public double weights[];

    /**
     * It specifies variable for the overall sum. 
     */
    public double sum;

    double lMin;

    double lMax;

    double[] lMinArray;

    double[] lMaxArray;

    HashMap<Var, Integer> positionMaping;

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
    public LinearFloat(Store store, FloatVar[] list, double[] weights, String rel, double sum) {

	commonInitialization(store, list, weights, sum);
	this.relationType = relation(rel);

    }
	
    private void commonInitialization(Store store, FloatVar[] list, double[] weights, double sum) {
	this.store=store;
	queueIndex = 1;

	assert ( list.length == weights.length ) : "\nLength of two vectors different in LinearFloat";

	numberArgs = (short) (list.length + 1);

	numberId = counter++;

	this.sum = sum;

	HashMap<FloatVar, Double> parameters = new HashMap<FloatVar, Double>();

	for (int i = 0; i < list.length; i++) {

	    assert (list[i] != null) : i + "-th element of list in LinearFloat constraint is null";
			
	    if (weights[i] != 0) {
		// if (list[i].singleton()) 
		//     this.sum -= list[i].value() * weights[i];
		// else
		    if (parameters.get(list[i]) != null) {
			// variable ordered in the scope of the LinearFloat constraint.
			Double coeff = parameters.get(list[i]);
			Double sumOfCoeff = coeff + weights[i];
			parameters.put(list[i], sumOfCoeff);
		    }
		    else
			parameters.put(list[i], weights[i]);

	    }
	}

	this.list = new FloatVar[parameters.size()];
	this.weights = new double[parameters.size()];

	int i = 0;
	for (FloatVar var : parameters.keySet()) {
	    this.list[i] = var;
	    this.weights[i] = parameters.get(var);
	    i++;
	}

	int capacity = list.length*4/3+1;
	if (capacity < 16)
	    capacity = 16;
	positionMaping = new HashMap<Var, Integer>(capacity);

	// store.registerRemoveLevelLateListener(this);

	lMinArray = new double[list.length];
	lMaxArray = new double[list.length];
	lMin = 0.0;
	lMax = 0.0;

	// recomputeLHSBounds();

	for (int j = 0; j < this.list.length; j++) {

	    assert (positionMaping.get(this.list[j]) == null) : "The variable occurs twice in the list, not able to make a maping from the variable to its list index.";

	    positionMaping.put(this.list[j], j);
	    // queueVariable(store.level, this.list[j]);

			
	}

	checkForOverflow();

    }

    /**
     * It constructs the constraint LinearFloat. 
     * @param variables variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted variables.
     */
    public LinearFloat(Store store, ArrayList<? extends FloatVar> variables,
		       ArrayList<Double> weights, String rel, double sum) {

	double[] w = new double[weights.size()];
	for (int i = 0; i < weights.size(); i++)
	    w[i] = weights.get(i);
		
	commonInitialization(store, variables.toArray(new FloatVar[variables.size()]),
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

	do {

	    store.propagationHasOccurred = false;

	    for (int i = 0; i < list.length; i++) {

		FloatVar v = list[i];

		computeBounds(i);
		FloatIntervalDomain d = FloatDomain.divBounds(lMin, lMax, weights[i], weights[i]);
		double divMin = d.min();
		double divMax = d.max();

		switch (rel) {
		case eq : //============================================= 

		    if (divMin > divMax) 
			throw Store.failException;

		    v.domain.in(store.level, v, divMin, divMax);

		    break;
		case lt : //=============================================

		    if (weights[i] < 0) {
			v.domain.inMin(store.level, v, FloatDomain.next(divMin));
		    }
		    else {
			v.domain.inMax(store.level, v, FloatDomain.previous(divMax));
		    }
		    break;
		case le : //=============================================

		    if (weights[i] < 0) {
			v.domain.inMin(store.level, v, divMin);
		    }
		    else {
			v.domain.inMax(store.level, v, divMax);
		    }
		    break;
		case ne : //=============================================

		    FloatInterval fi = new FloatInterval(divMin, divMax);

		    if ( fi.singleton() ) 
			v.domain.inComplement(store.level, v, divMin, divMax);
		    break;
		case gt : //=============================================

		    if (weights[i] < 0) {
			v.domain.inMax(store.level, v, FloatDomain.previous(divMax));
		    }
		    else {
			v.domain.inMin(store.level, v, FloatDomain.next(divMin));
		    }
		    break;
		case ge : //=============================================

		    if (weights[i] < 0) {
			v.domain.inMax(store.level, v, divMax);
		    }
		    else {
			v.domain.inMin(store.level, v, divMin);
		    }
		    break;
		}
	    }

	} while (store.propagationHasOccurred);
    }

    void recomputeLHSBounds() {

	lMin = 0.0;
	lMax = 0.0;
	for (int i=0; i<list.length; i++) {

	    FloatDomain listDom = list[i].dom();

	    FloatIntervalDomain mul = FloatDomain.mulBounds(listDom.min(), listDom.max(), weights[i], weights[i]);
	    lMinArray[i] = mul.min();
	    lMaxArray[i] = mul.max();

	    if (lMinArray[i] != 0.0)
		lMin = FloatDomain.addBounds(lMin, lMin, lMinArray[i], lMinArray[i]).min();
	    if (lMaxArray[i] != 0.0)
		lMax = FloatDomain.addBounds(lMax, lMax, lMaxArray[i], lMaxArray[i]).max();
	}

	// System.out.println (this + "\n" + lMin+".."+max);

    }

    void computeBounds(int index) {

	double min = sum;
	double max = sum;
	for (int i=0; i<list.length; i++) {

	    if ( i != index) {
		FloatDomain listDom = list[i].dom();

		FloatIntervalDomain mul = FloatDomain.mulBounds(listDom.min(), listDom.max(), weights[i], weights[i]);
		double min_i = mul.min();
		double max_i = mul.max();

		if (max_i != 0.0)
		    min = FloatDomain.subBounds(min, min, max_i, max_i).min();
		if (min_i != 0.0)
		    max = FloatDomain.subBounds(max, max, min_i, min_i).max();
	    }
	}

	lMin = min;
	lMax = max;

	// System.out.println (this + "\n" + min+".."+max);

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
    public void removeConstraint() {
	for (Var v : list)
	    v.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {

	recomputeLHSBounds();

	return entailed(relationType);

    }

    @Override
    public boolean notSatisfied() {

	recomputeLHSBounds();

	return entailed(negRel[relationType]);

    }

    private boolean entailed(byte rel) {
	    
	switch (rel) {
	case eq : 
	    FloatInterval fi_lMinlMax = new FloatInterval(lMin, lMax);

	    if (fi_lMinlMax.singleton() && lMin <= sum && sum <= lMax)
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

    void checkForOverflow() {

	double sumMin=0, sumMax=0;
	for (int i=0; i<list.length; i++) {
	    double n1 = list[i].min() * weights[i];
	    double n2 = list[i].max() * weights[i];
	    if (Double.isInfinite(n1) || Double.isInfinite(n2))
		throw new ArithmeticException("Overflow occurred in floating point operations");

	    if (n1 <= n2) {
		sumMin += n1;
		sumMax += n2;
	    }
	    else {
		sumMin += n2;
		sumMax += n1;
	    }

	    if (Double.isInfinite(sumMin) || Double.isInfinite(sumMax))
		throw new ArithmeticException("Overflow occurred in floating point operations");

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
	    System.err.println ("Wrong relation symbol in LinearFloat constraint " + r + "; assumed ==");
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
	result.append(" : LinearFloat( [ ");

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

    public FloatVar derivative(Store store, FloatVar f, java.util.Set<FloatVar> vars, FloatVar x) {

	// System.out.println ("FloatLinear of " + f + " on " + x);

	int fIndex = 0;
	while (list[fIndex] != f)
	    fIndex++;

	if (fIndex == list.length) {
	    System.out.println ("Wrong variable in derivative of " + this);
	    System.exit(0);
	}

	double w = weights[fIndex];
	FloatVar[] df = new FloatVar[list.length];
	double[] ww = new double[list.length];
	FloatVar v = null;

	for (int i = 0; i < list.length; i++) {
	    if ( i != fIndex) {
		df[i] = Derivative.getDerivative(store, list[i], vars, x);

		// System.out.println ("derivate of " + list[i] + " = " + df[i]);

		ww[i] = weights[i]/(-weights[fIndex]);
	    }
	    else {
		v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
		df[i] = v;
		ww[i] = -1.0;
	    }
	}

	org.jacop.constraints.Constraint c = new LinearFloat(store, df, ww, "==", 0.0);
	Derivative.poseDerivativeConstraint(c);

	// System.out.println ("Derivative of " + f + " over " + x + " is " + c);

	return v;
   }

}
