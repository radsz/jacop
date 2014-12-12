/**
 *  Linear.java 
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

package org.jacop.floats.constraints.linear;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;

import org.jacop.core.IntDomain;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.floats.constraints.PmulCeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.linear.BoundsVarValue;
import org.jacop.util.SimpleHashSet;

/**
 * Linear constraint implements the weighted summation over several
 * Variable's . It provides the weighted sum from all Variable's on the list.
 * The weights must be positive integers.
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

public class Linear extends PrimitiveConstraint {
    Store store;
    static int counter = 1;

    /**
     * Defines relations
     */
    public final static byte eq=0, lt=1, le=2, ne=3, gt=4, ge=5;

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

    HashMap<FloatVar, VariableNode> varMap = new HashMap<FloatVar, VariableNode>();

    // LinkedHashSet<FloatVar> variableQueue = new LinkedHashSet<FloatVar>();
    SimpleHashSet<FloatVar> variableQueue = new SimpleHashSet<FloatVar>();

    boolean reified = true;

    BTree linearTree;

    VariableNode[] sortedVarNodes;

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
    public Linear(Store store, FloatVar[] list, double[] weights, String rel, double sum) {

	this.relationType = relation(rel);
	commonInitialization(store, list, weights, sum);
    }
	
    private void commonInitialization(Store store, FloatVar[] list, double[] weights, double sum) {
	this.store=store;
	queueIndex = 1;

	assert ( list.length == weights.length ) : "\nLength of two vectors different in Linear";

	numberArgs = (short) (list.length);

	numberId = counter++;

	this.sum = sum;

	HashMap<FloatVar, Double> parameters = new HashMap<FloatVar, Double>();

	for (int i = 0; i < list.length; i++) {

	    assert (list[i] != null) : i + "-th element of list in Linear constraint is null";
			
	    if (weights[i] != 0) {
		// This causes problem for several examples...
		if (list[i].singleton()) 
		    this.sum -= (list[i].value() * weights[i]);
		else
		    if (parameters.get(list[i]) != null) {
			// variable ordered in the scope of the Linear constraint.
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

	int k = 0;
	for (FloatVar var : parameters.keySet()) {
	    this.list[k] = var;
	    this.weights[k] = parameters.get(var);
	    k++;
	}


	if  (this.list.length == 0) {

	    this.list = new FloatVar[2];
	    this.weights = new double[2];
	    this.list[0] = new FloatVar(store, 0,0);
	    this.weights[0] = 1;
	    this.list[1] = new FloatVar(store, 0,0);
	    this.weights[1] = 1;
	    
	}

	if ( this.list.length == 1) {
	    // System.out.println("% Warrning: List of length 1 in LinearFloat(["+this.list[0].id()+"], ["+this.weights[0] +"], "+rel2String()+", " + this.sum+")");

	    FloatVar v = this.list[0];
	    double w = this.weights[0];
	    this.list = new FloatVar[2];
	    this.weights = new double[2];
	    this.list[0] = v;
	    this.weights[0] = w;
	    this.list[1] = new FloatVar(store, 0,0);
	    this.weights[1] = 1;

	}

	VariableNode[] leafNodes = new VariableNode[this.list.length];

	for (int i = 0; i < this.list.length; i++) {

	    if (this.weights[i] == 1)
	    	leafNodes[i] = new VarNode(store, this.list[i]);
	    else
		leafNodes[i] = new VarWeightNode(store, this.list[i], this.weights[i]);
	    leafNodes[i].rel = relationType;

	    varMap.put(this.list[i], leafNodes[i]);

	}

	java.util.Arrays.sort(leafNodes, new VarWeightComparator<VariableNode>());
	sortedVarNodes = leafNodes;
	// System.out.println (java.util.Arrays.asList(leafNodes));


	RootBNode root = buildBinaryTree(leafNodes);
	linearTree = new BTree(root);

	// System.out.println(this);
	// System.out.println (linearTree);

	checkForOverflow();

    }

    RootBNode buildBinaryTree(BinaryNode[] nodes) {

	BinaryNode[] nextLevelNodes = new BinaryNode[nodes.length/2 + nodes.length % 2];
	// System.out.println ("next level length = " + nextLevelNodes.length);

	if (nodes.length > 1) {
	    for (int i=0; i<nodes.length-1; i += 2) {
		BinaryNode parent;

		if (nodes.length == 2) 
		    parent = new RootBNode(store, FloatDomain.MinFloat, FloatDomain.MaxFloat);
		else 
		    parent = new BNode(store, FloatDomain.MinFloat, FloatDomain.MaxFloat);

		parent.left = nodes[i];
		parent.right = nodes[i+1];

		nodes[i].sibling = nodes[i+1];
		nodes[i+1].sibling = nodes[i];

		nodes[i].parent = parent;
		nodes[i+1].parent = parent;

		nextLevelNodes[i/2] = parent;

	    }
	    if (nodes.length % 2 == 1) {
		nextLevelNodes[nextLevelNodes.length-1] = nextLevelNodes[0];
		nextLevelNodes[0] = nodes[nodes.length-1];
	    }

	    return buildBinaryTree(nextLevelNodes);
	}
	else {
	    // root node
	    ((RootBNode)nodes[0]).val = this.sum;
	    ((RootBNode)nodes[0]).rel = relationType;

	    return (RootBNode)nodes[0];
	}
    }


    /**
     * It constructs the constraint Linear. 
     * @param variables variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted variables.
     */
    public Linear(Store store, ArrayList<? extends FloatVar> variables,
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

	ArrayList<Var> variables = new ArrayList<Var>(list.length);

	for (Var v : list)
	    variables.add(v);

	return variables;
    }


    @Override
    public void consistency(Store store) {

	// compute for original relation
	linearTree.root.rel = relationType;

	pruneRelation(store);

	if (relationType != eq)
	    if (satisfied()) 
		removeConstraint();

    }

    @Override
    public void notConsistency(Store store) {

	// compute for negated original relation
	linearTree.root.rel = negRel[relationType];

	pruneRelation(store);

	if (negRel[relationType] != eq)
	    if (notSatisfied()) 
		removeConstraint();
		
    }

    private void pruneRelation(Store store) {

	while (!variableQueue.isEmpty()) {
	    // propagate changes in FDV's and prune

	    FloatVar v = variableQueue.removeFirst();
	    VariableNode n = varMap.get(v);

	    n.propagateAndPrune();

	}   

    }

    void propagate(SimpleHashSet<FloatVar> fdvs) {

	while (! fdvs.isEmpty() ) {

	    FloatVar v = fdvs.removeFirst();
	    VariableNode n = varMap.get(v);

	    n.propagate();

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

	reified = false;

	for (Var v : list) {
	    v.putModelConstraint(this, getConsistencyPruningEvent(v));
	    queueVariable(store.level, v);
	}

	store.addChanged(this);
	store.countConstraint();
    }


    @Override
    public void queueVariable(int level, Var var) {
	variableQueue.add((FloatVar)var);

    }

    @Override
	public void removeConstraint() {
	for (Var v : list)
	    v.removeConstraint(this);
    }

    @Override
	public boolean satisfied() {

	if (reified) 
	    propagate(variableQueue);

	return entailed(relationType);
    }

    @Override
	public boolean notSatisfied() {

	if (reified)
	    propagate(variableQueue);

	return entailed(negRel[relationType]);
    }

    private boolean entailed(byte rel) {

	BoundsVarValue b = (BoundsVarValue)linearTree.root.bound.value();

	switch (rel) {
	case eq : 
	    FloatInterval rootInterval = new FloatInterval(b.lb, b.ub);

	    if (rootInterval.singleton() && b.lb <= sum && sum <= b.ub)
		return true;
	    break;
	case lt : 
	    if (b.ub < sum)
		return true;
	    break;
	case le : 
	    if (b.ub <= sum)
		return true;
	    break;
	case ne : 
	    if (b.lb > sum || b.ub < sum)
		return true;
	    break;
	case gt : 
	    if (b.lb > sum)
		return true;
	    break;
	case ge : 
	    if (b.lb >= sum)
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
	    System.err.println ("Wrong relation symbol in Linear constraint " + r + "; assumed ==");
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
	result.append(" : Linear( [ ");

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

    /*
    // uncomment registration in commonInitialization
    @Override
    public void removeLevelLate(int level) {
	// System.out.println ("Backtrack, queue = " + variableQueue);

	// variableQueue.clear();

	if (variableQueue.size() > 0)
	    variableQueue = new SimpleHashSet<IntVar>();

    }
    */

    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    for (Var v : list) v.weight++;
	}
    }

    class VarWeightComparator<T extends VariableNode> implements java.util.Comparator<T> {

	VarWeightComparator() {
	}

	public int compare(T o1, T o2) {
	    double diff_o1 = 0, diff_o2 = 0;

	    if (o1 instanceof VarNode)
		diff_o1 = o1.max() - o1.min();
	    else
		diff_o1 = (o1.max() - o1.min()) * ((VarWeightNode)o1).weight;

	    if (o2 instanceof VarNode)
		diff_o2 = o2.max() - o2.min();
	    else
		diff_o2 = (o2.max() - o2.min()) * ((VarWeightNode)o2).weight;
	    
	    return (int)(diff_o2 - diff_o1);
	}
    }

}
