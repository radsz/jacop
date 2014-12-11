/**
 *  Constraints.java 
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
package org.jacop.fz;

import java.util.ArrayList;

import org.jacop.constraints.*;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.BooleanVar;
import org.jacop.core.BoundDomain;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.ValueEnumeration;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.*;

import org.jacop.set.constraints.AdiffBeqC;
import org.jacop.set.constraints.AinB;
import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.set.constraints.AunionBeqC;
import org.jacop.set.constraints.CardAeqX;
import org.jacop.set.constraints.EinA;
import org.jacop.set.constraints.ElementSet;
import org.jacop.set.constraints.Lex;
import org.jacop.set.constraints.XinA;
import org.jacop.set.constraints.AdisjointB;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import org.jacop.util.fsm.FSM;
import org.jacop.util.fsm.FSMState;
import org.jacop.util.fsm.FSMTransition;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.NetworkFlow;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.constraints.geost.*;

/**
 * 
 * The part of the parser responsible for parsing constraints. 
 * 
 * @author Krzysztof Kuchcinski 
 *
 */
public class Constraints implements ParserTreeConstants {

    Tables dictionary;
    Store store;
    String p;
    IntVar zero, one;
    final static int eq=0, ne=1, lt=2, gt=3, le=4, ge=5;
    boolean intPresent = true;
    boolean floatPresent = true;

    // =========== Annotations ===========
    boolean boundsConsistency = true, domainConsistency = false;
    // defines_var
    IntVar definedVar = null;

    ArrayList<IntVar[]> parameterListForAlldistincts = new ArrayList<IntVar[]>();
    ArrayList<Constraint> delayedConstraints = new ArrayList<Constraint>();

//     boolean storeLevelIncreased=false;

    final static boolean debug = false;

    /**
     * It creates an object to parse the constraint part of the flatzinc file.
     * @param store the constraint store in which the constraints are being created.
     */
    public Constraints(Store store) {
	this.store = store;
// 	this.zero = new Variable(store, "zero", 0,0);
// 	this.one = new Variable(store, "one", 1,1);
    }

    // not needed any longer since it is not supported by flatzinc ;)
//     void generateVarConstraint(SimpleNode constraintWithAnnotations, Tables table) throws FailException {

// 	dictionary = table;
//  	this.zero = table.zero; 
// 	this.one = table.one; 

// //   	constraintWithAnnotations.dump("");

//  	SimpleNode node = (SimpleNode)constraintWithAnnotations.jjtGetChild(0);

//  //	node.dump("");

// 	// constraint can be a variable of array access
// 	// not very usefull but possible
// 	if ( ((ASTConstElem)node).getName() == null) {
// 	    SimpleNode child = (SimpleNode)node.jjtGetChild(0);
// 	    if ( ((ASTVariableExpr)child).getIdent() != null) {
// 		IntVar x = dictionary.getVariable(((ASTVariableExpr)child).getIdent());
// 		if (x != null) {
// 		    Constraint c = new XeqC(x, 1);
// 		    pose(c);
// 		}
// 		else {
// 		    System.err.println("ERROR: Trying to pose variable constraint for "+((ASTVariableExpr)child).getIdent());
// 		    System.exit(0);
// 		}
// 	    }
// 	    else if (((ASTVariableExpr)child).getArrayAccess() != null) {
// 		ArrayAccess aa = ((ASTVariableExpr)child).getArrayAccess();
// 		if (aa != null) {
// 		    Constraint c = new XeqC(dictionary.getVariableArray(aa.getIdent())[aa.getIndex()], 1);
// 		    pose(c);
// 		}
// 		else {
// 		    System.err.println("ERROR: Trying to pose variable constraint for array"+((ASTVariableExpr)child).getArrayAccess());
// 		    System.exit(0);
// 		}		
// 	    }
// 	}
//     }

    void generateConstraints(SimpleNode constraintWithAnnotations, Tables table) throws FailException {

// 	if (!storeLevelIncreased) {
// 	    System.out.println("1. Level="+store.level);
// 	    store.setLevel(store.level + 1);
// 	    storeLevelIncreased = true;
// 	    System.out.println("2. Level="+store.level);
// 	}

	if (debug)
	    constraintWithAnnotations.dump("");

	// default consistency - bounds
 	boundsConsistency = true; 
 	domainConsistency = false;
	definedVar = null;

	dictionary = table;
 	this.zero = table.zero; 
	this.one = table.one; 

	int numberChildren = constraintWithAnnotations.jjtGetNumChildren();
// 	System.out.println ("numberChildren = "+numberChildren);
	if (numberChildren > 1 )
	    parseAnnotations(constraintWithAnnotations);

	SimpleNode node = (SimpleNode)constraintWithAnnotations.jjtGetChild(0);

//  	node.dump("=> ");

	// Predicates
	if (node.getId() == JJTCONSTELEM) {

	    p = ((ASTConstElem)node).getName();

	    if (p.startsWith("int2float")) {

		ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		pose(new XeqP(getVariable(p1), getFloatVariable(p2)));
	    }

	    else if (p.startsWith("float_") ) {
		int operation = comparisonPredicate(p, 6);

		// node.dump("");
		// System.out.println(p + " op = " + operation);

		// float_eq*, float_ne*, float_lt*, float_gt*, float_le*, and float_ge*
		if ( operation != -1) {
		    float_comparison(operation, node, 8);
		}

		// float_lin_* (eq, ne, lt, gt, le, ge)
		else if (p.startsWith("lin_", 6)) {
		    operation = comparisonPredicate(p, 10);
		    float_lin_relation(operation, node);
		} 

		else if (p.startsWith("plus", 6)) {

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    if (p1.getType() == 5) {// p1 int
		    	pose(new PplusCeqR(getFloatVariable(p2), getFloat(p1), getFloatVariable(p3)));
		    }
		    else if (p2.getType() == 5) {// p2 int
		    	pose(new PplusCeqR(getFloatVariable(p1), getFloat(p2), getFloatVariable(p3)));
		    }
		    else
			pose(new PplusQeqR(getFloatVariable(p1), getFloatVariable(p2), getFloatVariable(p3)));

		} else if (p.startsWith("times", 6)) {

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    if (p1.getType() == 5) {// p1 float
			pose(new PmulCeqR(getFloatVariable(p2), getFloat(p1), getFloatVariable(p3)));
		    }
		    else if (p2.getType() == 5) {// p2 float
			pose(new PmulCeqR(getFloatVariable(p1), getFloat(p2), getFloatVariable(p3)));
		    }
		    else
			pose(new PmulQeqR(getFloatVariable(p1), getFloatVariable(p2), getFloatVariable(p3)));

		} else if (p.startsWith("div", 6)) {

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    pose(new PdivQeqR(getFloatVariable(p1), getFloatVariable(p2), getFloatVariable(p3)));
		}
		else if (p.startsWith("abs", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new AbsPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("sqrt", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new SqrtPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("sin", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new SinPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("cos", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new CosPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("asin", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new AsinPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("acos", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new AcosPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("tan", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new TanPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("atan", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new AtanPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("exp", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new ExpPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("ln", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    pose(new LnPeqR(getFloatVariable(p1), getFloatVariable(p2)));
		}
		else if (p.startsWith("min", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    FloatVar v1 = getFloatVariable(p1);
		    FloatVar v2 = getFloatVariable(p2);
		    FloatVar v3 = getFloatVariable(p3);

		    pose(new org.jacop.floats.constraints.Min(new FloatVar[] {v1, v2}, v3));
		    // 1.
		    // pose(new IfThenElse(new PlteqQ(v1,v2), new PeqQ(v1,v3), new PeqQ(v2,v3)));
		    // 2.
		    // pose(new IfThen(new PltQ(v1,v2), new PeqQ(v1,v3)));
		    // pose(new IfThen(new PltQ(v2,v1), new PeqQ(v2,v3)));
		}
		else if (p.startsWith("max", 6)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    FloatVar v1 = getFloatVariable(p1);
		    FloatVar v2 = getFloatVariable(p2);
		    FloatVar v3 = getFloatVariable(p3);

		    pose(new org.jacop.floats.constraints.Max(new FloatVar[] {v1, v2}, v3));

		    // 1.
		    pose(new IfThenElse(new PltQ(v2,v1), new PeqQ(v1,v3), new PeqQ(v2,v3)));
		    // 2.
		    // pose(new IfThen(new PltQ(v2,v1), new PeqQ(v1,v3)));
		    // pose(new IfThen(new PltQ(v1,v2), new PeqQ(v2,v3)));
		}
		else {
		    System.err.println("%% ERROR: JaCoP does not implement this constraints on floats");
		    System.exit(0);
		}

	    }
	    // int_* predicates
	    else if (p.startsWith("int_") ) {
		int operation = comparisonPredicate(p, 4);
		// 	    System.out.println(p + " op = " + operation);

		if (p.startsWith("negate", 4)) {
		    int_negate(node);
		}

		// int_eq*, int_ne*, int_lt*, int_gt*, int_le*, and int_ge*
		else if ( operation != -1) {
		    int_comparison(operation, node, 6);
		}

		// int_lin_* (eq, ne, lt, gt, le, ge)
		else if (p.startsWith("lin_", 4)) {
		    operation = comparisonPredicate(p, 8);
		    int_lin_relation(operation, node);
		}

		else if (p.startsWith("plus", 4)) {

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    if (p1.getType() == 0) {// p1 int
			pose(new XplusCeqZ(getVariable(p2), getInt(p1), getVariable(p3)));
		    }
		    else if (p2.getType() == 0) {// p2 int
			pose(new XplusCeqZ(getVariable(p1), getInt(p2), getVariable(p3)));
		    }
		    else if (p3.getType() == 0) {// p3 int
			pose(new XplusYeqC(getVariable(p1), getVariable(p2), getInt(p3)));
		    }
		    else
			pose(new XplusYeqZ(getVariable(p1), getVariable(p2), getVariable(p3)));
		}

		else if (p.startsWith("minus", 4)) {
		    // p1 - p2 = p3 <=> p2 + p3 = p1
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    if (p2.getType() == 0) {// p2 int
			pose(new XplusCeqZ(getVariable(p3), getInt(p2), getVariable(p1)));
		    }
		    else if (p3.getType() == 0) {// p3 int
			pose(new XplusCeqZ(getVariable(p2), getInt(p3), getVariable(p1)));
		    }
		    else if (p3.getType() == 0) {// p1 int
			pose(new XplusYeqC(getVariable(p2), getVariable(p3), getInt(p1)));
		    }
		    else
			pose(new XplusYeqZ(getVariable(p2), getVariable(p3), getVariable(p1)));
		}
		else if (p.startsWith("times", 4)) {
		    // 		    node.dump("");

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    if (p1.getType() == 0) {// p1 int
			pose(new XmulCeqZ(getVariable(p2), getInt(p1), getVariable(p3)));
		    }
		    else if (p2.getType() == 0) {// p2 int
			pose(new XmulCeqZ(getVariable(p1), getInt(p2), getVariable(p3)));
		    }
		    else if (p3.getType() == 0) {// p3 int
			pose(new XmulYeqC(getVariable(p1), getVariable(p2), getInt(p3)));
		    }
		    else
			pose(new XmulYeqZ(getVariable(p1), getVariable(p2), getVariable(p3)));
		}
		else if (p.startsWith("div", 4)) {
		    // p1/p2 = p3 <=> p2 * p3 = p1
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);
		    IntVar v3 = getVariable(p3);

		    pose(new XdivYeqZ(v1, v2, v3));

// 		    Variable r = new Variable(store, IntDomain.MinInt, IntDomain.MaxInt);
//  		    Variable t = new Variable(store, IntDomain.MinInt, IntDomain.MaxInt);

// 		    pose(new XplusYeqZ(r, t, v1));

// 		    // follows new flatzinc standard; reminder has the same sign as the first argument
//  		    Variable absV2 = new Variable(store, 0, IntDomain.MaxInt);
//  		    Variable minusAbsV2 = new Variable(store, IntDomain.MinInt, 0);
// 		    pose(new AbsXeqY(v2, absV2));
// 		    pose(new XplusYeqC(minusAbsV2, absV2, 0));
//  		    pose(new IfThen(new XgtC(v1, 0), new And(new XltY(r, absV2), new XgteqC(r, 0))));
//   		    pose(new IfThen(new XltC(v1, 0), new And(new XgtY(r, minusAbsV2), new XlteqC(r, 0))));

// 		    // pose(new Eq(new XgtC(v2, 0), new And(new XltY(r, v2), new XgteqC(r, 0))));
// 		    // pose(new Eq(new XltC(v2, 0), new And(new XgtY(r, v2), new XlteqC(r, 0))));

// 		    pose(new XmulYeqZ(v2, v3, t));
		}
		else if (p.startsWith("mod", 4)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);
		    IntVar v3 = getVariable(p3);

		    pose(new XmodYeqZ(v1, v2, v3));

// 		    Variable t1 = new Variable(store, IntDomain.MinInt, IntDomain.MaxInt);
// 		    Variable t2 = new Variable(store, IntDomain.MinInt, IntDomain.MaxInt);

// 		    pose(new XplusYeqZ(t2, v3, v1)); 
// 		    // follows new flatzinc standard; reminder has the same sign as the first argument
//  		    Variable absV2 = new Variable(store, 0, IntDomain.MaxInt);
//  		    Variable minusAbsV2 = new Variable(store, IntDomain.MinInt, 0);
// 		    pose(new AbsXeqY(v2, absV2));
// 		    pose(new XplusYeqC(minusAbsV2, absV2, 0));
//  		    pose(new IfThen(new XgtC(v1, 0), new And(new XltY(v3, absV2), new XgteqC(v3, 0))));
//  		    pose(new IfThen(new XltC(v1, 0), new And(new XgtY(v3, minusAbsV2), new XlteqC(v3, 0))));

//   		    // pose(new Eq(new XgtC(v2, 0), new And(new XltY(v3, v2), new XgteqC(v3, 0))));
//   		    // pose(new Eq(new XltC(v2, 0), new And(new XgtY(v3, v2), new XlteqC(v3, 0))));

// 		    pose(new XmulYeqZ(t1, v2, t2));
		}
		else if (p.startsWith("min", 4)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);
		    IntVar v3 = getVariable(p3);

		    // pose(new IfThen(new XlteqY(v1,v2), new XeqY(v1,v3)));
		    // pose(new IfThen(new XlteqY(v2,v1), new XeqY(v2,v3)));

		    if (v1 == v2)
		    	pose(new XeqY(v1, v3));
		    else
		    	pose(new org.jacop.constraints.Min(new IntVar[] {v1, v2}, v3));

		}
		else if (p.startsWith("max", 4)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);
		    IntVar v3 = getVariable(p3);


		    // pose(new IfThen(new XgteqY(v1,v2), new XeqY(v1,v3)));
		    // pose(new IfThen(new XgteqY(v2,v1), new XeqY(v2,v3)));

		    if (  v1.singleton() && v2.singleton() ) {
			int max = java.lang.Math.max(v1.value(), v2.value());
			v3.domain.in(store.level, v3, max, max);
		    }
		    else if (v1.singleton() && v1.value() >= v2.max() ) {
			int max = v1.value();
			v3.domain.in(store.level, v3, max, max);
		    }
		    else if (v2.singleton() && v2.value() >= v1.max() ) {
			int max = v2.value();
			v3.domain.in(store.level, v3, max, max);
		    } 
		    else if (v1.min() >= v2.max() )
			pose(new XeqY(v1, v3));
		    else if (v2.min() >= v1.max() )
			pose(new XeqY(v2, v3));
		    else if (v1 == v2)
		    	pose(new XeqY(v1, v3));
		    else
		    	pose(new org.jacop.constraints.Max(new IntVar[] {v1, v2}, v3));

		}
		else if (p.startsWith("abs", 4)) {
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);

		    if (boundsConsistency)
		    	pose(new AbsXeqY(v1, v2));
		    else
			pose(new AbsXeqY(v1, v2, true));

		}
		else
		    System.out.println("TODO: "+p);
	    }

	    // array_* predicates
	    else if (p.startsWith("array_") ) {
		if (p.startsWith("bool_", 6)) {
		    if (p.startsWith("and", 11)) {
			//  			node.dump("");

			SimpleNode p1 = (SimpleNode)node.jjtGetChild(0);
			ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
			IntVar[] a1 = getVarArray(p1);
			IntVar v = getVariable(p2);

			pose(new AndBool(a1, v));
			// IntVar t1 = new IntVar(store, 0, a1.length);
			// pose(new Sum(a1, t1));
			// pose(new Reified(new XeqC(t1, a1.length), v));
		    }
		    else if (p.startsWith("or", 11)) {
			//   			node.dump("");

			SimpleNode p1 = (SimpleNode)node.jjtGetChild(0);
			ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
			IntVar[] a1 = getVarArray(p1);
			IntVar v = getVariable(p2);

			pose(new OrBool(a1, v));
			// IntVar t1 = new IntVar(store, 0, a1.length);
			// pose(new Sum(a1, t1));
			// pose(new Reified(new XgtC(t1, 0), v));
		    }
		    else if (p.startsWith("xor", 11)) {

			SimpleNode p1 = (SimpleNode)node.jjtGetChild(0);
			IntVar[] a1 = getVarArray(p1);

			pose(new XorBool(a1, one));

		    }
		    else if (p.startsWith("element", 11)) {
			// array_bool_element
			generateIntElementConstraint(node);
		    }
		    else
			System.err.println("%% ERROR: Not expected constraint : "+p);
		}
		else if (p.startsWith("var_bool_element", 6) ) {
		    // array_var_bool_element
		    generateVarElementConstraint(node);
		    // 		    generateElementConstraint(p, 0);
		}
		else if (p.startsWith("var_int_element", 6) ) {
		    // array_var_int_element
		    generateVarElementConstraint(node);
		    // 		    generateElementConstraint(p, 1);
		}
		else if (p.startsWith("int_element", 6)) {
		    // array_int_element
		    generateIntElementConstraint(node);
		}
		else if (p.startsWith("var_set_element", 6) ) {
		    // array_var_set_element
		    generateVarSetElementConstraint(node);
		}
		else if (p.startsWith("set_element", 6)) {
		    // array_set_element
		    generateSetElementConstraint(node);
		} 
		else if (p.startsWith("float_element", 6)) {
		    generateFloatElementConstraint(node);
		}
		else
		    System.out.println("TODO: "+p);
	    }

	    // bool_* predicates
	    else if (p.startsWith("bool_") ) {

		int operation = comparisonPredicate(p, 5);

		// bool_left_imp
		// a <- b <-> r
		//-------------
		// 0 <- 0 <-> 1
		// 0 <- 1 <-> 0
		// 1 <- 0 <-> 1
		// 1 <- 1 <-> 1
		if (p.startsWith("left_imp", 5)) {

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);
		    IntVar v3 = getVariable(p3);

		    pose(new IfThenBool(v2, v1, v3));
		    //  		    pose(new Reified(new Not(new And(new XeqC(v1, 0), new XeqC(v2, 1))), v3));
		    // 					pose(new Reified(new Or(new XneqC(v1, 0), new XneqC(v2, 1)), v3));

		    // 		    pose(new ExtensionalSupportMDD(new Variable[] {v1, v2, v3}, 
		    // 						   new int[][] {{0,0,1}, {0,1,0}, {1,0,1},{1,1,1}}));
		} 
		else if ( operation != -1) {
		    // bool_eq*, bool_ne*, bool_lt*, bool_gt*, bool_le*, and bool_ge*
		    int_comparison(operation, node, 7);
		}
		// bool_or
		else if (p.startsWith("or", 5)) {

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);
		    IntVar v3 = getVariable(p3);

		    pose(new OrBool(new IntVar[] {v1, v2}, v3));
		    // pose(new Reified(new XplusYgtC(v1, v2, 0), v3));
		}
		// bool_and
		else if (p.startsWith("and", 5)) {

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);
		    IntVar v3 = getVariable(p3);

 		    pose(new AndBool(new IntVar[] {v1, v2}, v3));
 		    // pose(new Reified(new XplusYeqC(v1, v2, 2), v3));
		}
		// bool_xor
		else if (p.startsWith("xor", 5)) {

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);
		    IntVar v3 = getVariable(p3);

		    pose(new XorBool(new IntVar[] {v1, v2}, v3));
		    // 					pose(new Reified(new XneqY(v1, v2), v3));
		}
		// bool_not
		else if (p.startsWith("not", 5)) {

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);

 		    pose(new XneqY(v1, v2));
// 		    pose(new XplusYeqC(v1, v2, 1));
		}
		// bool_right_imp
		// a -> b <-> r
		//-------------
		// 0 -> 0 <-> 1
		// 0 -> 1 <-> 1
		// 1 -> 0 <-> 0
		// 1 -> 1 <-> 1
		else if (p.startsWith("right_imp", 5)) {
		    // 		    node.dump("");
		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
		    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);
		    IntVar v3 = getVariable(p3);

		    pose(new IfThenBool(v1, v2, v3));
		    //  		    pose(new Reified(new Not(new And(new XeqC(v1, 1), new XeqC(v2, 0))), v3));
		    // 					pose(new Reified(new Or(new XneqC(v1, 1), new XneqC(v2, 0)), v3));

		    //  		    pose(new ExtensionalSupportMDD(new Variable[] {v1, v2, v3}, 
		    //  						   new int[][] {{0,0,1}, {0,1,1}, {1,0,0},{1,1,1}}));
		}
		// bool_clause[_reified]+
		// bool_clause([x1,..., xm], [y1,..., yn], true) ===>
		// ===> array_bool_or([x1,..., xm, not y1,..., not yn], true)
		else if (p.startsWith("clause", 5)) {

		    IntVar[] a1 = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] a2 = getVarArray((SimpleNode)node.jjtGetChild(1));

		    if (a1.length ==0 && a2.length ==0 )
			return;

		    BooleanVar t3;
		    if (a1.length ==0 ) {
			BoundDomain d = new BoundDomain(0,0);
			t3 = new BooleanVar(store, "", d);
		    }
		    else {
  			t3 = new BooleanVar(store);
  			pose(new OrBool(a1, t3));
		    }

		    BooleanVar t4;
		    if (a2.length ==0 ) {
			BoundDomain d = new BoundDomain(0,0);
			t4 = new BooleanVar(store, "", d);
		    }
		    else {
			// de Morgan law not y1 \/ not y2 ...\/ not yn = not(y1 /\ y2 .../\ yn)
			BooleanVar t2 = new BooleanVar(store);
			t4 = new BooleanVar(store);
			pose(new AndBool(a2, t2)); // and
			pose(new XneqY(t2,t4));  // not
		    }

		    if (p.startsWith("_reif", 11)) {
			IntVar v3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));
			pose(new Reified(new XplusYgtC(t3, t4, 0), v3));
			//  			pose(new Reified(new Or(new XgtC(t3, 0), new XgtC(t4, 0)), v3));
		    }
		    else
			pose(new XplusYgtC(t3, t4, 0));
		    // 			pose(new Or(new XgtC(t3, 0), new XgtC(t4, 0)));

		}
		// bool_lin_* (eq, ne, lt, gt, le, ge)
		else if (p.startsWith("lin_", 5)) {

		    operation = comparisonPredicate(p, 9);
		    int_lin_relation(operation, node);
		}
		else
		    System.out.println("TODO: "+p);
		// 		<-------------
	    }

	    // set_* predicates
	    else if (p.startsWith("set_") ) {

		if (p.startsWith("eq", 4)) {

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);

		    PrimitiveConstraint c = new org.jacop.set.constraints.AeqB(v1, v2);

		    if (p.startsWith("_reif", 6)) {
			IntVar v3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

			pose(new Reified(c, v3));
		    }
		    else
			pose(c);

		}
		else if (p.startsWith("ne", 4)) {

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);

		    PrimitiveConstraint c = new Not(new org.jacop.set.constraints.AeqB(v1, v2));

		    if (p.startsWith("_reif", 6)) {
			IntVar v3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

			pose(new Reified(c, v3));
		    }
		    else
			pose(c);
		}
		else if (p.startsWith("lt", 4)) {

		    if (p.startsWith("_reif", 6)) {
			System.err.println("%% set_lt_reif with list of set variables is not avaible in org.jacop.set");
			System.exit(0);
		    }

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);

		    pose(new Lex(v1, v2));
		}
		else if (p.startsWith("gt", 4)) {

		    if (p.startsWith("_reif", 6)) {
			System.err.println("%% set_gt_reif with list of set variables is not avaible in org.jacop.set");
			System.exit(0);
		    }

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);

		    pose(new Lex(v2, v1));
		}
		else if (p.startsWith("le", 4)) {

		    if (p.startsWith("_reif", 6)) {
			System.err.println("%% set_le_reif with list of set variables is not avaible in org.jacop.set");
			System.exit(0);
		    }

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);

		    pose(new Lex(v1, v2, false));

		}
		else if (p.startsWith("ge", 4))  {

		    if (p.startsWith("_reif", 6)) {
			System.err.println("%% set_ge_reif with list of set variables is not avaible in org.jacop.set");
			System.exit(0);
		    }

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);

		    pose(new Lex(v2, v1, false));

		}

		else  if (p.startsWith("intersect", 4)) {

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);
		    SetVar v3 = getSetVariable(node, 2);

		    pose(new AintersectBeqC(v1, v2, v3));
		}
		else if (p.startsWith("card", 4)) {

		    SetVar v1 = getSetVariable(node, 0);
		    IntVar v2 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(1));

		    if (v2.singleton()) {
			v1.domain.inCardinality(store.level, v1, v2.min(), v2.max());

			if (debug)
			    System.out.println ("Cardinality of set " + v1 + " = " + v2);

		    }
		    else
			pose(new CardAeqX(v1, v2));
		}
		else if (p.startsWith("in", 4)) {

		    PrimitiveConstraint c;

		    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		    SimpleNode v1Type = (SimpleNode)node.jjtGetChild(1);
		    if (v1Type.getId() == JJTSETLITERAL) {
			IntDomain d = getSetLiteral(node, 1);
			IntVar v1 = getVariable(p1);
			if (p.startsWith("_reif", 6)) 
			    c = new org.jacop.constraints.In(v1, d);
			else { 
			    v1.domain.in(store.level, v1, d);
			    return;
			}
		    }
		    else {
			SetVar v2 = getSetVariable(node, 1);

			if (p1.getType() == 0) { // p1 int
			    int i1 = getInt(p1);
			    c = new EinA(i1, v2);
			}
			else { // p1 var
			    IntVar v1 = getVariable(p1);
			    c = new XinA(v1, v2);
			}
		    }
		    // FIXME, include AinB here? 

		    if (p.startsWith("_reif", 6)) {
			IntVar v3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

			pose(new Reified(c, v3));
		    }
		    else
			pose(c);

		}
		else if (p.startsWith("subset", 4)) {

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);

		    PrimitiveConstraint c = new AinB(v1, v2);
		    if (p.startsWith("_reif", 10)) {
			IntVar v3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

			pose(new Reified(c, v3));
		    }
		    else
			pose(c);
		}
		else if (p.startsWith("superset", 4)) {

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);

		    PrimitiveConstraint c = new AinB(v2, v1);
		    if (p.startsWith("_reif", 12)) {
			IntVar v3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

			pose(new Reified(c, v3));
		    }
		    else
			pose(c);
		}
		else if (p.startsWith("union", 4)) {

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);
		    SetVar v3 = getSetVariable(node, 2);

		    pose(new AunionBeqC(v1, v2, v3));
		}
		else if (p.startsWith("diff", 4)) {

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);
		    SetVar v3 = getSetVariable(node, 2);

		    pose(new AdiffBeqC(v1, v2, v3));
		}
		else if (p.startsWith("symdiff", 4)) {

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);
		    SetVar v3 = getSetVariable(node, 2);

		    SetVar t1 = new SetVar(store, new BoundSetDomain(IntDomain.MinInt, IntDomain.MaxInt));
		    SetVar t2 = new SetVar(store, new BoundSetDomain(IntDomain.MinInt, IntDomain.MaxInt));
		    
		    pose(new AdiffBeqC(v1, v2, t1));
		    
		    pose(new AdiffBeqC(v2, v1, t2));

		    pose(new AunionBeqC(t1, t2, v3));
		}
		else
		    System.out.println("TODO: "+p);
	    }
	    // bool2int and int2bool coercion operations
	    else if (p.equals("bool2int") || p.equals("int2bool") ) {
		// 		node.dump("");

		ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
		ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

		pose(new XeqY(getVariable(p1), getVariable(p2)));
	    }
	    // ========== JaCoP constraints ==================>>
	    else if (p.startsWith("jacop_"))
		if (p.startsWith("cumulative", 6)) {

		    IntVar[] s = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] d = getVarArray((SimpleNode)node.jjtGetChild(1));
		    IntVar[] r = getVarArray((SimpleNode)node.jjtGetChild(2));
		    IntVar b = getVariable((ASTScalarFlatExpr)node.jjtGetChild(3));

		    // if (b.min() == b.max())
		    // 	b = new IntVar(store, 0, b.max());

		    // if (boundsConsistency) 
		    //  	pose(new Cumulative(s, d, r, b, true, false, false));
		    // else 
		    pose(new Cumulative(s, d, r, b, true, true, false));

		}
		else if (p.startsWith("circuit", 6)) {
		    IntVar[] v = getVarArray((SimpleNode)node.jjtGetChild(0));

		    pose(new Circuit(v));

		    if ( domainConsistency )  // we add additional implied constraint if domain consistency is required
			parameterListForAlldistincts.add(v);

		}
		else if (p.startsWith("subcircuit", 6)) {
		    IntVar[] v = getVarArray((SimpleNode)node.jjtGetChild(0));

		    pose(new Subcircuit(v));
		}
		else if (p.startsWith("alldiff", 6)) {
		    IntVar[] v = getVarArray((SimpleNode)node.jjtGetChild(0));

		    IntervalDomain dom = new IntervalDomain();
		    for (IntVar var : v)
			dom = (IntervalDomain)dom.union( var.dom() );
 		    if (v.length <= 100) { // && v.length == dom.getSize()) {
			// we do not not pose Alldistinct directly because of possible inconsistency with its 
			// intiallization; we collect all vectors and pose it at the end when all constraints are posed
			// pose(new Alldistinct(v));

			if (boundsConsistency) {
			    pose(new Alldiff(v));
  			    // System.out.println("Alldiff imposed");
			}
			else { // domain consistency
			    parameterListForAlldistincts.add(v);

    			    // System.out.println("Alldistinct imposed on " + java.util.Arrays.asList(v));
			}
		    }
		    else {
			pose(new Alldiff(v));
			//			System.out.println("Alldiff imposed");
		    }
		}
		else if (p.startsWith("alldistinct", 6)) {
		    IntVar[] v = getVarArray((SimpleNode)node.jjtGetChild(0));
		    // we do not not pose Alldistinct directly because of possible inconsistency with its 
		    // intiallization; we collect all vectors and pose it at the end when all constraints are posed

// 		    pose(new Alldistinct(v));
		    parameterListForAlldistincts.add(v);
//  		    System.out.println("Alldistinct imposed "+ java.util.Arrays.asList(v));
		}
		else if (p.startsWith("among_var", 6)) {
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] s = getVarArray((SimpleNode)node.jjtGetChild(1));
		    IntVar v = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

		    // we do not not pose AmongVar directly because of possible inconsistency with its 
		    // intiallization; we collect all constraints and pose them at the end when all other constraints are posed

		    delayedConstraints.add(new AmongVar(x, s, v));
// 		    pose(new AmongVar(x, s, v));
		}
		else if (p.startsWith("among", 6)) {
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntDomain s = getSetLiteral(node, 1);
		    IntVar v = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

		    // if (s.singleton()) 
		    // pose(new Count(x, v, s.value()));
		    // else {

		    IntervalDomain setImpl = new IntervalDomain();
		    for (ValueEnumeration e = s.valueEnumeration(); e.hasMoreElements();) {
			int val = e.nextElement();

			setImpl.unionAdapt(new IntervalDomain(val, val));
		    }

		    pose(new Among(x, setImpl, v));

		    // }
		}
		else if (p.startsWith("gcc", 6)) {
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] c = getVarArray((SimpleNode)node.jjtGetChild(1));
		    int index_min = getInt((ASTScalarFlatExpr)node.jjtGetChild(2));
		    int index_max = index_min + c.length - 1;

		    for (int i=0; i<x.length; i++) {
			if (index_min>x[i].max() || index_max<x[i].min()) {
			    System.err.println("%% ERROR: gcc domain error in variable " + x[i]);
			    System.exit(0);
			}
			if (index_min>x[i].min() && index_min<x[i].max()) 
			    x[i].domain.inMin(store.level, x[i], index_min);
			if (index_max<x[i].max() && index_max>x[i].min())
			    x[i].domain.inMax(store.level, x[i], index_max);
		    }
		    // 		    System.out.println("c = " + Arrays.asList(x));

		    // =========> remove all non-existing-values counters
		    IntDomain gcc_dom = new IntervalDomain();
		    for (IntVar v : x)
			gcc_dom = gcc_dom.union( v.dom() );
		    ArrayList<Var> c_list = new ArrayList<Var>();
		    for (int i=0; i<c.length; i++)
			if ( gcc_dom.contains(i+index_min ) )
			    c_list.add(c[i]);
			else
			    pose(new XeqC(c[i], 0));
		    IntVar[] c_array = new IntVar[c_list.size()];
		    c_array = c_list.toArray(c_array);
		    // =========>

		    pose(new GCC(x, c_array));
		}
		else if (p.startsWith("global_cardinality_closed", 6)) {
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    int[] cover = getIntArray((SimpleNode)node.jjtGetChild(1));
		    IntVar[] counter = getVarArray((SimpleNode)node.jjtGetChild(2));

		    IntDomain gcc_dom = new IntervalDomain();
		    for (int e : cover)
			gcc_dom = gcc_dom.union( e );		    
		    for (IntVar v : x)
			v.domain.in(store.level, v, gcc_dom);

		    pose( new GCC(x, counter));
		}
		else if (p.startsWith("global_cardinality_low_up_closed", 6)) {
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    int[] cover = getIntArray((SimpleNode)node.jjtGetChild(1));
		    int[] low = getIntArray((SimpleNode)node.jjtGetChild(2));
		    int[] up = getIntArray((SimpleNode)node.jjtGetChild(3));

		    IntDomain gcc_dom = new IntervalDomain();
		    for (int e : cover)
			gcc_dom = gcc_dom.union( e );		    
		    for (IntVar v : x)
			v.domain.in(store.level, v, gcc_dom);

		    IntVar[] counter = new IntVar[low.length];
		    for (int i = 0; i < counter.length; i++)
			counter[i] = new IntVar(store, "counter"+i, low[i], up[i]);

		    pose( new GCC(x, counter));
		}
		else if (p.startsWith("diff2", 6)) {
		    IntVar[] v = getVarArray((SimpleNode)node.jjtGetChild(0));

		    IntVar[][] r = new IntVar[v.length/4][4];
		    for (int i=0; i<r.length; i++)
			for (int j=0; j<4; j++)
			    r[i][j] = v[4*i+j];

		    pose(new Diff2(r));
		}
		else if (p.startsWith("list_diff2", 6)) {
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] y = getVarArray((SimpleNode)node.jjtGetChild(1));
		    IntVar[] lx = getVarArray((SimpleNode)node.jjtGetChild(2));
		    IntVar[] ly = getVarArray((SimpleNode)node.jjtGetChild(3));

		    pose(new Diff2(x, y, lx, ly));
		}
		else if (p.startsWith("count", 6)) {
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    int y = getInt((ASTScalarFlatExpr)node.jjtGetChild(1));
		    IntVar c = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

		    pose(new Count(x, c, y));

		    // pose(new Among(x, new IntervalDomain(y,y), c));
		}
		else if (p.startsWith("nvalue", 6)) {
		    IntVar n = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(1));

		    pose(new Values(x, n));
		}
		else if (p.startsWith("minimum", 6)) {
		    IntVar n = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(1));

		    pose(new org.jacop.constraints.Min(x, n));
		}
		else if (p.startsWith("maximum", 6)) {
		    IntVar n = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(1));

		    pose(new org.jacop.constraints.Max(x, n));
		}
		else if (p.startsWith("table_int", 6) ||
			 p.startsWith("table_bool", 6)) { 
		    IntVar[] v = getVarArray((SimpleNode)node.jjtGetChild(0));
		    int size = v.length;

		    int[] tbl = getIntArray((SimpleNode)node.jjtGetChild(1));
		    int[][] t = new int[tbl.length/size][size];
		    for (int i=0; i<t.length; i++)
			for (int j=0; j<size; j++)
			    t[i][j] = tbl[size*i+j];

		    // we do not not pose ExtensionalSupportMDD directly because of possible inconsistency with its 
		    // intiallization; we collect all constraints and pose them at the end when all other constraints are posed

		    delayedConstraints.add(new ExtensionalSupportMDD(v, t));
 		    //pose(new ExtensionalSupportMDD(v, t));
		}
		else if (p.startsWith("assignment", 6)) {
		    IntVar[] f = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] invf = getVarArray((SimpleNode)node.jjtGetChild(1));
		    int index_f = getInt((ASTScalarFlatExpr)node.jjtGetChild(2));
		    int index_invf = getInt((ASTScalarFlatExpr)node.jjtGetChild(3));

		    // we do not not pose Assignment directly because of possible inconsistency with its 
		    // intiallization; we collect all constraints and pose them at the end when all other constraints are posed

		    if ( domainConsistency )  // we add additional implied constraint if domain consistency is required
			parameterListForAlldistincts.add(f);

		    delayedConstraints.add(new Assignment(f, invf, index_f, index_invf));

// 		    pose(new Assignment(f, invf, index_f, index_invf));
		}
		else if (p.startsWith("regular", 6)) {

		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    int Q = getInt((ASTScalarFlatExpr)node.jjtGetChild(1));
		    int S = getInt((ASTScalarFlatExpr)node.jjtGetChild(2));
		    int[] d = getIntArray((SimpleNode)node.jjtGetChild(3));
		    int q0 = getInt((ASTScalarFlatExpr)node.jjtGetChild(4));
		    IntDomain F = getSetLiteral(node, 5);
		    int minIndex = getInt((ASTScalarFlatExpr)node.jjtGetChild(6));

		    // Build DFA
		    FSM dfa = new FSM();
		    FSMState[] s = new FSMState[Q]; 
		    for (int i=0; i<s.length; i++) { 
			s[i] = new FSMState(); 
			dfa.allStates.add(s[i]); 
		    } 
		    dfa.initState = s[q0 - 1]; 
		    ValueEnumeration final_states = F.valueEnumeration(); //new SetValueEnumeration(F);
		    while (final_states.hasMoreElements())
			dfa.finalStates.add(s[final_states.nextElement()-1]); 

		    //  		    System.out.println("init state: "+ dfa.initState+", "+ F + "  final states: "+dfa.finalStates +",  first state: "+ s[0]);

		    for (int i=0; i<Q; i++) {
			//  			System.out.print(i+": ");
			for (int j=0; j<S; j++)
			    if (d[i*S+j] != 0) {
				s[i].transitions.add(new FSMTransition(new IntervalDomain(j+minIndex,j+minIndex), s[d[i*S+j]-minIndex])); 
				//   				System.out.print("("+(int)(j+minIndex)+") -> "+ (int)(d[i*S+j]-minIndex)+", ");
			    }
			//    			System.out.println();
		    }

		    pose(new Regular(dfa, x));

		    //  		    System.out.println(dfa+"\n");
		    //   		    System.out.println("Regular("+Arrays.asList(x)+", "+Q+", "+
		    //  				       S+", "+Arrays.asList(d)+", "+q0+", "+
		    //  				       dfa.finalStates+", "+minIndex+")");
		}
		else if (p.startsWith("knapsack", 6)) {
		    int[] weights = getIntArray((SimpleNode)node.jjtGetChild(0));
		    int[] profits = getIntArray((SimpleNode)node.jjtGetChild(1));
		    IntVar W = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));
		    IntVar P = getVariable((ASTScalarFlatExpr)node.jjtGetChild(3));
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(4));

//   		    System.out.println("Knapsack("+
// 				       java.util.Arrays.toString(weights) +
// 				       ", "+ java.util.Arrays.toString(profits) +
// 				       ", "+ W +
// 				       ", "+ P +
// 				       ", " + java.util.Arrays.asList(x) +")");

 		    pose(new Knapsack(profits, weights, x, W, P));
		}
		else if (p.startsWith("sequence", 6)) { // implements jacop_sequence
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntDomain u = getSetLiteral(node, 1);
		    int q = getInt((ASTScalarFlatExpr)node.jjtGetChild(2));
		    int min = getInt((ASTScalarFlatExpr)node.jjtGetChild(3));
		    int max = getInt((ASTScalarFlatExpr)node.jjtGetChild(4));

		    IntervalDomain setImpl = new IntervalDomain();
		    for(int i = 0; true ;i++) {
		    	Interval val = u.getInterval(i);
		    	if (val != null)
		    		setImpl.unionAdapt(val);
		    	else
		    		break;
		    }

		    DecomposedConstraint c = new Sequence(x, setImpl, q, min, max);
// 		    System.out.println("sequence("+java.util.Arrays.asList(x)+", "+
// 				       u+", "+q+", "+", "+min+", "+max);
		    store.imposeDecomposition(c);
		}
 		else if (p.startsWith("stretch", 6)) {
		    int[] values = getIntArray((SimpleNode)node.jjtGetChild(0));
		    int[] min = getIntArray((SimpleNode)node.jjtGetChild(1));
		    int[] max = getIntArray((SimpleNode)node.jjtGetChild(2));
 		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(3));
//  		    System.out.println("Stretch("+java.util.Arrays.asList(values) +
// 				       ", " + java.util.Arrays.asList(min) +
// 				       ", " + java.util.Arrays.asList(max) +
// 				       ", "+ java.util.Arrays.asList(x)+")");   

		    DecomposedConstraint c = new Stretch(values, min, max, x);

		    store.imposeDecomposition(c);
 		}
 		else if (p.startsWith("disjoint", 6)) {

		    SetVar v1 = getSetVariable(node, 0);
		    SetVar v2 = getSetVariable(node, 1);

		    pose(new AdisjointB(v1, v2));
		}
	    // 		else if (p.startsWith("sequence", 6)) {
	    // 		    Variable[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
	    // 		    Set u = getSetLiteral((SimpleNode)node, 1);
	    // 		    int q = getInt((ASTScalarFlatExpr)node.jjtGetChild(2));
	    // 		    int min = getInt((ASTScalarFlatExpr)node.jjtGetChild(3));
	    // 		    int max = getInt((ASTScalarFlatExpr)node.jjtGetChild(4));

	    //  		    DecomposedConstraint c = new Sequence(x, u, q, min, max);
	    // 		    System.out.println("sequence("+Arrays.asList(x)+", "+
	    // 				       u+", "+q+", "+", "+min+", "+max);
	    //   		    store.imposeDecomposition(c);
	    // 		}
 		else if (p.startsWith("network", 6)) {
		    int[] arc = getIntArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] flow = getVarArray((SimpleNode)node.jjtGetChild(1));
		    IntVar[] weight = getVarArray((SimpleNode)node.jjtGetChild(2));
		    int[] balance = getIntArray((SimpleNode)node.jjtGetChild(3));
		    IntVar cost = getVariable((ASTScalarFlatExpr)node.jjtGetChild(4));

  		    // System.out.println("NetworkFlow("+ arc +
 		    // 		       ", " + java.util.Arrays.asList(flow) +
 		    // 		       ", " + java.util.Arrays.asList(weight) +
 		    // 		       ", "+ balance +
		    // 		       ", "+ cost +")");   

		    NetworkBuilder net = new NetworkBuilder();

		    Node[] netNode = new Node[balance.length];
		    for (int i = 0; i < balance.length; i++) 
			netNode[i] = net.addNode("n_"+i, balance[i]);

		    for (int i = 0; i < flow.length; i++) {
			net.addArc(netNode[arc[2*i]-1], netNode[arc[2*i+1]-1], weight[i], flow[i]);
		    }

		    net.setCostVariable(cost);

 		    pose(new NetworkFlow(net));

		} 
		else if (p.startsWith("lex_less_int", 6) || p.startsWith("lex_less_bool", 6)) {
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] y = getVarArray((SimpleNode)node.jjtGetChild(1));

		    // DecomposedConstraint c = new org.jacop.constraints.Lex(new IntVar[][] {x, y}, true);
		    // store.imposeDecomposition(c);

		    Constraint c = new LexOrder(x, y, true);
		    store.impose(c);

		}
		else if (p.startsWith("lex_lesseq_int", 6) || p.startsWith("lex_lesseq_bool", 6)) {
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] y = getVarArray((SimpleNode)node.jjtGetChild(1));

		    // System.out.println ("lex_lesseq_int: x.length = " + x.length +  " y.length = " + y.length);

		    // DecomposedConstraint c = new org.jacop.constraints.Lex(new IntVar[][] {x, y});
		    // store.imposeDecomposition(c);

		    Constraint c = new LexOrder(x, y, false);
		    store.impose(c);

		}
 		else if (p.startsWith("bin_packing", 6)) {
		    IntVar[] bin = getVarArray((SimpleNode)node.jjtGetChild(0));
		    IntVar[] capacity = getVarArray((SimpleNode)node.jjtGetChild(1));
		    int[] w = getIntArray((SimpleNode)node.jjtGetChild(2));

   		    pose( new org.jacop.constraints.binpacking.Binpacking(bin, capacity, w) );
//   		    Constraint binPack = new org.jacop.constraints.binpacking.Binpacking(bin, capacity, w);
//   		    delayedConstraints.add(binPack);
		}
		else if (p.startsWith("float_maximum", 6)) {
		    FloatVar p2 = getFloatVariable((ASTScalarFlatExpr)node.jjtGetChild(1));
		    FloatVar[] p1 = getFloatVarArray((SimpleNode)node.jjtGetChild(0));

		    pose(new org.jacop.floats.constraints.Max(p1, p2));
		}
		else if (p.startsWith("float_minimum", 6)) {
		    FloatVar p2 = getFloatVariable((ASTScalarFlatExpr)node.jjtGetChild(1));
		    FloatVar[] p1 = getFloatVarArray((SimpleNode)node.jjtGetChild(0));

		    pose(new org.jacop.floats.constraints.Min(p1, p2));
		}
 		else if (p.startsWith("geost", 6)) {

		    int dim = getInt((ASTScalarFlatExpr)node.jjtGetChild(0));
		    int[] rect_size = getIntArray((SimpleNode)node.jjtGetChild(1));
		    int[] rect_offset = getIntArray((SimpleNode)node.jjtGetChild(2));
		    IntDomain[] shape =  getSetArray((SimpleNode)node.jjtGetChild(3));
		    IntVar[] x = getVarArray((SimpleNode)node.jjtGetChild(4));
		    IntVar[] kind = getVarArray((SimpleNode)node.jjtGetChild(5));

		    // System.out.println("dim = " + dim);
		    // System.out.print("rect_size = [");
		    // for (int i = 0; i < rect_size.length; i++) 
		    // 	System.out.print(" " + rect_size[i]);
		    // System.out.print("]\nrect_offset = [");
		    // for (int i = 0; i < rect_offset.length; i++) 
		    // 	System.out.print(" " + rect_offset[i]);
		    // System.out.println("]\nshape = " + java.util.Arrays.asList(shape));
		    // System.out.println("x = " + java.util.Arrays.asList(x));
		    // System.out.println("kind = " + java.util.Arrays.asList(kind));
		    // System.out.println("===================");


		    ArrayList<Shape> shapes = new ArrayList<Shape>(); 

		    // dummy shape to have right indexes for kind (starting from 1)
		    ArrayList<DBox> dummy = new ArrayList<DBox>();
		    int[] offsetDummy = new int[dim];
		    int[] sizeDummy = new int[dim];
		    for (int k = 0; k < dim; k++) {
			offsetDummy[k] = 0;
			sizeDummy[k] = 1;
		    }
		    dummy.add(new DBox(offsetDummy, sizeDummy));
		    shapes.add( new Shape(0, dummy));

		    // create all shapes (starting with id=1)
		    for (int i = 0; i < shape.length; i++) {
			ArrayList<DBox> shape_i = new ArrayList<DBox>();

			for (ValueEnumeration e = shape[i].valueEnumeration(); e.hasMoreElements();) {
			    int j = e.nextElement();

			    int[] offset = new int[dim];
			    int[] size = new int[dim];

			    for (int k = 0; k < dim; k++) {
				offset[k] = rect_offset[(j-1)*dim+k];
				size[k] = rect_size[(j-1)*dim+k];
			    }
			    shape_i.add(new DBox(offset, size));

			}
			shapes.add( new Shape((i+1), shape_i) );
		    }		    

		    // for (int i = 0; i < shapes.size(); i++) 
		    // 	System.out.println("*** " + shapes.get(i));

		    ArrayList<GeostObject> objects = new ArrayList<GeostObject>(); 

		    for (int i = 0; i < kind.length; i++) {

			IntVar[] coords = new IntVar[dim]; 

			for (int k = 0; k < dim; k++) 
			    coords[k] = x[i*dim+k];

			// System.out.println("coords = " + java.util.Arrays.asList(coords));

			IntVar start = new IntVar(store, "start["+i+"]", 0,0); 
			IntVar duration = new IntVar(store, "duration["+i+"]", 1,1); 
			IntVar end = new IntVar(store, "end["+i+"]", 1, 1); 
			GeostObject obj = new GeostObject(i, coords, kind[i], start, duration, end); 
			objects.add(obj);
		    }

		    // System.out.println("===========");
		    // for (int i = 0; i < objects.size(); i++) 
		    // 	System.out.println(objects.get(i));
		    // System.out.println("===========");

		    ArrayList<ExternalConstraint> constraints = new ArrayList<ExternalConstraint>(); 
		    int[] dimensions = new int[dim+1]; 
		    for (int i = 0; i < dim+1; i++) 
			dimensions[i] = i;

		    NonOverlapping constraint1 = new NonOverlapping(objects, dimensions); 
		    constraints.add(constraint1); 

		    if (p.startsWith("geost_bb", 6)) {

			int[] lb = getIntArray((SimpleNode)node.jjtGetChild(6));
			int[] ub = getIntArray((SimpleNode)node.jjtGetChild(7));

			// System.out.print("[");
			// for (int i = 0; i < lb.length; i++) 
			// 	System.out.print(" " + lb[i]);
			// System.out.print("]\n[");
			// for (int i = 0; i < ub.length; i++) 
			// 	System.out.print(" " + ub[i]);
			// System.out.println("]");

			InArea constraint2 = new InArea(new DBox(lb, ub), null); 
			constraints.add(constraint2);
		    }

   		    pose( new Geost(objects, constraints, shapes) );
		}
		else
		    System.err.println("%% ERROR: Constraint "+p+" not supported.");
	    // >>========== JaCoP constraints ==================
	    else
		System.err.println("%% ERROR: Constraint "+p+" not supported.");
	}
    }

    int comparisonPredicate(String name, int offset) {

	if (name.startsWith("eq", offset))
	    return eq;
	else if (name.startsWith("ne", offset))
	    return ne;
	else if (name.startsWith("lt", offset))
	    return lt;
	else if (name.startsWith("gt", offset))
	    return gt;
	else if (name.startsWith("le", offset))
	    return le;
	else if (name.startsWith("ge", offset))
	    return ge;
	else return -1;
    }

    void int_negate(SimpleNode node) throws FailException {
	// 	 node.dump("");

	// p1 + p2 = 0
	ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
	ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

	PrimitiveConstraint c = null;
	if (p2.getType() == 0) { // p2 int
	    IntVar v1 = getVariable(p1);
	    c = new XplusCeqZ(v1, p2.getInt(), zero);
	}
	else if (p1.getType() == 0) { // p1 int
	    IntVar v2 = getVariable(p2);
	    c = new XplusCeqZ(v2, p1.getInt(), zero);
	}
	else {
	    IntVar v1 = getVariable(p1);
	    IntVar v2 = getVariable(p2);
	    c = new XplusYeqZ(v1, v2, zero);
	}
	pose(c);
    }


    void int_comparison(int operation, SimpleNode node, int reifStart) {

	//   	 node.dump("");

	ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
	ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

	boolean reified = false; 
	if (p.startsWith("_reif", reifStart)) {
	    reified = true;
	}

	if (reified) { // reified constraint
	    PrimitiveConstraint c = null;
	    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);
	    IntVar v3 = getVariable(p3);

	    if (p2.getType() == 0 || p2.getType() == 1) { // var rel int or bool
		IntVar v1 = getVariable(p1);

		int i2 = getInt(p2);
		switch (operation) {

		case eq :
		    if (v1.min() > i2 || v1.max() < i2) {
		    	v3.domain.in(store.level, v3, 0, 0);
			return;
		    }
		    else if (v1.min() == i2 && v1.singleton() ) {
		    	v3.domain.in(store.level, v3, 1, 1);
			return;
		    } else if (v3.max() == 0) {
			v1.domain.inComplement(store.level, v1, i2);
			return;
		    }
		    else if (v3.min() == 1) {
			v1.domain.in(store.level, v1, i2, i2);
			return;
		    }
		    else
			c = new XeqC(v1, i2);
		    break;

		case ne :
		    if (v1.min() > i2 || v1.max() < i2) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (v1.min() == i2 && v1.singleton() ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    } else if (v3.max() == 0) {
			v1.domain.in(store.level, v1, i2, i2);
			return;
		    }
		    else if (v3.min() == 1) {
			v1.domain.inComplement(store.level, v1, i2);
			return;
		    }
		    else
			c = new XneqC(v1, i2);
		    break;
		case lt :
		    if (v1.max() < i2) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (v1.min() >= i2 ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new XltC(v1, i2);
		    break;
		case gt :
		    if (v1.min() > i2) {
			v3.domain.in(store.level, v3, 1, 1);
			return;
		    }
		    else if (v1.max() <= i2 ) {
			v3.domain.in(store.level, v3, 0, 0);
			return;
		    }
		    else
			c = new XgtC(v1, i2);
		    break;
		case le :
		    if (v1.max() <= i2) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (v1.min() > i2 ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new XlteqC(v1, i2);
		    break;
		case ge :
		    if (v1.min() >= i2) {
			v3.domain.in(store.level, v3, 1, 1);
			return;
		    }
		    else if (v1.max() < i2 ) {
			v3.domain.in(store.level, v3, 0, 0);
			return;
		    }
		    else
			c = new XgteqC(v1, i2);
		    break;
		}
	    } else if (p1.getType() == 0 || p1.getType() == 1) { // int rel var or bool
		IntVar v2 = getVariable(p2);
		int i1 = getInt(p1);

		switch (operation) {

		case eq :
		    if (v2.min() > i1 || v2.max() < i1) {
		    	v3.domain.in(store.level, v3, 0, 0);
			return;
		    }
		    else if (v2.min() == i1 && v2.singleton() ) {
		    	v3.domain.in(store.level, v3, 1, 1);
			return;
		    }
		    else if (v3.max() == 0) {
			v2.domain.inComplement(store.level, v2, i1);
			return;
		    }
		    else if (v3.min() == 1) {
			v2.domain.in(store.level, v2, i1, i1);
			return;
		    }
		    else
			c = new XeqC(v2, i1);
		    break;

		case ne :
		    if (v2.min() > i1 || v2.max() < i1) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (v2.min() == i1 && v2.singleton() ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new XneqC(v2, i1);
		    break;
		case lt :
		    if (i1 < v2.min()) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (i1 >= v2.max() ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new XgtC(v2, i1);
		    break;
		case gt :
		    if (i1 > v2.max()) {
			v3.domain.in(store.level, v3, 1, 1);
			return;
		    }
		    else if (i1 <= v2.min() ) {
			v3.domain.in(store.level, v3, 0, 0);
			return;
		    }
		    else
			c = new XltC(v2, i1);
		    break;
		case le :
		    if (i1 <= v2.min()) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (i1 > v2.max() ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new XgteqC(v2, i1);
		    break;
		case ge :
		    if (i1 > v2.max()) {
			v3.domain.in(store.level, v3, 1, 1);
			return;
		    }
		    else if (i1 < v2.min() ) {
			v3.domain.in(store.level, v3, 0, 0);
			return;
		    }
		    else
			c = new XlteqC(v2, i1);
		    break;
		}
	    } else { // var rel var
		IntVar v1 = getVariable(p1);
		IntVar v2 = getVariable(p2);

		switch (operation) {
		case eq :
		    c = new XeqY(v1, v2);

		    // if (v3.singleton())
		    // 	if (v3.min() == 1) 
		    // 	    if (v1.singleton()) {
		    // 		v2.domain.in(store.level, v2, v1.domain);
		    // 		return;
		    // 	    }
		    // 	    else {
		    // 		pose(c);
		    // 		return;
		    // 	    }
		    // 	else { // v3.max() == 0
		    // 	    if (v1.singleton()) {
		    // 		v2.domain.inComplement(store.level, v2, v1.min());
		    // 		return;
		    // 	    }
		    // 	    else {
		    // 		pose(c);
		    // 		return;
		    // 	    }
		    // 	}

		    break;
		case ne :
		    c = new XneqY(v1, v2);
		    break;
		case lt :
		    c = new XltY(v1, v2);
		    break;
		case gt :
		    c = new XgtY(v1, v2);
		    break;
		case le :
		    c = new XlteqY(v1, v2);
		    break;
		case ge :
		    c = new XgteqY(v1, v2);
		    break;
		}
	    }

 	    Constraint cr = new Reified(c, v3);
 	    pose(cr);
	}
	else  { // not reified constraints

	    if (p1.getType() == 0 || p1.getType() == 1) { // first parameter int or bool
		if (p2.getType() == 0 || p2.getType() == 1) { // first parameter int/bool & second parameter int/bool
		    int i1 = getInt(p1);
		    int i2 = getInt(p2);
		    switch (operation) {
		    case eq :
			if (i1 != i2) throw Store.failException;
			break;
		    case ne :
			if (i1 == i2) throw Store.failException;
			break;
		    case lt :
			if (i1 >= i2) throw Store.failException;
			break;
		    case gt :
			if (i1 <= i2) throw Store.failException;
			break;
		    case le :
			if (i1 > i2) throw Store.failException;
			break;
		    case ge :
			if (i1 < i2) throw Store.failException;
			break;
		    }
		} 
		else { // first parameter int/bool & second parameter var

		    int i1 = getInt(p1);
		    IntVar v2 = getVariable(p2);

		    switch (operation) {
		    case eq :
			v2.domain.in(store.level, v2, i1, i1);
			break;
		    case ne :
			v2.domain.inComplement(store.level, v2, i1);
			break;
		    case lt :
			v2.domain.in(store.level, v2, i1+1, IntDomain.MaxInt);
			break;
		    case gt :
			v2.domain.in(store.level, v2, IntDomain.MinInt, i1-1);
			break;
		    case le :
			v2.domain.in(store.level, v2, i1, IntDomain.MaxInt);
			break;
		    case ge :
			v2.domain.in(store.level, v2, IntDomain.MinInt, i1);
			break;
		    }
		}
	    }
	    else { // first parameter var
		if (p2.getType() == 0 || p2.getType() == 1) { // first parameter var & second parameter int

		    IntVar v1 = getVariable(p1);
		    int i2 = getInt(p2);

		    switch (operation) {
		    case eq :
			v1.domain.in(store.level, v1, i2, i2);
			break;
		    case ne :
			v1.domain.inComplement(store.level, v1, i2);
			break;
		    case lt :
			v1.domain.in(store.level, v1, IntDomain.MinInt, i2-1);
			break;
		    case gt :
			v1.domain.in(store.level, v1, i2+1, IntDomain.MaxInt);
			break;
		    case le :
			v1.domain.in(store.level, v1, IntDomain.MinInt, i2);
			break;
		    case ge :
			v1.domain.in(store.level, v1, i2, IntDomain.MaxInt);
			break;
		    }

		} 
		else { // first parameter var & second parameter var

		    PrimitiveConstraint c = null;
		    IntVar v1 = getVariable(p1);
		    IntVar v2 = getVariable(p2);

		    switch (operation) {
		    case eq :
			c = new XeqY(v1, v2);
			break;
		    case ne :
			c = new XneqY(v1, v2);
			break;
		    case lt :
			c = new XltY(v1, v2);
			break;
		    case gt :
			c = new XgtY(v1, v2);
			break;
		    case le :
			c = new XlteqY(v1, v2);
			break;
		    case ge :
			c = new XgteqY(v1, v2);
			break;
		    }
		    pose(c);
		}
	    }

	}
    }



    void float_comparison(int operation, SimpleNode node, int reifStart) {

	//   	 node.dump("");

	ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
	ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

	boolean reified = false; 
	if (p.startsWith("_reif", reifStart)) {
	    reified = true;
	}

	if (reified) { // reified constraint
	    PrimitiveConstraint c = null;
	    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);
	    IntVar v3 = getVariable(p3);

	    if (p2.getType() == 5) { // var rel float

		FloatVar v1 = getFloatVariable(p1);

		double i2 = getFloat(p2);
		switch (operation) {

		case eq :
		    if (v1.min() > i2 || v1.max() < i2) {
		    	v3.domain.in(store.level, v3, 0, 0);
			return;
		    }
		    else if (v1.min() == i2 && v1.singleton() ) {
		    	v3.domain.in(store.level, v3, 1, 1);
			return;
		    } else if (v3.max() == 0) {
			v1.domain.inComplement(store.level, v1, i2);
			return;
		    }
		    else if (v3.min() == 1) {
			v1.domain.in(store.level, v1, i2, i2);
			return;
		    }
		    else
			c = new PeqC(v1, i2);
		    break;

		case ne :
		    if (v1.min() > i2 || v1.max() < i2) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (v1.min() == i2 && v1.singleton() ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    } else if (v3.max() == 0) {
			v1.domain.in(store.level, v1, i2, i2);
			return;
		    }
		    else if (v3.min() == 1) {
			v1.domain.inComplement(store.level, v1, i2);
			return;
		    }
		    else
			c = new PneqC(v1, i2);
		    break;
		case lt :
		    if (v1.max() < i2) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (v1.min() >= i2 ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new PltC(v1, i2);
		    break;
		case le :
		    if (v1.max() <= i2) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (v1.min() > i2 ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new PlteqC(v1, i2);
		    break;
		// case gt :
		//     if (v1.min() > i2) {
		// 	v3.domain.in(store.level, v3, 1, 1);
		// 	return;
		//     }
		//     else if (v1.max() <= i2 ) {
		// 	v3.domain.in(store.level, v3, 0, 0);
		// 	return;
		//     }
		//     else
		// 	c = new PgtC(v1, i2);
		//     break;
		// case ge :
		//     if (v1.min() >= i2) {
		// 	v3.domain.in(store.level, v3, 1, 1);
		// 	return;
		//     }
		//     else if (v1.max() < i2 ) {
		// 	v3.domain.in(store.level, v3, 0, 0);
		// 	return;
		//     }
		//     else
		// 	c = new PgteqC(v1, i2);
		//     break;
		}
	    } else if (p1.getType() == 5) { // float rel var
		FloatVar v2 = getFloatVariable(p2);
		double i1 = getFloat(p1);

		switch (operation) {

		case eq :
		    if (v2.min() > i1 || v2.max() < i1) {
		    	v3.domain.in(store.level, v3, 0, 0);
			return;
		    }
		    else if (v2.min() == i1 && v2.singleton() ) {
		    	v3.domain.in(store.level, v3, 1, 1);
			return;
		    }
		    else if (v3.max() == 0) {
			v2.domain.inComplement(store.level, v2, i1);
			return;
		    }
		    else if (v3.min() == 1) {
			v2.domain.in(store.level, v2, i1, i1);
			return;
		    }
		    else
			c = new PeqC(v2, i1);
		    break;

		case ne :
		    if (v2.min() > i1 || v2.max() < i1) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (v2.min() == i1 && v2.singleton() ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new PneqC(v2, i1);
		    break;
		case lt :
		    if (i1 < v2.min()) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (i1 >= v2.max() ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new PgtC(v2, i1);
		    break;
		case le :
		    if (i1 <= v2.min()) {
		    	v3.domain.in(store.level, v3, 1, 1);
		    	return;
		    }
		    else if (i1 > v2.max() ) {
		    	v3.domain.in(store.level, v3, 0, 0);
		    	return;
		    }
		    else
			c = new PgteqC(v2, i1);
		    break;
		// case gt :
		//     if (i1 > v2.max()) {
		// 	v3.domain.in(store.level, v3, 1, 1);
		// 	return;
		//     }
		//     else if (i1 <= v2.min() ) {
		// 	v3.domain.in(store.level, v3, 0, 0);
		// 	return;
		//     }
		//     else
		// 	c = new PltC(v2, i1);
		//     break;
		// case ge :
		//     if (i1 > v2.max()) {
		//     	v3.domain.in(store.level, v3, 1, 1);
		//     	return;
		//     }
		//     else if (i1 < v2.min() ) {
		//     	v3.domain.in(store.level, v3, 0, 0);
		//     	return;
		//     }
		//     else
		//     	c = new PlteqC(v2, i1);
		//     break;
		}
	    } else { // var rel var
		FloatVar v1 = getFloatVariable(p1);
		FloatVar v2 = getFloatVariable(p2);

		switch (operation) {
		case eq :
		    c = new PeqQ(v1, v2);
		    break;
		case ne :
		    c = new PneqQ(v1, v2);
		    break;
		case lt :
		    c = new PltQ(v1, v2);
		    break;
		case le :
		    c = new PlteqQ(v1, v2);
		    break;
		// case gt :
		//     c = new PgtQ(v1, v2);
		//     break;
		// case ge :
		//     c = new PgteqQ(v1, v2);
		//     break;
		}
	    }

 	    Constraint cr = new Reified(c, v3);
 	    pose(cr);
	}
	else  { // not reified constraints

	    if (p1.getType() == 5) { // first parameter float
		if (p2.getType() == 0 || p2.getType() == 1) { // first parameter float & second parameter float
		    double i1 = getFloat(p1);
		    double i2 = getFloat(p2);
		    switch (operation) {
		    case eq :
			if (i1 != i2) throw Store.failException;
			break;
		    case ne :
			if (i1 == i2) throw Store.failException;
			break;
		    case lt :
			if (i1 >= i2) throw Store.failException;
			break;
		    case le :
			if (i1 > i2) throw Store.failException;
			break;
		    // case gt :
		    // 	if (i1 <= i2) throw Store.failException;
		    // 	break;
		    // case ge :
		    // 	if (i1 < i2) throw Store.failException;
		    // 	break;
		    }
		} 
		else { // first parameter float & second parameter var

		    double i1 = getFloat(p1);
		    FloatVar v2 = getFloatVariable(p2);

		    switch (operation) {
		    case eq :
			v2.domain.in(store.level, v2, i1, i1);
			break;
		    case ne :
			v2.domain.inComplement(store.level, v2, i1);
			break;
		    case lt :
			v2.domain.in(store.level, v2, FloatDomain.next(i1), VariablesParameters.MAX_FLOAT);
			break;
		    case le :
			v2.domain.in(store.level, v2, i1, VariablesParameters.MAX_FLOAT);
			break;
		    // case gt :
		    // 	v2.domain.in(store.level, v2, IntDomain.MinInt, i1-1);
		    // 	break;
		    // case ge :
		    // 	v2.domain.in(store.level, v2, IntDomain.MinInt, i1);
		    // 	break;
		    }
		}
	    }
	    else { // first parameter var
		if (p2.getType() == 5) { // first parameter var & second parameter float

		    FloatVar v1 = getFloatVariable(p1);
		    double i2 = getFloat(p2);

		    switch (operation) {
		    case eq :
			v1.domain.in(store.level, v1, i2, i2);
			break;
		    case ne :
			v1.domain.inComplement(store.level, v1, i2);
			break;
		    case lt :
			v1.domain.in(store.level, v1, VariablesParameters.MIN_FLOAT, i2-1);
			break;
		    case le :
			v1.domain.in(store.level, v1, VariablesParameters.MIN_FLOAT, i2);
			break;
		    // case gt :
		    // 	v1.domain.in(store.level, v1, i2+1, VariablesParameters.MAX_FLOAT);
		    // 	break;
		    // case ge :
		    // 	v1.domain.in(store.level, v1, i2, VariablesParameters.MAX_FLOAT);
		    // 	break;
		    }

		} 
		else { // first parameter var & second parameter var

		    PrimitiveConstraint c = null;
		    FloatVar v1 = getFloatVariable(p1);
		    FloatVar v2 = getFloatVariable(p2);

		    switch (operation) {
		    case eq :
			c = new PeqQ(v1, v2);
			break;
		    case ne :
			c = new PneqQ(v1, v2);
			break;
		    case lt :
			c = new PltQ(v1, v2);
			break;
		    case le :
			c = new PlteqQ(v1, v2);
			break;
		    // case gt :
		    // 	c = new PgtQ(v1, v2);
		    // 	break;
		    // case ge :
		    // 	c = new PgteqQ(v1, v2);
		    // 	break;
		    }
		    pose(c);
		}
	    }

	}
    }

//     void int_comparison(int operation, SimpleNode node, int reifStart) throws FailException {

// 	//   	 node.dump("");

// 	ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
// 	ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

// 	PrimitiveConstraint c = null;

// 	if (p2.getType() == 0) { // var rel int
// 	    int i2 = getInt(p2);
// 	    IntVar v1 = getVariable(p1);
// 	    switch (operation) {
// 	    case eq :
// 		c = new XeqC(v1, i2);
// 		break;
// 	    case ne :
// 		c = new XneqC(v1, i2);
// 		break;
// 	    case lt :
// 		c = new XltC(v1, i2);
// 		break;
// 	    case gt :
// 		c = new XgtC(v1, i2);
// 		break;
// 	    case le :
//  		c = new XlteqC(v1, i2);
// 		break;
// 	    case ge :
// 		c = new XgteqC(v1, i2);
// 		break;
// 	    }
// 	} else if (p1.getType() == 0) { // int rel var
// 	    int i1 = getInt(p1);
// 	    IntVar v2 = getVariable(p2);
// 	    switch (operation) {
// 	    case eq :
// 		c = new XeqC(v2, i1);
// 		break;
// 	    case ne :
// 		c = new XneqC(v2, i1);
// 		break;
// 	    case lt :
// 		c = new XgtC(v2, i1);
// 		break;
// 	    case gt :
// 		c = new XltC(v2, i1);
// 		break;
// 	    case le :
//  		c = new XgteqC(v2, i1);
// 		break;
// 	    case ge :
// 		c = new XlteqC(v2, i1);
// 		break;
// 	    }
// 	}
// 	else { // var rel var
// 	    IntVar v1 = getVariable(p1);
// 	    IntVar v2 = getVariable(p2);
// 	    switch (operation) {
// 	    case eq :
// 		c = new XeqY(v1, v2);
// 		break;
// 	    case ne :
// 		c = new XneqY(v1, v2);
// 		break;
// 	    case lt :
// 		c = new XltY(v1, v2);
// 		break;
// 	    case gt :
// 		c = new XgtY(v1, v2);
// 		break;
// 	    case le :
// 		c = new XlteqY(v1, v2);
// 		break;
// 	    case ge :
// 		c = new XgteqY(v1, v2);
// 		break;
// 	    }
// 	}
// 	if (p.startsWith("_reif", reifStart)) {
// 	    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);
// 	    IntVar v3 = getVariable(p3);
// 	    Constraint cr = new Reified(c, v3);
// 	    pose(cr);
// 	}
// 	else {
// 	    pose(c);
// 	}
//     }

    void int_lin_relation(int operation, SimpleNode node) throws FailException {
	// int_lin_*[_reif] (* = eq | ne | lt | gt | le | ge)

	// node.dump("");

	int[] p1 = getIntArray((SimpleNode)node.jjtGetChild(0));
	IntVar[] p2 = getVarArray((SimpleNode)node.jjtGetChild(1));

	// Case for bool_lin_eq
	if (((ASTConstElem)node).getName().equals("bool_lin_eq")) {// if bool_lin_eq allow p3 to be variable

	    IntVar par3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

	    // If a linear term contains only constants and can be evaluated 
	    // check if satisfied and do not generate constraint
	    if (par3.min() == par3.max() && allConstants(p2)) {
		int el=0, s=0;
		while (el < p2.length) {
		    s += p2[el].min()*p1[el];
		    el++;
		}
		if (s == par3.min())
		    return;
		else
		    throw store.failException;
	    }

	    Constraint c = new SumWeight(p2, p1, par3);
	    // System.out.println (c);

	    pose(c);
	    return;
	}

	int p3 = getInt((ASTScalarFlatExpr)node.jjtGetChild(2));

	// Possible overflow because of too high weigts in SumWeight
	for (int i = 0; i < p1.length; i++)
	    if (p1[i] >= IntDomain.MaxInt || p1[i] <= IntDomain.MinInt) {
		int min = p2[i].domain.multiply(p1[i], p2[i].min());
		int max = p2[i].domain.multiply(p1[i], p2[i].max());
		if (min >= IntDomain.MaxInt || min <= IntDomain.MinInt || max >= IntDomain.MaxInt || max <= IntDomain.MinInt)
		    throw new ArithmeticException("Too high or low value for domain assignment");
	    }


	if (p.startsWith("_reif", 10)) { // reified
	    IntVar p4 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(3));

	    IntVar t;
	    switch (operation) {
	    case eq :
		if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
		    pose(new Reified(new XplusCeqZ(p2[1], p3, p2[0]), p4));
		}
		else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
		    pose(new Reified(new XplusCeqZ(p2[0], p3, p2[1]), p4));
		} 
		else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
		    pose(new Reified(new XplusYeqC(p2[0], p2[1], p3), p4));
		} 
		else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
		    pose(new Reified(new XplusYeqC(p2[0], p2[1], -p3), p4));
		} 
		else {
		    // t = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
		    // if (allWeightsOne(p1))
		    // 	pose(new Sum(p2, t));
		    // else
		    // 	pose(new SumWeight(p2, p1, t));
		    // pose(new Reified(new XeqC(t, p3), p4));
		    pose(new Reified(new Linear(store, p2, p1, "==", p3), p4));
		}
		break;
	    case ne :
		// t = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
		// pose(new SumWeight(p2, p1, t));
		// pose(new Reified(new XneqC(t, p3), p4));
		if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
		    pose(new Reified(new Not(new XplusCeqZ(p2[1], p3, p2[0])), p4));
		}
		else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
		    pose(new Reified(new Not(new XplusCeqZ(p2[0], p3, p2[1])), p4));
		} 
		else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
		    pose(new Reified(new Not(new XplusYeqC(p2[0], p2[1], p3)), p4));
		} 
		else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
		    pose(new Reified(new Not(new XplusYeqC(p2[0], p2[1], -p3)), p4));
		} 
		else 
		    pose(new Reified(new Linear(store, p2, p1, "!=", p3), p4));
		break;
	    case lt :
		// t = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
		// pose(new SumWeight(p2, p1, t));
		// pose(new Reified(new XltC(t, p3), p4));
		pose(new Reified(new Linear(store, p2, p1, "<", p3), p4));
		break;
		// gt not present in the newest flatzinc version
	    // case gt :
	    // 	t = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
	    // 	pose(new SumWeight(p2, p1, t));
	    // 	pose(new Reified(new XgtC(t, p3), p4));
	    // 	break;
	    case le :
		if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) 
		    pose(new Reified(new org.jacop.constraints.XplusClteqZ(p2[0], -p3, p2[1]), p4));
		else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) 
		    pose(new Reified(new org.jacop.constraints.XplusClteqZ(p2[1], -p3, p2[0]), p4));
		else if (p1.length == 1 && p1[0] == 1) 
		    pose(new Reified(new org.jacop.constraints.XlteqC(p2[0], p3), p4));
		else if (p1.length == 1 && p1[0] == -1) 
		    pose(new Reified(new org.jacop.constraints.XgteqC(p2[0], -p3), p4));
		else if (allWeightsOne(p1)) {
		    t = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
		    pose(new Sum(p2, t));
		    pose(new Reified(new XlteqC(t, p3), p4));
		}
		else {
		    // t = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
		    // pose(new SumWeight(p2, p1, t));
		    // pose(new Reified(new XlteqC(t, p3), p4));
		    pose(new Reified(new Linear(store,p2, p1, "<=", p3), p4));
		}
		break;
		// ge not present in the newest flatzinc version
	    // case ge :
	    // 	t = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
	    // 	pose(new SumWeight(p2, p1, t));
	    // 	pose(new Reified(new XgteqC(t, p3), p4));
	    // 	break;
	    default:
		System.err.println("%% ERROR: Constraint "+p+" not supported.");
		System.exit(0);
	    }
	}
	else { // non reified

	    // If a linear term contains only constants and can be evaluated 
	    // check if satisfied and do not generate constraint

	    boolean p2Fixed = allConstants(p2);
	    int s=0;
	    if (p2Fixed) {
		int el=0;
		while (el < p2.length) {
		    s += p2[el].min()*p1[el];
		    el++;
		}
	    }

	    IntVar t;
	    switch (operation) {
	    case eq :

		if (p2Fixed)
		    if (s == p3)
			return;
		    else
			throw store.failException;

		if (p1.length == 1) {
		    pose(new XmulCeqZ(p2[0], p1[0], new IntVar(store, p3, p3)));
		}
		else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
		    if (p3 != 0)
			pose(new XplusCeqZ(p2[1], p3, p2[0]));
		    else
			pose(new XeqY(p2[1], p2[0]));
		}
		else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
		    if (p3 != 0) {
			    pose(new XplusCeqZ(p2[0], p3, p2[1]));
		    }
		    else
			pose(new XeqY(p2[0], p2[1]));
		}
		else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
		    pose(new XplusYeqC(p2[0], p2[1], p3));
		} 
		else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
		    if (p3 == 0)
			pose(new XplusYeqC(p2[0], p2[1], p3));
		    else
			pose(new XplusYeqC(p2[0], p2[1], -p3));
		}
		else if (domainConsistency && (maxDomain(p2) <= 4 || p2.length <= 2) ) { // heuristic rule to select domain consistency since 
		                                                                         // its complexity is O(d^n), d <= 4 or n <= 2 ;)
		    // We do not impose linear constraint with domain consistency if 
		    // the cases are covered by four cases above.

		    pose(new SumWeightDom(p2, p1, p3));
		}
		else if ( (p3 == 0 && p1.length == 3) && 
		     ((p1[0] == -1 && p1[1] == -1 && p1[2] == 1) || (p1[0] == 1 && p1[1] == 1 && p1[2] == -1)) )
		    pose(new XplusYeqZ(p2[0], p2[1], p2[2]));
		    // pose(new Linear(store, p2, p1, "==", p3));
		else {
		    // IntVar v;
		    // if (p3==0) 
		    // 	v = zero;
		    // else if (p3 == 1) 
		    // 	v = one;
		    // else 
		    // 	v = new IntVar(store, p3, p3);
		    if (sumPossible(p1, p3) > -1) {
			int pos = sumPossible(p1, p3);
			IntVar[] vect = new IntVar[p1.length-1];
			int n = 0;
			for (int i=0; i<p2.length; i++)
			    if (i != pos)
				vect[n++] = p2[i];
			pose(new Sum(vect, p2[pos]));
		    }
		    else if (allWeightsOne(p1)) {
			IntVar v;
			if (p3==0) 
			    v = zero;
			else if (p3 == 1) 
			    v = one;
			else
			    v = new IntVar(store, p3, p3);
			pose(new Sum(p2, v));
		    }
		    else if (allWeightsMinusOne(p1)) {
			IntVar v;
			if (p3==0) 
			    v = zero;
			else
			    v = new IntVar(store, -p3, -p3);
			pose(new Sum(p2, v));
		    }
		    // else if (p3 == 0) 
		    // 	if (sumPossible1(p1)) { // case when weights are [1, -1, ..., -1] or [-1, 1, ..., 1]
 		    // 	    IntVar[] vars = new IntVar[p2.length-1];
 		    // 	    for (int i=1; i<p2.length; i++)
 		    // 		vars[i-1] = p2[i];
 		    // 	    pose(new Sum(vars, p2[0]));
		    // 	}
		    // 	else if (sumPossible2(p1)) { // case when weights are [-1, ..., -1, 1] or [1, ..., 1, -1]
		    // 	    IntVar[] vars = new IntVar[p2.length-1];
		    // 	    for (int i=0; i<p2.length-1; i++)
		    // 		vars[i] = p2[i];
		    // 	    pose(new Sum(vars, p2[p2.length-1]));
		    // 	}
		    // 	else {
		    // 	    // pose(new SumWeight(p2, p1, v));
		    // 	    pose(new Linear(store, p2, p1, "==", p3));
		    // 	}
		    else {
			/*
 			ArrayList<IntVar> multipliedByOne = new ArrayList<IntVar>();
			ArrayList<IntVar> others = new ArrayList<IntVar>();
			ArrayList<Integer> othersWeights = new ArrayList<Integer>();
			if (p1.length > 100) {
			    for (int i = 0; i < p1.length; i++) 
				if (p1[i] == 1)
				    multipliedByOne.add(p2[i]);
				else {
				    others.add(p2[i]);
				    othersWeights.add(p1[i]);
				}
			    if (multipliedByOne.size() > 0) {
				IntVar tmp1 = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
				IntVar tmp2 = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
				pose(new Sum(multipliedByOne, tmp1));
				pose(new SumWeight(others, othersWeights, tmp2));
				pose(new XplusYeqC(tmp1, tmp2, p3));
				return;
			    }
			}
			*/

			// pose(new SumWeight(p2, p1, v));
			pose(new Linear(store, p2, p1, "==", p3));
		    }
		}
		break;
	    case ne :

		if (p2Fixed)
		    if (s != p3)
			return;
		    else
			throw store.failException;

 		if (p1.length == 2 && p3 == 0 && ( (p1[0] == 1 && p1[1] == -1) || (p1[0] == -1 && p1[1] == 1) ))
			pose(new XneqY(p2[0], p2[1]));
		else {
		    // IntervalDomain dne = new IntervalDomain(IntDomain.MinInt, p3-1);
		    // dne.unionAdapt(p3+1, IntDomain.MaxInt);
		    // t = new IntVar(store, "", dne);
		    // pose(new SumWeight(p2, p1, t));
		    pose(new Linear(store, p2, p1, "!=", p3));
		}
		break;
	    case lt :

		if (p2Fixed)
		    if (s < p3)
			return;
		    else
			throw store.failException;

 		if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
		    pose(new XltY(p2[0], p2[1]));
 		else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
		    pose(new XltY(p2[1], p2[0]));
		else {
		    //t = new IntVar(store, IntDomain.MinInt, p3-1);
		    //pose(new SumWeight(p2, p1, t));
		    pose(new Linear(store, p2, p1, "<", p3));
		}
		break;
	    // gt not present in the newest flatzinc version
	    // case gt :
 	    // 	if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
	    // 	    pose(new XgtY(p2[0], p2[1]));
 	    // 	else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
	    // 	    pose(new XgtY(p2[0], p2[1]));
	    // 	else {
	    // 	    t = new IntVar(store, p3+1, IntDomain.MaxInt);
	    // 	    pose(new SumWeight(p2, p1, t));
	    // 	}
	    // 	break;
	    case le :

		if (p2Fixed)
		    if (s <= p3)
			return;
		    else
			throw store.failException;

		if (p1.length == 1) {

		    if (p1[0] < 0) {
			int rhsValue = (int)( Math.round( Math.ceil ( ((float)(p3/p1[0])) )));

			p2[0].domain.inMin(store.level, p2[0], rhsValue);
			if (debug)
			    System.out.println ("Pruned variable " + p2[0] + " to be >= " + rhsValue);

			// pose(new XgteqC(p2[0], rhsValue));
		    }
		    else { // weight > 0
			int rhsValue = (int)( Math.round( Math.floor ( ((float)(p3/p1[0])) )));

			p2[0].domain.inMax(store.level, p2[0], rhsValue);

			if (debug)
			    System.out.println ("Pruned variable " + p2[0] + " to be <= " + rhsValue);
			// pose(new XlteqC(p2[0], rhsValue));
		    }
		}
 		else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
		    pose(new XlteqY(p2[0], p2[1]));
 		else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
		    pose(new XlteqY(p2[1], p2[0]));
		else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) 
		    pose(new XplusClteqZ(p2[0], -p3, p2[1]) );
		else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1)
		    pose(new XplusClteqZ(p2[1], -p3, p2[0]) );

		// else if (allWeightsOne(p1)) {
		//     t = new IntVar(store, IntDomain.MinInt, p3);
		//     pose(new Sum(p2, t));		    
		// }
		// else if (allWeightsMinusOne(p1)) {
		//     t = new IntVar(store, -p3, IntDomain.MaxInt);
		//     pose(new Sum(p2, t));		    
		// }
		// else if (sumPossible(p1, p3) > -1) {
		//     int pos = sumPossible(p1, p3);
		//     IntVar[] vect = new IntVar[p1.length-1];
		//     int n = 0;
		//     for (int i=0; i<p2.length; i++)
		// 	if (i != pos)
		// 	    vect[n++] = p2[i];
		//     IntVar le = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
		//     pose(new XlteqY(le, p2[pos]));
		//     pose(new Sum(vect, le));
		// }

		else {
		    // t = new IntVar(store, IntDomain.MinInt, p3);
		    // pose(new SumWeight(p2, p1, t));
		    pose(new Linear(store, p2, p1, "<=", p3));
		}
		break;
		// ge not present in the newest flatzinc version
	    // case ge :
 	    // 	if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
	    // 	    pose(new XgteqY(p2[0], p2[1]));
 	    // 	else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
	    // 	    pose(new XgteqY(p2[1], p2[0]));
	    // 	else {
	    // 	    t = new IntVar(store, p3, IntDomain.MaxInt);
	    // 	    pose(new SumWeight(p2, p1, t));
	    // 	}
	    // 	break;
		default:
		    System.err.println("%% ERROR: Constraint "+p+" not supported.");
		    System.exit(0);
	    }
	}
    }

    int maxDomain(IntVar[] vs) {
	int s = IntDomain.MinInt;

	for (IntVar v : vs) 
	    s = (s > v.getSize()) ? s : v.getSize();
	
	return s;

    }

    void float_lin_relation(int operation, SimpleNode node) throws FailException {
	// float_lin_*[_reif] (* = eq | ne | lt | gt | le | ge)

	// node.dump("");
	double[] p1 = getFloatArray((SimpleNode)node.jjtGetChild(0));
	FloatVar[] p2 = getFloatVarArray((SimpleNode)node.jjtGetChild(1));

	double p3 = getFloat((ASTScalarFlatExpr)node.jjtGetChild(2));

	if (p.startsWith("_reif", 12)) { // reified
	    IntVar p4 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(3));

	    switch (operation) {
	    case eq :
		pose(new Reified(new LinearFloat(store, p2, p1, "==", p3), p4));
		break;
	    case ne :
		pose(new Reified(new LinearFloat(store, p2, p1, "!=", p3), p4));
		break;
	    case lt :
		pose(new Reified(new LinearFloat(store, p2, p1, "<", p3), p4));
		break;
	    case le :
		pose(new Reified(new LinearFloat(store,p2, p1, "<=", p3), p4));
		break;
	    default:
		System.err.println("%% ERROR: Constraint "+p+" not supported.");
		System.exit(0);
	    }
	}
	else { // non reified
	    switch (operation) {
	    case eq :

		if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
		    if (p3 != 0)
			pose(new PplusCeqR(p2[1], p3, p2[0]));
		    else
			pose(new PeqQ(p2[1], p2[0]));
		}
		else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
		    if (p3 != 0) {
			    pose(new PplusCeqR(p2[0], p3, p2[1]));
		    }
		    else
			pose(new PeqQ(p2[0], p2[1]));
		}
		else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
		    pose(new PplusQeqR(p2[0], p2[1], new FloatVar(store, p3,p3)));
		} 
		else
		    pose(new LinearFloat(store, p2, p1, "==", p3));
		break;
	    case ne :
		pose(new LinearFloat(store, p2, p1, "!=", p3));
		break;
	    case lt :
		pose(new LinearFloat(store, p2, p1, "<", p3));
		break;
	    case le :
		pose(new LinearFloat(store, p2, p1, "<=", p3));
		break;
		default:
		    System.err.println("%% ERROR: Constraint "+p+" not supported.");
		    System.exit(0);
	    }
	}
    }

    boolean allWeightsOne(int[] w) {
	//boolean allOne=true;
	for (int i=0; i<w.length; i++)
	    if (w[i] != 1)
		return false;
	return true;
    }

    boolean allWeightsMinusOne(int[] w) {
    	//boolean allOne=true;
    	for (int i=0; i<w.length; i++)
    	    if (w[i] != -1)
    		return false;
    	return true;
    }

    /*
    boolean allWeightsOneOrMinusOne(int[] w) {
	boolean allOne = true;
	for (int i=0; i<w.length; i++) 
	    if (w[i] != 1 && w[i] != -1)
		return false;
	return true;
    }
    */

    int sumPossible(int[] ws, int result) {
	if (result == 0) {
	    int one = 0, minusOne = 0;
	    int lastOnePosition = -1, lastMinusOnePosition = -1;
	    //boolean sum = true;
	    for (int i=0; i<ws.length; i++)
		if (ws[i] == 1) {
		    one++;
		    lastOnePosition = i;
		}
		else if (ws[i] == -1) {
		    minusOne++;
		    lastMinusOnePosition = i;
		}

	    if (one == 1 && minusOne == ws.length - 1)
		return lastOnePosition;
	    else if (minusOne == 1 && one == ws.length - 1)
		return lastMinusOnePosition;
	    else
		return -1;
	}
	else
	    return -1;
    }

    /*
    boolean sumPossible1(int[] w) {
	//boolean sum = true;
	if (w[0] == 1) {
	    for (int i=1; i<w.length; i++) 
		if (w[i] != -1)
		    return false;
	}
	else  if (w[0] == -1) {
	    for (int i=1; i<w.length; i++) 
		if (w[i] != 1)
		    return false;
	}
	else
	    return false;
	return true;
    }

    boolean sumPossible2(int[] w) {
	//boolean sum = true;
	if (w[w.length-1] == 1) {
	    for (int i=0; i<w.length-1; i++) 
		if (w[i] != -1)
		    return false;
	}
	else if (w[w.length-1] == -1) {
	    for (int i=0; i<w.length-1; i++) 
		if (w[i] != 1)
		    return false;
	}
	else
	    return false;
	return true;
    }
    */

    void generateIntElementConstraint(SimpleNode node) throws FailException {

	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
	int[] p2 = getIntArray((SimpleNode)node.jjtGetChild(1));
	IntVar p3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

	// // element using ExtensionalSupportSTR
	// int[][] rel = new int[p2.length][2];
	// for (int i=0; i<p2.length; i++) {
	//     rel[i][0] = i+1;
	//     rel[i][1] = p2[i];
	// }
	// pose(new org.jacop.constraints.ExtensionalSupportVA(new IntVar[] {p1, p3}, rel));

	/*
	if (listEqualIndex(p2)) {
	    pose(new XeqY(p1, p3));

	    return;
	}
	*/

	p1.domain.in(store.level, p1, 1, IntDomain.MaxInt);

	int newP2Length = p1.max() - p1.min() + 1;
	int listLength = (p2.length < newP2Length) ? p2.length : newP2Length;
	int[] newP2 = new int[listLength];
	for (int i=0; i < listLength; i++) 
	    newP2[i] = p2[p1.min() - 1 + i];

	pose(new Element(p1, newP2, p3, p1.min() - 1));


	// pose(new Element(p1, p2, p3));
    }

    /*
    boolean listEqualIndex(int[] p) {
	int n = 1;
	for (int i = 0; i < p.length; i++) {
	    if (p[i] == n++)
		continue;
	    else
		return false;
	}
	return true;
    }
    */

    void generateVarElementConstraint(SimpleNode node) throws FailException {
	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));	    
	IntVar p3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

// 	int[] p2 = getIntArray((SimpleNode)node.jjtGetChild(1));
// 	if (p2 != null)
// 	    pose(new Element(p1, p2, p3));
// 	else {
	IntVar[] p2var = getVarArray((SimpleNode)node.jjtGetChild(1));

	pose(new Element(p1, p2var, p3));

// 	}
    }

    void generateSetElementConstraint(SimpleNode node) throws FailException {
	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
	IntDomain[] p2 = getSetArray((SimpleNode)node.jjtGetChild(1));
	SetVar p3 = getSetVariable(node, 2);

	for (int i=0; i < p2.length; i++)
	    if (p2[i] == null) {
	    System.err.println("%% var_set_element with list of set variables is not avaible in org.jacop.set");
	    System.exit(0);
	}
	
	pose(new ElementSet(p1, p2, p3));
    }

    void generateVarSetElementConstraint(SimpleNode node) throws FailException {

	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
	SetVar p3 = getSetVariable(node, 2);

	IntDomain[] p2 = getSetArray((SimpleNode)node.jjtGetChild(1));
	if (p2 != null) {

	    for (int i=0; i < p2.length; i++)
		if (p2[i] == null) {
		    System.err.println("%% var_set_element with list of set variables is not avaible in org.jacop.set");
		    System.exit(0);
		}
	    
	    pose(new ElementSet(p1, p2, p3));

	}
	else {
	    System.err.println("%% var_set_element with list of set variables is not avaible in org.jacop.set");
	    System.exit(0);
	}
    }


    void generateFloatElementConstraint(SimpleNode node) throws FailException {

	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
	double[] p2 = getFloatArray((SimpleNode)node.jjtGetChild(1));
	FloatVar p3 = getFloatVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

	p1.domain.in(store.level, p1, 1, IntDomain.MaxInt);

	int newP2Length = p1.max() - p1.min() + 1;
	int listLength = (p2.length < newP2Length) ? p2.length : newP2Length;
	double[] newP2 = new double[listLength];
	for (int i=0; i < listLength; i++) 
	    newP2[i] = p2[p1.min() - 1 + i];

	pose(new ElementFloat(p1, newP2, p3, p1.min() - 1));


	// pose(new ElementFloat(p1, p2, p3));
    }

    int getInt(ASTScalarFlatExpr node) {
	intPresent = true;

	if (node.getType() == 0) //int
	    return node.getInt();
	if (node.getType() == 1) //bool
	    return node.getInt();
	else if (node.getType() == 2) // ident
	    return dictionary.getInt(node.getIdent());
	else if (node.getType() == 3) {// array access
	    int[] intTable = dictionary.getIntArray(node.getIdent());
	    if (intTable == null) {
		intPresent = false;
		return Integer.MIN_VALUE;
	    }
	    else
		return intTable[node.getInt()];
	}
	else {
	    System.err.println("getInt: Wrong parameter " + node);
	    System.exit(0);
	    return 0;
	}
    }

    double getFloat(ASTScalarFlatExpr node) {
	floatPresent = true;

	if (node.getType() == 5) //int
	    return node.getFloat();
	else if (node.getType() == 2) // ident
	    return dictionary.getFloat(node.getIdent());
	else if (node.getType() == 3) {// array access
	    double[] floatTable = dictionary.getFloatArray(node.getIdent());
	    if (floatTable == null) {
		floatPresent = false;
		return VariablesParameters.MIN_FLOAT;
	    }
	    else
		return floatTable[node.getInt()];
	}
	else {
	    System.err.println("getFloat: Wrong parameter " + node);
	    System.exit(0);
	    return 0;
	}
    }

    int getScalarFlatExpr(SimpleNode node, int i) {
	SimpleNode child = (SimpleNode)node.jjtGetChild(i);
	if (child.getId() == JJTSCALARFLATEXPR) {
	    switch ( ((ASTScalarFlatExpr)child).getType() ) {
	    case 0: // int
		return ((ASTScalarFlatExpr)child).getInt();
	    case 1: // bool
		return ((ASTScalarFlatExpr)child).getInt();
	    case 2: // ident
		return dictionary.getInt(((ASTScalarFlatExpr)child).getIdent());
	    case 3: // array acces
		return dictionary.getIntArray(((ASTScalarFlatExpr)child).getIdent())[((ASTScalarFlatExpr)child).getInt()];
	    default: // string & float;
		System.err.println("Not supported scalar in parameter; compilation aborted."); 
		System.exit(0);
	    }
	}
	else {
	    System.err.println("Not supported parameter assignment; compilation aborted."); 
	    System.exit(0);
	}
	return -1;
    }

    // TODO, the functions below look awfully familiar to the functions from the Tables.java, maybe to be consistent they should be in Tables?
	
    IntDomain[] getSetArray(SimpleNode node) {
	IntDomain[] s=null;
	int arrayIndex=0;

	if (node.getId() == JJTARRAYLITERAL) {
	    int count = node.jjtGetNumChildren();
	    s = new IntDomain[count];
	    for (int i=0; i<count; i++) {
		s[arrayIndex++] = getSetLiteral(node, i);
	    }
	}
	else if (node.getId() == JJTSCALARFLATEXPR) {
	    if ( ((ASTScalarFlatExpr)node).getType() == 2) {// ident
		s = dictionary.getSetArray(((ASTScalarFlatExpr)node).getIdent());
		if (s == null) { // there is still a chance that the var_array has constant sets ;)
		    SetVar[] sVar = dictionary.getSetVariableArray(((ASTScalarFlatExpr)node).getIdent());
		    int numberSingleton=0;
		    for (int i=0; i<sVar.length; i++)
			if (sVar[i].singleton())
			    numberSingleton++;
		    if (sVar.length == numberSingleton) {
			s = new IntDomain[sVar.length];
			for (int i=0; i<sVar.length; i++)
			    s[i] = sVar[i].dom().glb();
// 			    System.out.println(((SetDomain)sVar[i].dom()).glb());
		    }
		}
	    }
	    else {
		System.err.println("Wrong set array."); 
		System.exit(0);
	    }
	}
	return s;
    }

    IntDomain getSetLiteral(SimpleNode node, int index) {
	SimpleNode child = (SimpleNode)node.jjtGetChild(index);
	if (child.getId() == JJTSETLITERAL) {
	    switch ( ((ASTSetLiteral)child).getType() ) {
	    case 0: // interval
		SimpleNode grand_child_1 = (SimpleNode)child.jjtGetChild(0);
		SimpleNode grand_child_2 = (SimpleNode)child.jjtGetChild(1);
		if (grand_child_1.getId() == JJTINTFLATEXPR && grand_child_2.getId() == JJTINTFLATEXPR) {
		    int i1 = ((ASTIntFlatExpr)grand_child_1).getInt();
		    int i2 = ((ASTIntFlatExpr)grand_child_2).getInt();
		    return new IntervalDomain(i1, i2);
		}
	    case 1: // list
		IntDomain s= new IntervalDomain();
		int el=-1111;
		int count = child.jjtGetNumChildren();
		for (int i=0; i<count; i++) {
		    el = getScalarFlatExpr(child, i);
		    s.unionAdapt(el);
		}
		return s;
	    default: 
		System.err.println("Set type not supported; compilation aborted."); 
		System.exit(0);
	    }
	}
	else if (child.getId() == JJTSCALARFLATEXPR) {
	    switch ( ((ASTScalarFlatExpr)child).getType() ) {
	    case 0: // int
	    case 1: // bool
		System.err.println("Set initialization fault; compilation aborted."); 
		System.exit(0);
		break;
	    case 2: // ident
		return dictionary.getSet(((ASTScalarFlatExpr)child).getIdent());
	    case 3: // array access
		return dictionary.getSetArray(((ASTScalarFlatExpr)child).getIdent())[((ASTScalarFlatExpr)child).getInt()];
	    case 4: // string
	    case 5: // float
		System.err.println("Set initialization fault; compilation aborted."); 
		System.exit(0);
		break;
	    }
	}
	return new IntervalDomain();
    }

    int[] getIntArray(SimpleNode node) {
	if (node.getId() == JJTARRAYLITERAL) {
	    int count = node.jjtGetNumChildren();
	    int[] aa = new int[count];
	    for (int i=0;i<count;i++) {
		ASTScalarFlatExpr child = (ASTScalarFlatExpr)node.jjtGetChild(i);
		int el = getInt(child);
// 		if (el == Integer.MIN_VALUE)
		if (! intPresent)
		    return null;
		else
		    aa[i] = el;
	    }
	    return aa;
	}
	else if (node.getId() == JJTSCALARFLATEXPR) {
	    if (((ASTScalarFlatExpr)node).getType() == 2) // ident
		return dictionary.getIntArray(((ASTScalarFlatExpr)node).getIdent());
	    else {
		System.err.println("Wrong type of int array; compilation aborted."); 
		System.exit(0);
		return new int[] {};
	    }
	}
	else {
	    System.err.println("Wrong type of int array; compilation aborted."); 
	    System.exit(0);
	    return new int[] {};
	}
    }

    double[] getFloatArray(SimpleNode node) {
	if (node.getId() == JJTARRAYLITERAL) {
	    int count = node.jjtGetNumChildren();
	    double[] aa = new double[count];
	    for (int i=0;i<count;i++) {
		ASTScalarFlatExpr child = (ASTScalarFlatExpr)node.jjtGetChild(i);
		double el = getFloat(child);
		if (! floatPresent)
		    return null;
		else
		    aa[i] = el;
	    }
	    return aa;
	}
	else if (node.getId() == JJTSCALARFLATEXPR) {
	    if (((ASTScalarFlatExpr)node).getType() == 2) // ident
		return dictionary.getFloatArray(((ASTScalarFlatExpr)node).getIdent());
	    else {
		System.err.println("Wrong type of int array; compilation aborted."); 
		System.exit(0);
		return new double[] {};
	    }
	}
	else {
	    System.err.println("Wrong type of int array; compilation aborted."); 
	    System.exit(0);
	    return new double[] {};
	}
    }

    IntVar getVariable(ASTScalarFlatExpr node) {

	if (node.getType() == 0) {// int
	    int val = node.getInt();
	    if (val == 0) return zero;
	    else if (val == 1) return one;
	    else return new IntVar(store, val, val);
	}
	if (node.getType() == 1) {// bool
	    int val = node.getInt();
	    if (val == 0) return zero;
	    else if (val == 1) return one;
	    return new IntVar(store, val, val);
	}
	else if (node.getType() == 2) { // ident
	    IntVar int_boolVar = dictionary.getVariable(node.getIdent());
	    if (int_boolVar == null) {
		int bInt = dictionary.getInt(node.getIdent());
		return new IntVar(store, bInt, bInt);
	    }	    return int_boolVar;
	}
	else if (node.getType() == 3) {// array access
	    if (node.getInt() >= dictionary.getVariableArray(node.getIdent()).length ||
		node.getInt() < 0) {
		System.out.println("Index out of bound for " + node.getIdent() + "["+node.getInt()+"]");
		System.exit(0);
		return new IntVar(store);
	    }
	    else
		return dictionary.getVariableArray(node.getIdent())[node.getInt()];
	}
	else {
	    System.err.println("Wrong parameter " + node);
	    System.exit(0);
	    return new IntVar(store);
	}
    }

    FloatVar getFloatVariable(ASTScalarFlatExpr node) {

	if (node.getType() == 5) {// float
	    double val = node.getFloat();
	    // if (val == 0) return zero;
	    // else if (val == 1) return one;
	    // else 
	    return new FloatVar(store, val, val);
	}
	else if (node.getType() == 2) { // ident
	    FloatVar float_Var = dictionary.getFloatVariable(node.getIdent());
	    if (float_Var == null) {
		double bFloat = dictionary.getFloat(node.getIdent());
		return new FloatVar(store, bFloat, bFloat);
	    }	    return float_Var;
	}
	else if (node.getType() == 3) {// array access
	    if (node.getInt() >= dictionary.getVariableFloatArray(node.getIdent()).length ||
		node.getFloat() < 0) {
		System.out.println("Index out of bound for " + node.getIdent() + "["+node.getInt()+"]");
		System.exit(0);
		return new FloatVar(store);
	    }
	    else
		return dictionary.getVariableFloatArray(node.getIdent())[node.getInt()];
	}
	else {
	    System.err.println("getFloatVariable: Wrong parameter " + node);
	    System.exit(0);
	    return new FloatVar(store);
	}
    }

    SetVar getSetVariable(SimpleNode node, int index) {

	SimpleNode child = (SimpleNode )node.jjtGetChild(index);
	if (child.getId() == JJTSETLITERAL) {
	    int count = child.jjtGetNumChildren();
	    if (count == 0)
		return new SetVar(store, new BoundSetDomain(new IntervalDomain(), new IntervalDomain()));
	    else {
		IntDomain s2 = getSetLiteral(node, index);
		return new SetVar(store, new BoundSetDomain(s2, s2));
	    }
	}
	else if (child.getId() == JJTSCALARFLATEXPR) {
	    if (((ASTScalarFlatExpr)child).getType() == 2) { // ident
		SetVar v =  dictionary.getSetVariable(((ASTScalarFlatExpr)child).getIdent());
		if (v != null)
		    return v;  // Variable ident
		else { // Set ident
		    IntDomain s = dictionary.getSet(((ASTScalarFlatExpr)child).getIdent());
		    return new SetVar(store, new BoundSetDomain(s, s));
		}
	    }
	    else if (((ASTScalarFlatExpr)child).getType() == 3) // array access
		return dictionary.getSetVariableArray(((ASTScalarFlatExpr)child).getIdent())[((ASTScalarFlatExpr)child).getInt()];
	    else {
		System.err.println("Wrong parameter in set " + child);
		System.exit(0);
		return new SetVar(store);
	    }
	}
	else {
	    System.err.println("Wrong parameter in set " + child);
	    System.exit(0);
	    return new SetVar(store);
	}
    }

    IntVar[] getVarArray(SimpleNode node) {
	if (node.getId() == JJTARRAYLITERAL) {
	    int count = node.jjtGetNumChildren();
	    IntVar[] aa = new IntVar[count];
	    for (int i=0;i<count;i++) {
		ASTScalarFlatExpr child = (ASTScalarFlatExpr)node.jjtGetChild(i);
		IntVar el = getVariable(child);
		aa[i] = el;
	    }
	    return aa;
	}
	else if (node.getId() == JJTSCALARFLATEXPR) {
	    if (((ASTScalarFlatExpr)node).getType() == 2) {// ident
		// array of var
		IntVar[] v = dictionary.getVariableArray(((ASTScalarFlatExpr)node).getIdent());
		if (v != null)
		    return v;
		else { // array of int
		    int[] ia = dictionary.getIntArray(((ASTScalarFlatExpr)node).getIdent());
		    if (ia != null) {
			IntVar[] aa = new IntVar[ia.length];
			for (int i=0; i<ia.length; i++)
			    aa[i] = new IntVar(store, ia[i], ia[i]);
			    // aa[i] = new IntVar(store, new IntervalDomain(ia[i], ia[i]));
			return aa;
		    }
		    else {
			System.err.println("Cannot find array " +((ASTScalarFlatExpr)node).getIdent() +
					   "; compilation aborted."); 
			System.exit(0);
			return new IntVar[] {};
		    }
		}
	    }
	    else {
		System.err.println("Wrong type of Variable array; compilation aborted."); 
		System.exit(0);
		return new IntVar[] {};
	    }
	}
	else {
	    System.err.println("Wrong type of Variable array; compilation aborted."); 
	    System.exit(0);
	    return new IntVar[] {};
	}
    }

    FloatVar[] getFloatVarArray(SimpleNode node) {
	if (node.getId() == JJTARRAYLITERAL) {
	    int count = node.jjtGetNumChildren();
	    FloatVar[] aa = new FloatVar[count];
	    for (int i=0;i<count;i++) {
		ASTScalarFlatExpr child = (ASTScalarFlatExpr)node.jjtGetChild(i);
		FloatVar el = getFloatVariable(child);
		aa[i] = el;
	    }
	    return aa;
	}
	else if (node.getId() == JJTSCALARFLATEXPR) {
	    if (((ASTScalarFlatExpr)node).getType() == 2) {// ident
		// array of var
		FloatVar[] v = dictionary.getVariableFloatArray(((ASTScalarFlatExpr)node).getIdent());
		if (v != null)
		    return v;
		else { // array of int
		    double[] ia = dictionary.getFloatArray(((ASTScalarFlatExpr)node).getIdent());
		    if (ia != null) {
			FloatVar[] aa = new FloatVar[ia.length];
			for (int i=0; i<ia.length; i++)
			    aa[i] = new FloatVar(store, ia[i], ia[i]);
			return aa;
		    }
		    else {
			System.err.println("Cannot find array " +((ASTScalarFlatExpr)node).getIdent() +
					   "; compilation aborted."); 
			System.exit(0);
			return new FloatVar[] {};
		    }
		}
	    }
	    else {
		System.err.println("Wrong type of Variable array; compilation aborted."); 
		System.exit(0);
		return new FloatVar[] {};
	    }
	}
	else {
	    System.err.println("Wrong type of Variable array; compilation aborted."); 
	    System.exit(0);
	    return new FloatVar[] {};
	}
    }

    void parseAnnotations(SimpleNode constraintWithAnnotations) {

	for (int i = 1; i < constraintWithAnnotations.jjtGetNumChildren(); i++) {
	    ASTAnnotation ann = (ASTAnnotation)constraintWithAnnotations.jjtGetChild(i);

//  	    ann.dump("");
// 	    System.out.println ("ann["+i+"] = "+ ann.getAnnId());

	    if ( ann.getAnnId().equals("bounds") || ann.getAnnId().equals("boundsZ") ) {
		boundsConsistency = true; 
		domainConsistency = false;
	    }
	    else if ( ann.getAnnId().equals("domain") ) {
		boundsConsistency = false; 
		domainConsistency = true;
	    }
	    else if ( ann.getAnnId().equals("defines_var") ) {  // no used in JaCoP yet
		ASTAnnExpr expr = (ASTAnnExpr)ann.jjtGetChild(0);
		Var v = getAnnVar(expr);

		definedVar = (IntVar)v;
	    }
	}
    }

    Var getAnnVar(ASTAnnExpr node) {

	ASTScalarFlatExpr e = (ASTScalarFlatExpr)node.jjtGetChild(0);
	if (e != null)
	    return dictionary.getVariable( e.getIdent());
	else{
	    System.err.println("Wrong variable identified in \"defines_var\" annotation" + node);
	    System.exit(0);
	    return new IntVar(store);
	}
    }


    boolean allConstants(IntVar[] p) {
	boolean sat = true;
	int k = 0;
	while (sat && k < p.length) {
	    sat = (p[k].min() == p[k].max());
	    k++;
	}
	return sat;
    }

    void poseDelayedConstraints() {
	for (Constraint c : delayedConstraints) {
	    store.impose(c);
  	    if (debug)
 		System.out.println(c);
	}
	poseAlldistinctConstraints();
    }

    void poseAlldistinctConstraints() {
 	for (IntVar[] v : parameterListForAlldistincts) {
      	    if (debug)
 		System.out.println("Alldistinct("+java.util.Arrays.asList(v)+")");
 	    store.impose(new Alldistinct(v));
 	}
    }

    void pose(Constraint c) throws FailException {

	store.imposeWithConsistency(c);	
	
	if (debug)
	    System.out.println(c);
    }
}
