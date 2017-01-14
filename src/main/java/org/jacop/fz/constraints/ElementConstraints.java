/**
 *  ElementConstraints.java 
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
package org.jacop.fz.constraints;

import org.jacop.core.Store;
import org.jacop.core.IntVar;

import org.jacop.constraints.AndBool;

import org.jacop.satwrapper.SatTranslation;

import org.jacop.fz.*;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.Element;
import org.jacop.constraints.ElementVariableFast;
import org.jacop.set.constraints.ElementSet;
import org.jacop.floats.constraints.ElementFloat;
import org.jacop.set.core.SetVar;
import org.jacop.floats.core.FloatVar;

/**
 * 
 * Generation of boolean constraints in flatzinc
 * 
 * @author Krzysztof Kuchcinski 
 *
 */
class ElementConstraints extends Support implements ParserTreeConstants {

  public ElementConstraints(Store store, Tables d, SatTranslation sat) {
    super(store, d, sat);
  }

  static void gen_array_int_element(SimpleNode node) {
    generateIntElementConstraint(node);
  }

  static void gen_array_var_int_element(SimpleNode node) {
    generateVarElementConstraint(node);
  }

  static void gen_array_var_set_element(SimpleNode node) {
    generateVarSetElementConstraint(node);
  }

  static void gen_array_set_element(SimpleNode node) {
    generateSetElementConstraint(node);
  }

  static void gen_array_float_element(SimpleNode node) {
    generateFloatElementConstraint(node);
  }

  static void gen_array_var_float_element(SimpleNode node) {
    generateVarFloatElementConstraint(node);
  }

  static void generateIntElementConstraint(SimpleNode node) throws FailException {

	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
	int[] p2 = getIntArray((SimpleNode)node.jjtGetChild(1));
	IntVar p3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

	poseElementInteger(p1, p2, p3);
    }
  
  static void poseElementInteger(IntVar p1, int[] p2, IntVar p3) {
    
	p1.domain.in(store.level, p1, 1, IntDomain.MaxInt);

	int newP2Length = p1.max() - p1.min() + 1;
	int listLength = (p2.length < newP2Length) ? p2.length : newP2Length;
	int[] newP2 = new int[listLength];
	for (int i=0; i < listLength; i++) 
	    newP2[i] = p2[p1.min() - 1 + i];

	if (Options.getBoundConsistency())
	    pose(new ElementIntegerFast(p1, newP2, p3, p1.min() - 1));
	else
	    pose(new Element(p1, newP2, p3, p1.min() - 1));

    }

    static void generateVarElementConstraint(SimpleNode node) throws FailException {
	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));	    
	IntVar p3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

	IntVar[] p2var = getVarArray((SimpleNode)node.jjtGetChild(1));
	if (allSingleton(p2var)) {
	    int[] p2int = new int[p2var.length];
	    for (int i = 0; i < p2int.length; i++) 
		p2int[i] = p2var[i].value();

	    poseElementInteger(p1, p2int, p3);
	}
	else {
	  p1.domain.in(store.level, p1, 1, IntDomain.MaxInt);

	  int newP2Length = p1.max() - p1.min() + 1;
	  int listLength = (p2var.length < newP2Length) ? p2var.length : newP2Length;
	  IntVar[] newP2 = new IntVar[listLength];
	  for (int i=0; i < listLength; i++) 
	    newP2[i] = p2var[p1.min() - 1 + i];
	  pose(new ElementVariableFast(p1, newP2, p3, p1.min() - 1));
	}
    }

    static void generateSetElementConstraint(SimpleNode node) throws FailException {
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

    static void generateVarSetElementConstraint(SimpleNode node) throws FailException {

	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
	SetVar p3 = getSetVariable(node, 2);

	IntDomain[] p2 = getSetArray((SimpleNode)node.jjtGetChild(1));
	if (p2 != null) {

	    for (int i=0; i < p2.length; i++)
		if (p2[i] == null) {
		    System.err.println("%% var_set_element with list of set variables is not available in org.jacop.set");
		    System.exit(0);
		}
	    
	    pose(new ElementSet(p1, p2, p3));

	}
	else {
	    System.err.println("%% var_set_element with list of set variables is not available in org.jacop.set");
	    System.exit(0);
	}
    }


    static void generateFloatElementConstraint(SimpleNode node) throws FailException {

	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
	double[] p2 = getFloatArray((SimpleNode)node.jjtGetChild(1));
	FloatVar p3 = getFloatVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

	poseElementFloat(p1, p2, p3);

    }
  
    static void generateVarFloatElementConstraint(SimpleNode node) throws FailException {

	IntVar p1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
	FloatVar[] p2 = getFloatVarArray((SimpleNode)node.jjtGetChild(1));
	FloatVar p3 = getFloatVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

	if (allFloatSingleton(p2)) {
	    double[] p2double = new double[p2.length];
	    for (int i = 0; i < p2.length; i++) 
		p2double[i] = p2[i].value();

	    poseElementFloat(p1, p2double, p3);
	}
	else {
	    System.err.println("%% array_var_float_element with list of variables is not available in org.jacop.floats");
	    System.exit(0);	  
	}	
    }
  
  static void poseElementFloat(IntVar p1, double[] p2, FloatVar p3) {
    
	p1.domain.in(store.level, p1, 1, IntDomain.MaxInt);

	int newP2Length = p1.max() - p1.min() + 1;
	int listLength = (p2.length < newP2Length) ? p2.length : newP2Length;
	double[] newP2 = new double[listLength];
	for (int i=0; i < listLength; i++) 
	    newP2[i] = p2[p1.min() - 1 + i];

	pose(new ElementFloat(p1, newP2, p3, p1.min() - 1));

    }
  
    static boolean allSingleton(IntVar[] vs) {
	for (IntVar v : vs) 
	    if (!v.singleton())
		return false;
	return true;
    }

  static boolean allFloatSingleton(FloatVar[] vs) {
	for (FloatVar v : vs) 
	  if (v.min() != v.max())
		return false;
	return true;
    }

}
