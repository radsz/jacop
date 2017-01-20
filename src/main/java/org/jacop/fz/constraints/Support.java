/**
 *  Support.java 
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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.FailException;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntDomain;
import org.jacop.core.Var;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.XeqY;

import org.jacop.satwrapper.SatTranslation;

import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;

import org.jacop.floats.core.FloatVar;

import org.jacop.fz.*;

/**
 * 
 * Basic support for generation of constraints in flatzinc
 * 
 * @author Krzysztof Kuchcinski 
 *
 */
public class Support implements ParserTreeConstants {

  static Store store;
  static Tables dictionary;

  // ============ SAT solver interface ==============
  static SatTranslation sat;

  // boolean storeLevelIncreased=false;
  static boolean debug = false;

  // =========== Annotations ===========
  public static boolean boundsConsistency = true, domainConsistency = false;
  // defines_var-- not used yet
  public static IntVar definedVar = null;

  // comparison operators
  final static int eq=0, ne=1, lt=2, gt=3, le=4, ge=5;
  
  static boolean intPresent = true;
  static boolean floatPresent = true;
  
  static ArrayList<IntVar[]> parameterListForAlldistincts = new ArrayList<IntVar[]>();
  static ArrayList<Constraint> delayedConstraints = new ArrayList<Constraint>();

  public Support(Store store, Tables d, SatTranslation sat) {
    this.store = store;
    this.dictionary = d;
    this.debug = Options.debug();
    this.sat = sat;

    parameterListForAlldistincts.clear();
    delayedConstraints.clear();
  }

  static int getInt(ASTScalarFlatExpr node) {
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

  static int getScalarFlatExpr(SimpleNode node, int i) {
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
  
  static int[] getIntArray(SimpleNode node) {
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
  
  public static IntVar getVariable(ASTScalarFlatExpr node) {
    if (node.getType() == 0) {// int
      int val = node.getInt();
      return dictionary.getConstant(val);
    }
    if (node.getType() == 1) {// bool
      int val = node.getInt();
      return dictionary.getConstant(val);
    }
    else if (node.getType() == 2) { // ident
      IntVar int_boolVar = dictionary.getVariable(node.getIdent());
      if (int_boolVar == null) {
	int bInt = dictionary.getInt(node.getIdent());
	return dictionary.getConstant(bInt); // new IntVar(store, bInt, bInt);
      }
      return int_boolVar;
    }
    else if (node.getType() == 3) {// array access
      if (node.getInt() >= dictionary.getVariableArray(node.getIdent()).length ||
	  node.getInt() < 0) {
	System.out.println("Index out of bound for " + node.getIdent() + "["+node.getInt()+"]");
	System.exit(0);
	return new IntVar(store);
      }
      else {
	return dictionary.getVariableArray(node.getIdent())[node.getInt()];
      }
    }
    else {
      System.err.println("Wrong parameter " + node);
      System.exit(0);
      return new IntVar(store);
    }
  }
  
  static FloatVar getFloatVariable(ASTScalarFlatExpr node) {

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

  static SetVar getSetVariable(SimpleNode node, int index) {

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

  static double getFloat(ASTScalarFlatExpr node) {
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

  static double[] getFloatArray(SimpleNode node) {
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

  
  static IntVar[] getVarArray(SimpleNode node) {
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
	      aa[i] = dictionary.getConstant(ia[i]); // new IntVar(store, ia[i], ia[i]);
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

  static FloatVar[] getFloatVarArray(SimpleNode node) {
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

  static IntDomain[] getSetArray(SimpleNode node) {
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

  static IntDomain getSetLiteral(SimpleNode node, int index) {
    SimpleNode child = (SimpleNode)node.jjtGetChild(index);
    if (child.getId() == JJTSETLITERAL) {
      switch ( ((ASTSetLiteral)child).getType() ) {
      case 0: // interval
	SimpleNode grand_child_1 = (SimpleNode)child.jjtGetChild(0);
	SimpleNode grand_child_2 = (SimpleNode)child.jjtGetChild(1);
	if (grand_child_1.getId() == JJTINTFLATEXPR && grand_child_2.getId() == JJTINTFLATEXPR) {
	  int i1 = ((ASTIntFlatExpr)grand_child_1).getInt();
	  int i2 = ((ASTIntFlatExpr)grand_child_2).getInt();
	  if (i1 > i2)
	    return new IntervalDomain();
	  else
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

  static IntVar[] unique(IntVar[] vs) {

    HashSet<IntVar> varSet = new HashSet<IntVar>();
    for (IntVar v : vs) 
      varSet.add(v);

    int l = varSet.size();
    IntVar[] rs = new IntVar[l];

    int i = 0;
    for (IntVar v : varSet) {
      rs[i++] = v;
    }

    return rs;
  }

  public static void parseAnnotations(SimpleNode constraintWithAnnotations) {

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

  static Var getAnnVar(ASTAnnExpr node) {

    ASTScalarFlatExpr e = (ASTScalarFlatExpr)node.jjtGetChild(0);
    if (e != null)
      return dictionary.getVariable( e.getIdent());
    else{
      System.err.println("Wrong variable identified in \"defines_var\" annotation" + node);
      System.exit(0);
      return new IntVar(store);
    }
  }
  
  public static void poseDelayedConstraints() {
    // generate channeling constraints for aliases
    // variables that are output variables
    aliasConstraints();
	
    for (Constraint c : delayedConstraints) {
      store.impose(c);
      if (debug)
	System.out.println(c);
    }
    poseAlldistinctConstraints();

  }

  static void poseAlldistinctConstraints() {
    for (IntVar[] v : parameterListForAlldistincts) {
      if (debug)
	System.out.println("Alldistinct("+java.util.Arrays.asList(v)+")");
      store.impose(new Alldistinct(v));
    }
  }

  static void aliasConstraints() {

    Set<IntVar> vs = dictionary.aliasTable.keySet();

    for (IntVar v : vs) {
      IntVar b = dictionary.aliasTable.get(v);

      // give values to output vars
      if (dictionary.isOutput(v))
	pose(new XeqY(v, b));
    }
  }

  static void poseDC(DecomposedConstraint c) throws FailException {

    store.imposeDecompositionWithConsistency(c);
    if (debug)
      System.out.println(c);
  }
    
  static void pose(Constraint c) throws FailException {

    store.imposeWithConsistency(c);	
	
    if (debug)
      System.out.println(c);
  }
}
