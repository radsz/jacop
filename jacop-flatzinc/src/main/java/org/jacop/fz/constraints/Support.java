/*
 * Support.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.XeqY;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatVar;
import org.jacop.fz.ASTAnnExpr;
import org.jacop.fz.ASTAnnotation;
import org.jacop.fz.ASTIntFlatExpr;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ASTSetLiteral;
import org.jacop.fz.Options;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.fz.Tables;
import org.jacop.fz.VariablesParameters;
import org.jacop.satwrapper.SatTranslation;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;

/**
 * Basic support for generation of constraints in flatzinc.
 *
 * @author Krzysztof Kuchcinski
 */
public class Support implements ParserTreeConstants {

  // comparison operators
  static final int EQ = 0;
  static final int NE = 1;
  static final int LT = 2;
  static final int GT = 3;
  static final int LE = 4;
  static final int GE = 5;
  static final AtomicInteger n1 = new AtomicInteger(0);
  static final AtomicInteger n2 = new AtomicInteger(0);
  static final AtomicInteger n3 = new AtomicInteger(0);
  static final AtomicInteger n4 = new AtomicInteger(0);
  static final AtomicInteger n5 = new AtomicInteger(0);
  static final AtomicInteger n6 = new AtomicInteger(0);
  static final AtomicInteger n7 = new AtomicInteger(0);
  final Store store;
  final Tables dictionary;
  // ============ SAT solver interface ==============
  final SatTranslation sat;
  final ArrayList<IntVar[]> parameterListForAlldistincts = new ArrayList<>();
  final ArrayList<Constraint> delayedConstraints = new ArrayList<>();
  final ReificationConstraints reif = new ReificationConstraints(this);
  final ImplicationConstraints imply = new ImplicationConstraints(this);
  public Options options;
  // =========== Annotations ===========
  public boolean boundsConsistency = true;
  public boolean domainConsistency;
  public int constraintPriority = -1;
  // defines_var-- not used yet
  public IntVar definedVar;
  boolean intPresent = true;
  boolean floatPresent = true;

  /**
   * Constructs a support object for flatzinc constraint generation.
   *
   * @param store the constraint store
   * @param d the tables containing variable definitions
   * @param sat the SAT translation interface
   */
  public Support(Store store, Tables d, SatTranslation sat) {
    this.store = store;
    this.dictionary = d;
    this.sat = sat;
  }

  /**
   * Retrieves an integer value from a scalar flat expression node.
   *
   * @param node the scalar flat expression node
   * @return the integer value
   */
  public int getInt(ASTScalarFlatExpr node) {
    intPresent = true;

    if (node.getType() == 0) { // int
      return node.getInt();
    }
    if (node.getType() == 1) { // bool
      return node.getInt();
    } else if (node.getType() == 2) { // ident
      return dictionary.getInt(node.getIdent());
    } else if (node.getType() == 3) { // array access
      int[] intTable = dictionary.getIntArray(node.getIdent());
      if (intTable == null) {
        intPresent = false;
        return Integer.MIN_VALUE;
      } else {
        return intTable[node.getInt()];
      }
    } else {
      throw new IllegalArgumentException("getInt: Wrong parameter " + node);
    }
  }

  /**
   * Retrieves a scalar flat expression value from a child node.
   *
   * @param node the parent node
   * @param i the index of the child node
   * @return the integer value from the scalar flat expression
   */
  int getScalarFlatExpr(SimpleNode node, int i) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(i);
    if (child.getId() == JJTSCALARFLATEXPR) {
      // string & float;
      return switch (((ASTScalarFlatExpr) child).getType()) {
        case 0 -> // int
            ((ASTScalarFlatExpr) child).getInt();
        case 1 -> // bool
            ((ASTScalarFlatExpr) child).getInt();
        case 2 -> // ident
            dictionary.getInt(((ASTScalarFlatExpr) child).getIdent());
        case 3 -> // array acces
            dictionary
                .getIntArray(((ASTScalarFlatExpr) child).getIdent())[
                ((ASTScalarFlatExpr) child).getInt()];
        default ->
            throw new IllegalArgumentException(
                "Not supported scalar in parameter; compilation aborted.");
      };
    } else {
      throw new IllegalArgumentException(
          "Not supported parameter assignment; compilation aborted.");
    }
  }

  /**
   * Helper method to get array from node - either from literal or from dictionary by identifier.
   *
   * @param node the parse tree node
   * @param literalExtractor function to extract array from literal node
   * @param arrayGetter function to get array from dictionary by identifier
   * @return the array
   */
  private <T> T getArrayFromNode(
      SimpleNode node,
      java.util.function.Function<SimpleNode, T> literalExtractor,
      java.util.function.Function<String, T> arrayGetter) {
    if (node.getId() == JJTARRAYLITERAL) {
      return literalExtractor.apply(node);
    } else if (node.getId() == JJTSCALARFLATEXPR) {
      if (((ASTScalarFlatExpr) node).getType() == 2) { // ident
        return arrayGetter.apply(((ASTScalarFlatExpr) node).getIdent());
      } else {
        throw new IllegalArgumentException("Wrong type of array; compilation aborted.");
      }
    } else {
      throw new IllegalArgumentException("Wrong type of array; compilation aborted.");
    }
  }

  /**
   * Retrieves an integer array from a parse tree node.
   *
   * @param node the parse tree node
   * @return the integer array
   */
  int[] getIntArray(SimpleNode node) {
    return getArrayFromNode(node, this::getIntArrayFromLiteral, dictionary::getIntArray);
  }

  private int[] getIntArrayFromLiteral(SimpleNode node) {
    int count = node.jjtGetNumChildren();
    int[] aa = new int[count];
    for (int i = 0; i < count; i++) {
      ASTScalarFlatExpr child = (ASTScalarFlatExpr) node.jjtGetChild(i);
      int el = getInt(child);
      if (!intPresent) {
        return null;
      } else {
        aa[i] = el;
      }
    }
    return aa;
  }

  /**
   * Gets an integer variable from a scalar flat expression node.
   *
   * @param node the AST scalar flat expression node
   * @return the integer variable
   */
  public IntVar getVariable(ASTScalarFlatExpr node) {
    if (node.getType() == 0) { // int
      int val = node.getInt();
      return dictionary.getConstant(val);
    }
    if (node.getType() == 1) { // bool
      int val = node.getInt();
      return dictionary.getConstant(val);
    } else if (node.getType() == 2) { // ident
      IntVar int_boolVar = dictionary.getVariable(node.getIdent());
      if (int_boolVar == null) {
        int bInt = dictionary.getInt(node.getIdent());
        return dictionary.getConstant(bInt); // new IntVar(store, bInt, bInt);
      }
      return int_boolVar;
    } else if (node.getType() == 3) { // array access
      if (node.getInt() >= dictionary.getVariableArray(node.getIdent()).length
          || node.getInt() < 0) {
        throw new IllegalArgumentException(
            "Index out of bound for " + node.getIdent() + "[" + (node.getInt() + 1) + "]");
      } else {
        return dictionary.getVariableArray(node.getIdent())[node.getInt()];
      }
    } else {
      throw new IllegalArgumentException("Wrong parameter " + node);
    }
  }

  /**
   * Retrieves a float variable from a scalar flat expression node.
   *
   * @param node the scalar flat expression node
   * @return the float variable
   */
  FloatVar getFloatVariable(ASTScalarFlatExpr node) {

    if (node.getType() == 5) { // float
      double val = node.getFloat();
      return new FloatVar(store, val, val);
    } else if (node.getType() == 2) { // ident
      FloatVar float_Var = dictionary.getFloatVariable(node.getIdent());
      if (float_Var == null) {
        double bFloat = dictionary.getFloat(node.getIdent());
        return new FloatVar(store, bFloat, bFloat);
      }
      return float_Var;
    } else if (node.getType() == 3) { // array access
      if (node.getInt() >= dictionary.getVariableFloatArray(node.getIdent()).length
          || node.getFloat() < 0) {
        throw new IllegalArgumentException(
            "Index out of bound for " + node.getIdent() + "[" + (node.getInt() + 1) + "]");
      } else {
        return dictionary.getVariableFloatArray(node.getIdent())[node.getInt()];
      }
    } else {
      throw new IllegalArgumentException("getFloatVariable: Wrong parameter " + node);
    }
  }

  /**
   * Retrieves a set variable from a parse tree node.
   *
   * @param node the parent node
   * @param index the index of the child node
   * @return the set variable
   */
  SetVar getSetVariable(SimpleNode node, int index) {

    SimpleNode child = (SimpleNode) node.jjtGetChild(index);
    if (child.getId() == JJTSETLITERAL) {
      int count = child.jjtGetNumChildren();
      if (count == 0) {
        return new SetVar(store, new BoundSetDomain(new IntervalDomain(), new IntervalDomain()));
      } else {
        IntDomain s2 = getSetLiteral(node, index);
        return new SetVar(store, new BoundSetDomain(s2, s2));
      }
    } else if (child.getId() == JJTSCALARFLATEXPR) {
      if (((ASTScalarFlatExpr) child).getType() == 2) { // ident
        SetVar v = dictionary.getSetVariable(((ASTScalarFlatExpr) child).getIdent());
        if (v != null) {
          return v; // Variable ident
        } else { // Set ident
          IntDomain s = dictionary.getSet(((ASTScalarFlatExpr) child).getIdent());
          return new SetVar(store, new BoundSetDomain(s, s));
        }
      } else if (((ASTScalarFlatExpr) child).getType() == 3) { // array access
        return dictionary
            .getSetVariableArray(((ASTScalarFlatExpr) child).getIdent())[
            ((ASTScalarFlatExpr) child).getInt()];
      } else {
        throw new IllegalArgumentException("Wrong parameter in set " + child);
      }
    } else {
      throw new IllegalArgumentException("Wrong parameter in set " + child);
    }
  }

  /**
   * Retrieves a float value from a scalar flat expression node.
   *
   * @param node the scalar flat expression node
   * @return the float value
   */
  double getFloat(ASTScalarFlatExpr node) {
    floatPresent = true;

    if (node.getType() == 5) { // int
      return node.getFloat();
    } else if (node.getType() == 2) { // ident
      return dictionary.getFloat(node.getIdent());
    } else if (node.getType() == 3) { // array access
      double[] floatTable = dictionary.getFloatArray(node.getIdent());
      if (floatTable == null) {
        floatPresent = false;
        return VariablesParameters.MIN_FLOAT;
      } else {
        return floatTable[node.getInt()];
      }
    } else {
      throw new IllegalArgumentException("getFloat: Wrong parameter " + node);
    }
  }

  /**
   * Retrieves a float array from a parse tree node.
   *
   * @param node the parse tree node
   * @return the float array
   */
  double[] getFloatArray(SimpleNode node) {
    return getArrayFromNode(node, this::getFloatArrayFromLiteral, dictionary::getFloatArray);
  }

  private double[] getFloatArrayFromLiteral(SimpleNode node) {
    int count = node.jjtGetNumChildren();
    double[] aa = new double[count];
    for (int i = 0; i < count; i++) {
      ASTScalarFlatExpr child = (ASTScalarFlatExpr) node.jjtGetChild(i);
      double el = getFloat(child);
      if (!floatPresent) {
        return null;
      } else {
        aa[i] = el;
      }
    }
    return aa;
  }

  /**
   * Retrieves an array of integer variables from a parse tree node.
   *
   * @param node the parse tree node
   * @return the array of integer variables
   */
  IntVar[] getVarArray(SimpleNode node) {
    if (node.getId() == JJTARRAYLITERAL) {
      return getIntVarArrayFromLiteral(node);
    }
    if (node.getId() == JJTSCALARFLATEXPR) {
      return getVarArrayFromScalarFlatExpr((ASTScalarFlatExpr) node);
    }
    throw new IllegalArgumentException("Wrong type of Variable array; compilation aborted.");
  }

  private IntVar[] getVarArrayFromScalarFlatExpr(ASTScalarFlatExpr node) {
    if (node.getType() != 2) {
      throw new IllegalArgumentException("Wrong type of Variable array; compilation aborted.");
    }
    String ident = node.getIdent();
    IntVar[] v = dictionary.getVariableArray(ident);
    if (v != null) {
      return v;
    }
    int[] ia = dictionary.getIntArray(ident);
    if (ia != null) {
      IntVar[] aa = new IntVar[ia.length];
      for (int i = 0; i < ia.length; i++) {
        aa[i] = dictionary.getConstant(ia[i]);
      }
      return aa;
    }
    throw new IllegalArgumentException("Cannot find array " + ident + "; compilation aborted.");
  }

  private IntVar[] getIntVarArrayFromLiteral(SimpleNode node) {
    int count = node.jjtGetNumChildren();
    IntVar[] aa = new IntVar[count];
    for (int i = 0; i < count; i++) {
      ASTScalarFlatExpr child = (ASTScalarFlatExpr) node.jjtGetChild(i);
      aa[i] = getVariable(child);
    }
    return aa;
  }

  /**
   * Retrieves an array of float variables from a parse tree node.
   *
   * @param node the parse tree node
   * @return the array of float variables
   */
  FloatVar[] getFloatVarArray(SimpleNode node) {
    if (node.getId() == JJTARRAYLITERAL) {
      return getFloatVarArrayFromLiteral(node);
    } else if (node.getId() == JJTSCALARFLATEXPR) {
      if (((ASTScalarFlatExpr) node).getType() == 2) { // ident
        // array of var
        return dictionary.getVariableFloatArray(((ASTScalarFlatExpr) node).getIdent());
      } else {
        throw new IllegalArgumentException("Wrong type of Variable array; compilation aborted.");
      }
    } else {
      throw new IllegalArgumentException("Wrong type of Variable array; compilation aborted.");
    }
  }

  private FloatVar[] getFloatVarArrayFromLiteral(SimpleNode node) {
    int count = node.jjtGetNumChildren();
    FloatVar[] aa = new FloatVar[count];
    for (int i = 0; i < count; i++) {
      ASTScalarFlatExpr child = (ASTScalarFlatExpr) node.jjtGetChild(i);
      aa[i] = getFloatVariable(child);
    }
    return aa;
  }

  IntDomain[] getSetArray(SimpleNode node) {
    if (node.getId() == JJTARRAYLITERAL) {
      return getSetArrayFromLiteral(node);
    }
    if (node.getId() == JJTSCALARFLATEXPR) {
      return getSetArrayFromIdent((ASTScalarFlatExpr) node);
    }
    return null;
  }

  private IntDomain[] getSetArrayFromLiteral(SimpleNode node) {
    int count = node.jjtGetNumChildren();
    IntDomain[] s = new IntDomain[count];
    for (int i = 0; i < count; i++) {
      s[i] = getSetLiteral(node, i);
    }
    return s;
  }

  private IntDomain[] getSetArrayFromIdent(ASTScalarFlatExpr node) {
    if (node.getType() != 2) {
      throw new IllegalArgumentException("Wrong set array.");
    }
    IntDomain[] s = dictionary.getSetArray(node.getIdent());
    if (s != null) {
      return s;
    }
    return getSetArrayFromSingletonSetVars(node.getIdent());
  }

  private IntDomain[] getSetArrayFromSingletonSetVars(String ident) {
    SetVar[] sVar = dictionary.getSetVariableArray(ident);
    if (sVar == null) {
      return null;
    }
    int numberSingleton = 0;
    for (SetVar setVar : sVar) {
      if (setVar.singleton()) {
        numberSingleton++;
      }
    }
    if (sVar.length != numberSingleton) {
      return null;
    }
    IntDomain[] s = new IntDomain[sVar.length];
    for (int i = 0; i < sVar.length; i++) {
      s[i] = sVar[i].dom().glb();
    }
    return s;
  }

  SetVar[] getSetVarArray(SimpleNode node) {
    if (node.getId() == JJTARRAYLITERAL) {
      return getSetVarArrayFromLiteral(node);
    }
    if (node.getId() == JJTSCALARFLATEXPR) {
      return getSetVarArrayFromIdent((ASTScalarFlatExpr) node);
    }
    throw new IllegalArgumentException("Wrong set variable array; compilation aborted.");
  }

  private SetVar[] getSetVarArrayFromLiteral(SimpleNode node) {
    int count = node.jjtGetNumChildren();
    SetVar[] s = new SetVar[count];
    for (int i = 0; i < count; i++) {
      s[i] = getSetVariable(node, i);
    }
    return s;
  }

  private SetVar[] getSetVarArrayFromIdent(ASTScalarFlatExpr node) {
    if (node.getType() != 2) {
      throw new IllegalArgumentException("Wrong set variable array; compilation aborted.");
    }
    SetVar[] s = dictionary.getSetVariableArray(node.getIdent());
    if (s != null) {
      return s;
    }
    throw new IllegalArgumentException("Wrong set variable array; compilation aborted.");
  }

  IntDomain getSetLiteral(SimpleNode node, int index) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(index);
    if (child.getId() == JJTSETLITERAL) {
      IntDomain result = getSetLiteralFromSetLiteral(child);
      if (result != null) {
        return result;
      }
    } else if (child.getId() == JJTSCALARFLATEXPR) {
      return getSetLiteralFromScalarExpr((ASTScalarFlatExpr) child);
    }
    return new IntervalDomain();
  }

  private IntDomain getSetLiteralFromSetLiteral(SimpleNode child) {
    switch (((ASTSetLiteral) child).getType()) {
      case 0:
        return getSetLiteralInterval(child);
      case 1:
        return getSetLiteralList(child);
      case 2:
        return getSetLiteralRange(child);
      default:
        throw new IllegalArgumentException("Set type not supported; compilation aborted.");
    }
  }

  private IntDomain getSetLiteralInterval(SimpleNode child) {
    SimpleNode grandChild1 = (SimpleNode) child.jjtGetChild(0);
    SimpleNode grandChild2 = (SimpleNode) child.jjtGetChild(1);
    if (grandChild1.getId() != JJTINTFLATEXPR || grandChild2.getId() != JJTINTFLATEXPR) {
      return null;
    }
    int i1 = ((ASTIntFlatExpr) grandChild1).getInt();
    int i2 = ((ASTIntFlatExpr) grandChild2).getInt();
    return i1 > i2 ? new IntervalDomain() : new IntervalDomain(i1, i2);
  }

  private IntDomain getSetLiteralList(SimpleNode child) {
    IntDomain s = new IntervalDomain();
    int count = child.jjtGetNumChildren();
    for (int i = 0; i < count; i++) {
      s.unionAdapt(getScalarFlatExpr(child, i));
    }
    return s;
  }

  private IntDomain getSetLiteralRange(SimpleNode child) {
    IntDomain d = new IntervalDomain();
    int n = child.jjtGetNumChildren();
    for (int i = 0; i < n; i++) {
      SimpleNode setElement = (SimpleNode) child.jjtGetChild(i);
      if (setElement.getId() == JJTSETELEMENT) {
        SimpleNode e1 = (SimpleNode) setElement.jjtGetChild(0);
        if (e1.getId() == JJTSCALARFLATEXPR) {
          d.unionAdapt(((ASTScalarFlatExpr) e1).getInt());
        } else if (e1.getId() == JJTINTFLATEXPR) {
          SimpleNode e2 = (SimpleNode) setElement.jjtGetChild(1);
          d.unionAdapt(
              new Interval(((ASTIntFlatExpr) e1).getInt(), ((ASTIntFlatExpr) e2).getInt()));
        }
      }
    }
    return d;
  }

  private IntDomain getSetLiteralFromScalarExpr(ASTScalarFlatExpr child) {
    return switch (child.getType()) {
      case 0, 1 ->
          throw new IllegalArgumentException("Set initialization fault; compilation aborted.");
      case 2 -> dictionary.getSet(child.getIdent());
      case 3 -> dictionary.getSetArray(child.getIdent())[child.getInt()];
      case 4, 5 ->
          throw new IllegalArgumentException("Set initialization fault; compilation aborted.");
      default ->
          throw new IllegalArgumentException("Set initialization fault; compilation aborted.");
    };
  }

  IntVar[] unique(IntVar[] vs) {

    LinkedHashSet<IntVar> varSet = new LinkedHashSet<>(Arrays.asList(vs));

    int l = varSet.size();
    IntVar[] rs = new IntVar[l];

    int i = 0;
    for (IntVar v : varSet) {
      rs[i++] = v;
    }

    return rs;
  }

  /**
   * Parses annotations from a constraint node.
   *
   * @param constraintWithAnnotations the constraint node with annotations
   */
  public void parseAnnotations(SimpleNode constraintWithAnnotations) {

    for (int i = 1; i < constraintWithAnnotations.jjtGetNumChildren(); i++) {
      ASTAnnotation ann = (ASTAnnotation) constraintWithAnnotations.jjtGetChild(i);

      constraintPriority = -1;

      if ("$expr".equals(ann.getAnnId())) {
        ASTScalarFlatExpr n = (ASTScalarFlatExpr) ann.jjtGetChild(0).jjtGetChild(0);
        if ("bounds".equals(n.getIdent()) || "boundsZ".equals(n.getIdent())) {
          boundsConsistency = true;
          domainConsistency = false;
        } else if ("domain".equals(n.getIdent())) {
          boundsConsistency = false;
          domainConsistency = true;
        }
      } else if ("defines_var".equals(ann.getAnnId())) { // no used in JaCoP yet
        SimpleNode child = (SimpleNode) ann.jjtGetChild(0);
        ASTAnnExpr expr = (ASTAnnExpr) child.jjtGetChild(0);
        Var v = getAnnVar(expr);

        definedVar = (IntVar) v;
      } else if ("priority".equals(ann.getAnnId())) {
        SimpleNode child = (SimpleNode) ann.jjtGetChild(0);
        ASTAnnExpr expr = (ASTAnnExpr) child.jjtGetChild(0);

        constraintPriority = getAnnInt(expr);
      }
    }
  }

  Var getAnnVar(ASTAnnExpr node) {

    ASTScalarFlatExpr e = (ASTScalarFlatExpr) node.jjtGetChild(0);
    if (e != null) {
      return dictionary.getVariable(e.getIdent());
    } else {
      throw new IllegalArgumentException(
          "Wrong variable identified in \"defines_var\" annotation" + node);
    }
  }

  int getAnnInt(ASTAnnExpr node) {

    ASTScalarFlatExpr e = (ASTScalarFlatExpr) node.jjtGetChild(0);
    if (e != null) {
      return getInt(e);
    } else {
      throw new IllegalArgumentException("Wrong definition od \"priority\" annotation" + node);
    }
  }

  /** Imposes all delayed constraints. */
  public void poseDelayedConstraints() {
    // generate channeling constraints for aliases
    // variables that are output variables
    aliasConstraints();

    for (Constraint c : delayedConstraints) {
      store.impose(c);
      if (options.debug()) {
        String s = "% " + c;
        IO.println(s.replace("\n", "\n% "));
      }
    }
    poseAlldistinctConstraints();

    // generate channeling constraints instead of reified constraints
    reif.pose();
    // generate channeling constraints instead of implied constraints
    imply.pose();
  }

  void poseAlldistinctConstraints() {
    for (IntVar[] v : parameterListForAlldistincts) {
      Alldistinct ad = new Alldistinct(v);
      store.impose(ad);
      if (options.debug()) {
        String s = "% " + ad;
        IO.println(s.replace("\n", "\n% "));
      }
    }
  }

  // =========== Specialized constraints ===================

  void aliasConstraints() {

    Set<Map.Entry<IntVar, IntVar>> entries = dictionary.aliasTable.entrySet();

    for (Map.Entry<IntVar, IntVar> e : entries) {
      IntVar v = e.getKey();
      IntVar b = e.getValue();

      // give values to output vars
      if (dictionary.isOutput(v)) {
        pose(new XeqY(v, b));
      }
    }
  }

  <T extends Constraint> void poseDc(DecomposedConstraint<T> c) throws FailException {

    store.imposeDecompositionWithConsistency(c);
    if (options.debug()) {
      String s = "% " + c;
      IO.println(s.replace("\n", "\n% "));
    }
  }

  void pose(Constraint c) throws FailException {

    if (constraintPriority >= 0 && constraintPriority <= 4) {
      store.imposeWithConsistency(c, constraintPriority);
    } else {
      store.imposeWithConsistency(c);
    }

    if (options.debug()) {
      String s = "% " + c;
      IO.println(s.replace("\n", "\n% "));
    }
  }

  /**
   * Adds a reified constraint.
   *
   * @param x the integer variable
   * @param v the value
   * @param b the boolean variable
   */
  public void addReified(IntVar x, int v, IntVar b) {
    reif.add(x, v, b);
  }

  /**
   * Imposes all reified constraints.
   *
   * @param s the support object
   */
  public void poseReified(Support s) {
    reif.pose();
  }

  /**
   * Adds an implied constraint.
   *
   * @param x the integer variable
   * @param v the value
   * @param b the boolean variable
   */
  public void addImplied(IntVar x, int v, IntVar b) {
    imply.add(x, v, b);
  }

  /**
   * Imposes all implied constraints.
   *
   * @param s the support object
   */
  public void poseImplied(Support s) {
    imply.pose();
  }

  void propagateFzXeqC(
      Store store, IntVar x, int c, IntVar b, boolean isReified, Runnable removeConstraint) {
    if (x.singleton(c)) {
      if (isReified) {
        b.domain.inValue(store.level, b, 1);
      } else {
        removeConstraint.run();
      }
      return;
    }
    if (!x.domain.contains(c)) {
      b.domain.inValue(store.level, b, 0);
      removeConstraint.run();
      return;
    }
    if (b.max() == 0) {
      if (isReified) {
        x.domain.inComplement(store.level, x, c);
      }
      removeConstraint.run();
      return;
    }
    if (b.min() == 1) {
      x.domain.inValue(store.level, x, c);
    }
  }

  void propagateFzXneqC(
      Store store, IntVar x, int c, IntVar b, boolean isReified, Runnable removeConstraint) {
    if (x.singleton(c)) {
      b.domain.inValue(store.level, b, 0);
      return;
    }
    if (!x.domain.contains(c)) {
      if (isReified) {
        b.domain.inValue(store.level, b, 1);
      }
      removeConstraint.run();
      return;
    }
    if (b.max() == 0) {
      if (isReified) {
        x.domain.inValue(store.level, x, c);
      }
      removeConstraint.run();
      return;
    }
    if (b.min() == 1) {
      x.domain.inComplement(store.level, x, c);
      if (isReified) {
        removeConstraint.run();
      }
    }
  }

  void propagateFzXeqY(
      Store store, IntVar x, IntVar y, IntVar b, boolean isReified, Runnable removeConstraint) {
    if (x == y || (x.singleton(y.min()) && y.singleton(x.min()))) {
      if (isReified) {
        b.domain.inValue(store.level, b, 1);
      } else {
        removeConstraint.run();
      }
      return;
    }
    if (!x.domain.isIntersecting(y.domain)) {
      b.domain.inValue(store.level, b, 0);
      removeConstraint.run();
      return;
    }
    if (b.max() == 0) {
      if (isReified) {
        if (y.singleton()) {
          x.domain.inComplement(store.level, x, y.value());
          removeConstraint.run();
        }
        if (x.singleton()) {
          y.domain.inComplement(store.level, y, x.value());
          removeConstraint.run();
        }
      } else {
        removeConstraint.run();
      }
      return;
    }
    if (b.min() == 1) {
      do {
        x.domain.in(store.level, x, y.domain);
        store.propagationHasOccurred = false;
        y.domain.in(store.level, y, x.domain);
      } while (store.propagationHasOccurred);
    }
  }

  Constraint fzXeqC(IntVar x, int c, IntVar b, boolean isReified) {

    return new Constraint(new IntVar[] {x, b}) {

      final int numberId = isReified ? n1.incrementAndGet() : n2.incrementAndGet();

      @Override
      public void consistency(final Store store) {
        propagateFzXeqC(store, x, c, b, isReified, this::removeConstraint);
      }

      @Override
      public String toString() {
        if (isReified) {
          return "fzXeqCreified" + numberId + ": XeqC_Reified(" + x + ", " + c + ", " + b + " )";
        } else {
          return "fzXeqCimplied" + numberId + ": XeqC_Implied(" + b + ", " + x + ", " + c + " )";
        }
      }

      public String id() {
        return isReified ? "fzXeqCreified" + numberId : "fzXeqCimplied" + numberId;
      }
    };
  }

  Constraint fzXeqCreified(IntVar x, int c, IntVar b) {
    return fzXeqC(x, c, b, true);
  }

  Constraint fzXeqCimplied(IntVar x, int c, IntVar b) {
    return fzXeqC(x, c, b, false);
  }

  Constraint fzXneqC(IntVar x, int c, IntVar b, boolean isReified) {

    return new Constraint(new IntVar[] {x, b}) {

      final int numberId = isReified ? n3.incrementAndGet() : n4.incrementAndGet();

      @Override
      public void consistency(final Store store) {
        propagateFzXneqC(store, x, c, b, isReified, this::removeConstraint);
      }

      @Override
      public String toString() {
        if (isReified) {
          return "fzXneqCreified" + numberId + ": XneqC_Reified(" + x + ", " + c + ", " + b + " )";
        } else {
          return "fzXneqCImpled" + numberId + ": XneqC_Implied(" + b + ", " + x + ", " + c + " )";
        }
      }

      public String id() {
        return isReified ? "fzXneqCreified" + numberId : "fzXneqCimplied" + numberId;
      }
    };
  }

  Constraint fzXneqCreified(IntVar x, int c, IntVar b) {
    return fzXneqC(x, c, b, true);
  }

  Constraint fzXneqCimplied(IntVar x, int c, IntVar b) {
    return fzXneqC(x, c, b, false);
  }

  Constraint fzXeqY(IntVar x, IntVar y, IntVar b, boolean isReified) {

    return new Constraint(new IntVar[] {x, y, b}) {

      final int numberId = isReified ? n5.incrementAndGet() : n6.incrementAndGet();

      @Override
      public void consistency(final Store store) {
        propagateFzXeqY(store, x, y, b, isReified, this::removeConstraint);
      }

      @Override
      public String toString() {
        if (isReified) {
          return "fzXeYCReified" + numberId + ": XeqY_Reified(" + x + ", " + y + ", " + b + " )";
        } else {
          return "fzXeqYimplied" + numberId + ": XeqY_Implied(" + x + ", " + y + ", " + b + " )";
        }
      }

      public String id() {
        return isReified ? "fzXeqYreified" + numberId : "fzXeqYimplied" + numberId;
      }
    };
  }

  Constraint fzXeqYreified(IntVar x, IntVar y, IntVar b) {
    return fzXeqY(x, y, b, true);
  }

  Constraint fzXeqYimplied(IntVar x, IntVar y, IntVar b) {
    return fzXeqY(x, y, b, false);
  }

  Constraint fzIfThenBool(IntVar b, IntVar x) {

    return new Constraint(new IntVar[] {b, x}) {

      final int numberId = n7.incrementAndGet();

      @Override
      public void consistency(final Store store) {

        if (b.min() == 1) {
          x.domain.inValue(store.level, x, 1);
        }

        if (x.max() == 0) {
          b.domain.inValue(store.level, b, 0);
        }
      }

      @Override
      public int getDefaultConsistencyPruningEvent() {
        return IntDomain.GROUND;
      }

      @Override
      public String toString() {
        return "fzIfThenBool" + numberId + ": IfThenBool(" + b + ", " + x + " )";
      }

      public String id() {
        return "fzIfThenBool" + numberId;
      }
    };
  }
}
