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
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.ToIntFunction;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.constraints.AlldiffSum;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.ImpliesNot;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Linearizations;
import org.jacop.constraints.OverlappingAlldiff;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusClteqZImplied;
import org.jacop.constraints.XplusClteqZImpliedNot;
import org.jacop.constraints.cumulative.MultiCumulative;
import org.jacop.constraints.diffn.DiffnK;
import org.jacop.constraints.lp.PartitionCuts;
import org.jacop.constraints.regular.MultiCostRegular;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatVar;
import org.jacop.fz.ASTAnnExpr;
import org.jacop.fz.ASTAnnotation;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTIntFlatExpr;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ASTSetLiteral;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ModelTimeOut;
import org.jacop.fz.Options;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.fz.Tables;
import org.jacop.fz.VariablesParameters;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.ConflictRows;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;
import org.jacop.lcg.ReifiedExplanation;
import org.jacop.lcg.ValueExclusion;
import org.jacop.lcg.ValueIndicator;
import org.jacop.presolve.OrderLiterals;
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
  // pairs of all_different that get an OverlappingAlldiff
  static final int OVERLAP_MIN_SHARED = 2;
  static final int OVERLAP_MAX_VARIABLES = 64;
  static final int OVERLAP_MAX_PAIRS = 10_000;

  final Store store;
  final Tables dictionary;
  // ============ SAT solver interface ==============
  final SatTranslation sat;
  final ArrayList<IntVar[]> parameterListForAlldistincts = new ArrayList<>();
  // how many of the lists above are implied by other constraints, by list
  private final Map<List<IntVar>, Integer> impliedAlldistincts = new HashMap<>();
  // the variables of every all_different of the model, for OverlappingAlldiff
  final ArrayList<IntVar[]> alldifferentLists = new ArrayList<>();
  // the variables channelled by elements and tables (AlldiffChannels), null when the rule is off
  public Set<IntVar> alldiffChannels;
  // all_different constraints over the size limits, and those of them given Alldistinct
  int alldiffsChecked;
  int alldiffsChannelled;
  // all different variables found by AlldifferentDetector, for AlldiffSum only
  final ArrayList<IntVar[]> detectedAlldifferentLists = new ArrayList<>();

  /**
   * Variables shifted by constants, {@code x[k] + o[k]}.
   *
   * @param x the variables.
   * @param o the offsets.
   */
  record Shifted(List<IntVar> x, List<Integer> o) {
    Shifted {
      x = List.copyOf(x);
      o = List.copyOf(o);
    }
  }

  // the cliques of AlldifferentDetector with their offsets, for the permutation sums of
  // LinearSystemDetector
  final ArrayList<Shifted> allDifferentOffsets = new ArrayList<>();
  // sums with unit coefficients that get an AlldiffSum when their variables are all different
  final ArrayList<UnitSum> unitSums = new ArrayList<>();
  static final int ALLDIFF_SUM_MIN_VARIABLES = 3;
  static final int ALLDIFF_SUM_MAX_VARIABLES = 64;
  final ArrayList<Constraint> delayedConstraints = new ArrayList<>();

  /** The tables that {@link TableScopeMerger} intersected, by their constraint node. */
  final Map<SimpleNode, int[]> mergedTables = new IdentityHashMap<>();

  /**
   * The linear constraints that {@link LinearOverlapDetector} rewrote, by their constraint node.
   */
  final Map<SimpleNode, LinearOverlapDetector.Rewrite> linearRewrites = new IdentityHashMap<>();

  /**
   * Drops the rewrites of the linear constraints once the constraints are generated. Their keys are
   * nodes of the parse tree, which reach the whole tree through their parents.
   */
  public void releaseLinearRewrites() {
    linearRewrites.clear();
  }

  final BinPackingCardinality binPackingCardinality = new BinPackingCardinality(this);
  final ArrayList<DiffnK> nonStrictDiffnK = new ArrayList<>();
  final BinPackingCliqueDetector binPackingCliques = new BinPackingCliqueDetector(this);
  final BinPackingPermutations binPackingPermutations = new BinPackingPermutations(this);
  final PermutationElementSums permutationElementSums = new PermutationElementSums(this);
  // unary resources found by the disjunctive clique detection: starts and durations
  final ArrayList<IntVar[][]> unaryResources = new ArrayList<>();
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
    int[] packed = node.packedInts();
    if (packed != null) {
      intPresent = true;
      return packed.clone();
    }
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
    IntVar v = getVariableUnsubstituted(node);
    ControlSubstitution s = activeControl;
    return s != null && v == s.from() && !s.negated() ? s.to() : v;
  }

  private IntVar getVariableUnsubstituted(ASTScalarFlatExpr node) {
    if (node.getType() == 0) { // int
      int val = node.getInt();
      return dictionary.getModelConstant(val);
    }
    if (node.getType() == 1) { // bool
      int val = node.getInt();
      return dictionary.getConstant(val);
    } else if (node.getType() == 2) { // ident
      IntVar int_boolVar = dictionary.getVariable(node);
      if (int_boolVar == null) {
        int bInt = dictionary.getInt(node.getIdent());
        return dictionary.getModelConstant(bInt);
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
        aa[i] = dictionary.getModelConstant(ia[i]);
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
        ASTScalarFlatExpr name = (ASTScalarFlatExpr) expr.jjtGetChild(0);
        if (name == null || !dictionary.isAlias(name.getIdent())) {
          // the integer of bool2int names its Boolean once merged into it, and the Boolean is not
          // defined by the constraint that defines the integer: speck-optimisation defines the
          // integer copy of every bit of the state, which left one variable of 12,213 to the
          // neighbourhoods of LNS
          if (halfReified(constraintWithAnnotations)) {
            // MiniZinc annotates b of int_lin_ne_imp(a, x, c, b) as defined, but b -> c leaves b
            // free when c holds
            dictionary.addHalfDefinedVar(v);
          } else {
            dictionary.addDefinedVar(v);
          }
        }
      } else if ("priority".equals(ann.getAnnId())) {
        SimpleNode child = (SimpleNode) ann.jjtGetChild(0);
        ASTAnnExpr expr = (ASTAnnExpr) child.jjtGetChild(0);

        constraintPriority = getAnnInt(expr);
      }
    }
  }

  private static boolean halfReified(SimpleNode constraintWithAnnotations) {
    return constraintWithAnnotations.jjtGetChild(0) instanceof ASTConstElem c
        && c.getName() != null
        && c.getName().endsWith("_imp");
  }

  Var getAnnVar(ASTAnnExpr node) {

    ASTScalarFlatExpr e = (ASTScalarFlatExpr) node.jjtGetChild(0);
    if (e != null) {
      return dictionary.getVariable(e);
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

  /**
   * Tells whether a detector that rewrites only constraints of the given kinds has to read the
   * model: whether the model has a constraint of one of the kinds. The scan reads only the names of
   * the constraints, while each pass of a detector over the model looks up the variables of every
   * constraint: on the 2.3 million clauses of MaxSAT 2021 relational-inference ar-2 each such pass
   * costs 3-4 s and finds nothing. Like the passes it replaces, it stops with {@link ModelTimeOut}
   * once the time-out has passed. Property {@code org.jacop.fz.detectorGates=false} reads the model
   * always.
   *
   * @param astTree the root of the parsed model.
   * @param kinds the names of the constraints the detector can rewrite.
   * @return true when the model has a constraint of one of the kinds, or the gates are off.
   * @throws ModelTimeOut when the time-out has passed.
   */
  public boolean hasConstraint(SimpleNode astTree, Set<String> kinds) {
    if (DISABLED.equals(System.getProperty("org.jacop.fz.detectorGates"))) {
      return true;
    }
    checkTimeOut();
    Set<String> present = constraintKinds(astTree);
    for (String kind : kinds) {
      if (present.contains(kind)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Tells whether the model has a constraint whose name passes a test, as {@link
   * #hasConstraint(SimpleNode, Set)} does for a set of names.
   *
   * @param astTree the root of the parsed model.
   * @param kind the test of a constraint name.
   * @return true when a constraint name passes the test, or the gates are off.
   * @throws ModelTimeOut when the time-out has passed.
   */
  public boolean hasConstraint(SimpleNode astTree, Predicate<String> kind) {
    if (DISABLED.equals(System.getProperty("org.jacop.fz.detectorGates"))) {
      return true;
    }
    checkTimeOut();
    for (String name : constraintKinds(astTree)) {
      if (kind.test(name)) {
        return true;
      }
    }
    return false;
  }

  // the names of the constraints of the model whose root is kindsOf, read once: the constraint
  // items and their names do not change while the detectors read the model, and a scan per gate
  // of the 1.9 million rows of PB 2006 haplotype simp-nonunif cost 0.1 s each
  private SimpleNode kindsOf;

  private Set<String> kinds;

  private Set<String> constraintKinds(SimpleNode astTree) {
    if (kindsOf != astTree) {
      Set<String> present = new HashSet<>();
      for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
        SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
        if (node.getId() == JJTCONSTRAINTITEMS) {
          for (int j = 0; j < node.jjtGetNumChildren(); j++) {
            checkTimeOut();
            SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
            if (item instanceof ASTConstElem c) {
              present.add(c.getName());
            }
          }
        }
      }
      kinds = present;
      kindsOf = astTree;
    }
    return kinds;
  }

  /**
   * Calls the action on every constraint of a parsed model, in the order of the model. It stops
   * with {@link ModelTimeOut} once the time-out has passed: a scan of a model with millions of
   * constraints takes seconds (rcpsp-wet-diverse j90_48_4, 470 MB).
   *
   * @param astTree the root of the parsed model.
   * @param action what is done with each constraint.
   */
  void forEachConstraint(SimpleNode astTree, Consumer<ASTConstElem> action) {
    forEachConstraintItem(astTree, (item, element) -> action.accept(element));
  }

  /**
   * Calls an action on each constraint element of the model with its constraint item, whose other
   * children are the annotations of the constraint (a node does not keep its parent).
   *
   * @param astTree the root of the parsed model
   * @param action the action, on the constraint item and its element
   */
  void forEachConstraintItem(SimpleNode astTree, BiConsumer<SimpleNode, ASTConstElem> action) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          checkTimeOut();
          SimpleNode constraint = (SimpleNode) node.jjtGetChild(j);
          SimpleNode item = (SimpleNode) constraint.jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            action.accept(constraint, (ASTConstElem) item);
          }
        }
      }
    }
  }

  /**
   * Records the domains of the variables of the inverse channels ({@code jacop_assignment}) before
   * any constraint prunes them; symmetry breaking compares them as the model declares them.
   *
   * @param astTree the root of the parsed model.
   */
  public void recordChannelDomains(SimpleNode astTree) {
    forEachConstraint(
        astTree,
        node -> {
          if ("jacop_assignment".equals(node.getName())) {
            for (int i = 0; i < 2; i++) {
              for (IntVar v : getVarArray((SimpleNode) node.jjtGetChild(i))) {
                dictionary.recordChannelDomain(v);
              }
            }
          }
        });
  }

  /**
   * Stops building the model once the time-out has passed.
   *
   * @throws ModelTimeOut when it has passed
   */
  void checkTimeOut() {
    // the clock is read at the first and every 64th call after it (Options.timeOutCheckStride), and
    // stays passed once it is: the
    // detectors call this for each constraint they read, 160 million times (2 s) on the 3.9
    // million clauses of MaxSAT 2021 haplotyping-pedigrees
    if (options == null) {
      return;
    }
    if (timedOut != options
        && (timeOutChecks++ & (options.timeOutCheckStride() - 1)) == 0
        && options.timeOutPassed()) {
      timedOut = options;
    }
    if (timedOut == options) {
      throw new ModelTimeOut();
    }
  }

  // the calls of checkTimeOut, and the options whose time-out one found passed
  private int timeOutChecks;

  private Options timedOut;

  /** Posts the conflict cliques of the bin packing constraints over the same bins. */
  public void detectBinPackingCliques() {
    implied(binPackingCliques::detect);
    implied(binPackingPermutations::detect);
    implied(permutationElementSums::detect);
  }

  /**
   * Runs a step that adds only redundant constraints, every solution of the model satisfying them,
   * and marks them implied in the store ({@link Store#markImplied(Constraint)}), the delayed ones
   * among them too. Local search does not evaluate them.
   *
   * @param step the step that poses the redundant constraints.
   */
  public void implied(Runnable step) {
    boolean was = store.isImposingImplied();
    int delayed = delayedConstraints.size();
    store.imposingImplied(true);
    try {
      step.run();
    } finally {
      store.imposingImplied(was);
    }
    for (int i = delayed; i < delayedConstraints.size(); i++) {
      store.markImplied(delayedConstraints.get(i));
    }
  }

  /**
   * Collects an all different that is implied by the other constraints of the model, such as the
   * one of a circuit, to be posted with the others and marked implied.
   *
   * @param v the variables.
   */
  void addImpliedAlldistinct(IntVar[] v) {
    parameterListForAlldistincts.add(v);
    impliedAlldistincts.merge(List.of(v), 1, Integer::sum);
  }

  /** Prints, under debug, how many all_different constraints the channel rule changed. */
  public void reportAlldiffChannels() {
    if (options.debug() && alldiffsChecked > 0) {
      FzConsole.println(
          "% alldiff channels: "
              + alldiffsChannelled
              + " of "
              + alldiffsChecked
              + " all_different over the size limits get Alldistinct");
    }
  }

  // the bin packings whose loads are also posted as sums of their items, see addLoadSums
  private final List<Object[]> loadSums = new ArrayList<>();

  /**
   * Collects a bin packing whose loads are also posted, with the delayed constraints, as the sums
   * of the items in each bin: a 0/1 variable per item and bin that says the item is in it, the one
   * the model reifies when it has one. Binpacking explains a load bound or a removed bin by the
   * bins of many items at once (97 atoms per reason on MZNC 2017 steelmillslab bench_19_5); the
   * sums give the learnt clauses those 0/1 variables and lifted linear reasons.
   *
   * @param bin the bin of each item
   * @param load the load of each bin
   * @param w the weight of each item
   * @param minBin the number of the first bin
   */
  void addLoadSums(IntVar[] bin, IntVar[] load, int[] w, int minBin) {
    loadSums.add(new Object[] {bin, load, w, minBin});
  }

  /** The most item-bin pairs whose load sums are posted beside a bin packing. */
  private static final int LOAD_SUM_PAIRS = 1 << 16;

  // load[i] = sum of w[k] * [bin[k] = i + minBin] over the items k, with the 0/1 variables
  // channelled to the bins
  private void poseLoadSums(IntVar[] bin, IntVar[] load, int[] w, int minBin) {
    int n = bin.length;
    int m = load.length;
    if ((long) n * m > LOAD_SUM_PAIRS) {
      return;
    }
    List<List<IntVar>> terms = new ArrayList<>();
    List<List<Integer>> weights = new ArrayList<>();
    for (int i = 0; i < m; i++) {
      terms.add(new ArrayList<>());
      weights.add(new ArrayList<>());
    }
    long[] fixed = new long[m];
    for (int k = 0; k < n; k++) {
      if (w[k] == 0) {
        continue;
      }
      IntDomain d = bin[k].dom();
      if (bin[k].singleton()) {
        int i = bin[k].value() - minBin;
        if (i >= 0 && i < m) {
          fixed[i] += w[k];
        }
        continue;
      }
      Map<Integer, IntVar> reified = reif.cs.get(bin[k]);
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        int i = v - minBin;
        if (i < 0 || i >= m) {
          continue;
        }
        IntVar b = reified == null ? null : reified.get(v);
        if (b == null) {
          b = new BooleanVar(store);
          addReified(bin[k], v, b);
        }
        terms.get(i).add(b);
        weights.get(i).add(w[k]);
      }
    }
    for (int i = 0; i < m; i++) {
      List<IntVar> t = terms.get(i);
      IntVar[] vs = new IntVar[t.size() + 1];
      int[] ws = new int[t.size() + 1];
      for (int j = 0; j < t.size(); j++) {
        vs[j] = t.get(j);
        ws[j] = weights.get(i).get(j);
      }
      vs[t.size()] = load[i];
      ws[t.size()] = -1;
      if (fixed[i] > Integer.MAX_VALUE) {
        return;
      }
      pose(new LinearInt(vs, ws, "==", (int) -fixed[i]));
    }
  }

  private void poseLoadSums() {
    for (Object[] p : loadSums) {
      poseLoadSums((IntVar[]) p[0], (IntVar[]) p[1], (int[]) p[2], (Integer) p[3]);
    }
  }

  /** Imposes all delayed constraints. */
  public void poseDelayedConstraints() {
    binPackingCardinality.attach();

    // generate channeling constraints for aliases
    // variables that are output variables
    aliasConstraints();

    // cost_regular constraints over the same word and automaton are filtered together;
    // org.jacop.fz.multiCostRegular=false keeps them apart, =lagrangian adds the relaxation
    String multiCost = System.getProperty("org.jacop.fz.multiCostRegular", "true");
    if (!DISABLED.equalsIgnoreCase(multiCost)) {
      List<Constraint> merged = MultiCostRegular.merge(delayedConstraints);
      if (merged != delayedConstraints) {
        delayedConstraints.clear();
        for (Constraint c : merged) {
          if (c instanceof MultiCostRegular m && "lagrangian".equalsIgnoreCase(multiCost)) {
            m.setLagrangian(true);
          }
          delayedConstraints.add(c);
        }
      }
    }

    // cumulative constraints over the same tasks share one time-table sweep; not under lazy clause
    // generation, where each cumulative constraint explains its own time-table pruning, nor with
    // presolve, whose cumulative reductions read each resource as one constraint;
    // org.jacop.fz.multiCumulative=false keeps them apart
    if (!options.lcg()
        && options.presolve() == Options.Presolve.OFF
        && Boolean.parseBoolean(System.getProperty("org.jacop.fz.multiCumulative", "true"))) {
      List<Constraint> merged = MultiCumulative.merge(delayedConstraints);
      if (merged != delayedConstraints) {
        delayedConstraints.clear();
        delayedConstraints.addAll(merged);
      }
    }

    for (Constraint c : delayedConstraints) {
      store.impose(c);
      if (options.debug()) {
        String s = "% " + c;
        FzConsole.println(s.replace("\n", "\n% "));
      }
    }
    poseAlldistinctConstraints();
    implied(this::poseOverlappingAlldiffs);
    implied(this::posePartitionSums);
    poseAlldiffSums();

    poseLoadSums();

    // generate channeling constraints instead of reified constraints
    reif.pose();
    // generate channeling constraints instead of implied constraints
    imply.pose();
    poseOrderChannels();
  }

  /**
   * Whether the reified comparisons of one variable with constants ({@code int_le_reif}, {@code
   * int_lt_reif} and their {@code >=}, {@code >} forms) become one {@link
   * org.jacop.constraints.ChannelOrder} per variable, as {@code int_eq_reif} becomes ChannelReif.
   * The system property org.jacop.fz.orderChannels=false keeps them as reifications.
   */
  private final boolean orderChannelsOn =
      Boolean.parseBoolean(System.getProperty("org.jacop.fz.orderChannels", "true"));

  /**
   * Whether the half-reified comparisons ({@code int_le_imp} and its kin) join the order channels
   * as implied items; the system property org.jacop.fz.orderChannels.implied=false leaves them as
   * implications.
   */
  private final boolean orderChannelsImplied =
      Boolean.parseBoolean(System.getProperty("org.jacop.fz.orderChannels.implied", "true"));

  // the order reifications b <-> x op c posted so far, for poseOrderChannels
  private final List<Constraint> orderReifications = new ArrayList<>();

  /** Statistics: order channels posted, and the reifications they replaced. */
  int orderChannels;

  int orderChannelItems;

  /**
   * Poses a reified comparison {@code b <-> x op c} of a variable with a constant, or its
   * half-reification {@code b -> x op c}, and keeps it for {@link #poseOrderChannels()} unless a
   * negated control substitution changes it.
   *
   * @param r the reification or implication.
   */
  void poseOrderReification(Constraint r) {
    boolean kept =
        orderChannelsOn
            && (r instanceof Reified || orderChannelsImplied)
            && (activeControl == null || !activeControl.negated());
    pose(r);
    if (kept) {
      orderReifications.add(r);
    }
  }

  /**
   * Replaces the order reifications of each variable with two or more of them by one ChannelOrder
   * over the same variables, which propagates the same bounds with one propagator (rule 5 of
   * presolve, {@link OrderLiterals}).
   */
  void poseOrderChannels() {
    if (orderReifications.isEmpty()) {
      return;
    }
    for (OrderLiterals.Group g : OrderLiterals.groups(orderReifications, orderChannelsImplied)) {
      g.reifications().forEach(Constraint::removeConstraint);
      store.imposeWithConsistency(g.channel());
      orderChannels++;
      orderChannelItems += g.reifications().size();
      if (options.debug()) {
        FzConsole.println("% " + g.channel());
      }
    }
    orderReifications.clear();
    if (orderChannels > 0 && options.debug()) {
      FzConsole.println(
          "% order channels: " + orderChannels + " replace " + orderChannelItems + " reifications");
    }
  }

  /**
   * Finds presence handles of the non-strict k-dimensional diffn constraints by probing; the store
   * must be at a fixpoint.
   *
   * @return false if probing proved the model inconsistent.
   */
  public boolean probeDiffnKHandles() {
    return nonStrictDiffnK.isEmpty()
        || new DiffnKHandleProbing(store, timeOutDeadline()).probe(nonStrictDiffnK);
  }

  void poseAlldistinctConstraints() {
    // the same array can be collected twice, e.g. from circuit and from all_different
    Set<List<IntVar>> posted = new HashSet<>();
    Map<List<IntVar>, Integer> collected = new HashMap<>();
    for (IntVar[] v : parameterListForAlldistincts) {
      collected.merge(List.of(v), 1, Integer::sum);
    }
    for (IntVar[] v : parameterListForAlldistincts) {
      List<IntVar> key = List.of(v);
      if (!posted.add(key)) {
        continue;
      }
      Alldistinct ad = new Alldistinct(v);
      store.impose(ad);
      // implied when no constraint of the model collected the same list
      if (collected.get(key).equals(impliedAlldistincts.get(key))) {
        store.markImplied(ad);
      }
      if (options.debug()) {
        String s = "% " + ad;
        FzConsole.println(s.replace("\n", "\n% "));
      }
    }
  }

  /**
   * Posts an {@link OverlappingAlldiff} next to each pair of all_different constraints that share
   * at least {@link #OVERLAP_MIN_SHARED} variables and at least half of the variables of each, each
   * with a variable of its own, and that have at most {@link #OVERLAP_MAX_VARIABLES} variables
   * together. Pairs sharing less, such as the rows and blocks of a sudoku, gain little pruning for
   * the cost of the propagator. The system property {@code org.jacop.fz.overlappingAlldiff} set to
   * false turns it off.
   */
  void poseOverlappingAlldiffs() {
    // --proof leaves out this redundant constraint, which it does not encode
    if (DISABLED.equalsIgnoreCase(System.getProperty("org.jacop.fz.overlappingAlldiff"))
        || alldifferentLists.size() < 2
        || options.proof() != null) {
      return;
    }
    // fixed variables (often one constant object shared by many lists) are left out: the
    // all_different constraints remove their values, so the rest is all different on its own
    List<IntVar[]> lists = new ArrayList<>();
    for (IntVar[] v : alldifferentLists) {
      lists.add(Arrays.stream(v).filter(x -> !x.singleton()).toArray(IntVar[]::new));
    }
    Map<IntVar, List<Integer>> occurs = new IdentityHashMap<>();
    for (int i = 0; i < lists.size(); i++) {
      for (IntVar v : lists.get(i)) {
        occurs.computeIfAbsent(v, k -> new ArrayList<>()).add(i);
      }
    }
    int posted = 0;
    for (int i = 0; i < lists.size() && posted < OVERLAP_MAX_PAIRS; i++) {
      IntVar[] s = lists.get(i);
      int[] shared = new int[lists.size()];
      for (IntVar v : s) {
        for (int j : occurs.get(v)) {
          if (j > i) {
            shared[j]++;
          }
        }
      }
      for (int j = i + 1; j < shared.length && posted < OVERLAP_MAX_PAIRS; j++) {
        IntVar[] t = lists.get(j);
        if (shared[j] >= OVERLAP_MIN_SHARED
            && shared[j] < s.length
            && shared[j] < t.length
            && 2 * shared[j] >= Math.max(s.length, t.length)
            && s.length + t.length - shared[j] <= OVERLAP_MAX_VARIABLES) {
          OverlappingAlldiff c = new OverlappingAlldiff(s, t);
          store.impose(c);
          posted++;
          if (options.debug()) {
            FzConsole.println("% " + c);
          }
        }
      }
    }
  }

  /** The value of a system property that turns a rule of the front end off. */
  private static final String DISABLED = "false";

  /** Fewest variables of an all_different whose partitions by unit sums get an implied sum. */
  static final int PARTITION_SUMS_MIN_VARIABLES = 4;

  /** Most all_different lists searched for partitions by unit sums. */
  static final int PARTITION_SUMS_MAX_LISTS = 1_000;

  /**
   * Posts the sums implied by unit sums that partition the variables of an all_different.
   *
   * <p>When equalities sum(X_1) = s_1, ..., sum(X_k) = s_k with unit coefficients split the
   * variables of an all_different A into disjoint blocks X_1, ..., X_k, then s_1 + ... + s_k is the
   * sum of the values of A. Those are |A| different values of the union of the domains of A, so the
   * total lies between the sum of the |A| smallest and the sum of the |A| largest values of that
   * union, and is a constant when A is a permutation of it (Choco's implied constraints, here
   * applied to the block sums). The rows of a magic square or a heterosquare are such a partition,
   * and so are its columns. The implied sum over the block sums s_i is posted, and it is also a
   * candidate for an {@link AlldiffSum} when the s_i are pairwise different by the all_different
   * constraints of the model (a heterosquare: the row sums of a permutation of 1..n² add up to
   * n²(n²+1)/2 and are all different, so each of them is far from its bounds). When A has several
   * partitions, the union of their block sums, with the sum of the totals, is one more candidate.
   *
   * <p>This is the aggregation that a linear relaxation of the all_different (the assignment
   * polytope, or the cuts of Williams and Yan, "Representations of the all_different predicate of
   * constraint satisfaction in integer programming", INFORMS Journal on Computing 13(2), 2001)
   * gives an LP solver, and that the propagators of the separate sums cannot see. The system
   * property {@code org.jacop.fz.partitionSums} set to false turns it off.
   */
  void posePartitionSums() {
    // --proof leaves out this redundant constraint, which it does not encode
    if (DISABLED.equalsIgnoreCase(System.getProperty("org.jacop.fz.partitionSums"))
        || options.proof() != null
        || unitSums.isEmpty()
        || alldifferentLists.isEmpty()) {
      return;
    }
    List<UnitSum> equalities = new ArrayList<>();
    for (UnitSum u : unitSums) {
      if ("==".equals(u.rel()) && !u.x().contains(u.sum())) {
        equalities.add(u);
      }
    }
    if (equalities.isEmpty()) {
      return;
    }
    List<UnitSum> implied = new ArrayList<>();
    Set<List<IntVar>> done = new HashSet<>();
    int lists = 0;
    for (IntVar[] a : alldifferentLists) {
      if (a.length >= PARTITION_SUMS_MIN_VARIABLES
          && done.add(List.of(a))
          && lists++ < PARTITION_SUMS_MAX_LISTS) {
        partitionSums(a, equalities, implied);
      }
    }
    // only sums of different variables that are not all fixed, within the AlldiffSum size limits
    for (UnitSum u : implied) {
      List<IntVar> x = u.x();
      if (x.size() >= ALLDIFF_SUM_MIN_VARIABLES
          && x.size() <= ALLDIFF_SUM_MAX_VARIABLES
          && distinct(x)
          && x.stream().anyMatch(v -> !v.singleton())) {
        unitSums.add(u);
      }
    }
  }

  /**
   * Posts the implied sums of the partitions of all_different(a) by the equalities and adds them to
   * implied, as {@link #posePartitionSums()} describes.
   */
  private void partitionSums(IntVar[] a, List<UnitSum> equalities, List<UnitSum> implied) {
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    for (IntVar v : a) {
      index.putIfAbsent(v, index.size());
    }
    if (index.size() != a.length) {
      return;
    }
    List<List<UnitSum>> partitions = partitionsBySums(a, index, equalities);
    long[] total = valueSumBounds(a);
    if (partitions.isEmpty() || total.length == 0) {
      return;
    }
    if (options.debug()) {
      FzConsole.println(
          "% partition sums: "
              + partitions.size()
              + " partition(s) of an all_different of "
              + a.length);
    }
    List<IntVar> union = new ArrayList<>();
    List<IntVar> totals = new ArrayList<>();
    for (List<UnitSum> p : partitions) {
      IntVar[] s = p.stream().map(UnitSum::sum).toArray(IntVar[]::new);
      IntVar t = totalVar(total[0], total[1]);
      pose(new SumInt(s, "==", t));
      implied.add(new UnitSum(List.of(s), "==", t));
      union.addAll(List.of(s));
      totals.add(t);
    }
    long unionLo = partitions.size() * total[0];
    long unionHi = partitions.size() * total[1];
    if (partitions.size() < 2 || unionLo < IntDomain.MIN_INT || unionHi > IntDomain.MAX_INT) {
      return;
    }
    // with a constant total, the sum of the totals is a constant too and needs no constraint
    if (total[0] < total[1]) {
      IntVar t = totalVar(unionLo, unionHi);
      pose(new SumInt(totals, "==", t));
      implied.add(new UnitSum(union, "==", t));
    } else {
      implied.add(new UnitSum(union, "==", dictionary.getConstant((int) unionLo)));
    }
  }

  private static boolean distinct(List<IntVar> x) {
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (IntVar v : x) {
      if (!seen.add(v)) {
        return false;
      }
    }
    return true;
  }

  /**
   * The partitions of the variables of a, each a list of equalities whose summed variables are
   * disjoint and cover a. Equalities over variables of a only are put in layers, each in the first
   * layer it is disjoint from; a layer that covers a is a partition. Greedy: it finds the rows and
   * the columns of a grid, not every partition.
   */
  private static List<List<UnitSum>> partitionsBySums(
      IntVar[] a, Map<IntVar, Integer> index, List<UnitSum> equalities) {
    List<BitSet> covered = new ArrayList<>();
    List<List<UnitSum>> layers = new ArrayList<>();
    for (UnitSum u : equalities) {
      BitSet b = block(u, a.length, index);
      if (b == null) {
        continue;
      }
      int layer = 0;
      while (layer < layers.size() && covered.get(layer).intersects(b)) {
        layer++;
      }
      if (layer == layers.size()) {
        covered.add(new BitSet(a.length));
        layers.add(new ArrayList<>());
      }
      covered.get(layer).or(b);
      layers.get(layer).add(u);
    }
    List<List<UnitSum>> partitions = new ArrayList<>();
    for (int l = 0; l < layers.size(); l++) {
      if (covered.get(l).cardinality() == a.length && layers.get(l).size() > 1) {
        partitions.add(layers.get(l));
      }
    }
    return partitions;
  }

  /**
   * The positions in a of the summed variables of u, or null when the sum variable is in a or a
   * summed variable is not (or occurs twice).
   */
  private static BitSet block(UnitSum u, int size, Map<IntVar, Integer> index) {
    if (index.containsKey(u.sum())) {
      return null;
    }
    BitSet b = new BitSet(size);
    for (IntVar v : u.x()) {
      Integer i = index.get(v);
      if (i == null || b.get(i)) {
        return null;
      }
      b.set(i);
    }
    return b;
  }

  /**
   * The smallest and the largest sum of a.length different values of the union of the domains of a,
   * or an empty array when the union has fewer values (the all_different fails on its own) or a
   * bound does not fit in an int.
   */
  static long[] valueSumBounds(IntVar[] a) {
    IntDomain union = new IntervalDomain();
    for (IntVar v : a) {
      union = union.union(v.dom());
    }
    int n = a.length;
    if (union.getSize() < n) {
      return new long[0];
    }
    long lo = 0;
    int left = n;
    for (int i = 0; i < union.noIntervals() && left > 0; i++) {
      Interval iv = union.getInterval(i);
      int k = (int) Math.min(left, (long) iv.max() - iv.min() + 1);
      lo += k * (long) iv.min() + (long) k * (k - 1) / 2;
      left -= k;
    }
    long hi = 0;
    left = n;
    for (int i = union.noIntervals() - 1; i >= 0 && left > 0; i--) {
      Interval iv = union.getInterval(i);
      int k = (int) Math.min(left, (long) iv.max() - iv.min() + 1);
      hi += k * (long) iv.max() - (long) k * (k - 1) / 2;
      left -= k;
    }
    if (lo < IntDomain.MIN_INT || hi > IntDomain.MAX_INT) {
      return new long[0];
    }
    return new long[] {lo, hi};
  }

  private IntVar totalVar(long lo, long hi) {
    if (lo == hi) {
      return dictionary.getConstant((int) lo);
    }
    return new IntVar(
        store, (int) Math.max(lo, IntDomain.MIN_INT), (int) Math.min(hi, IntDomain.MAX_INT));
  }

  /** sum(x) rel sum with rel one of ==, &lt;=, &gt;=, a candidate for an {@link AlldiffSum}. */
  record UnitSum(List<IntVar> x, String rel, IntVar sum) {}

  /**
   * Records sum(x) rel sum for {@link #poseAlldiffSums()} when the linear constraint has between
   * {@link #ALLDIFF_SUM_MIN_VARIABLES} and {@link #ALLDIFF_SUM_MAX_VARIABLES} distinct variables.
   */
  void recordUnitSum(IntVar[] x, String rel, IntVar sum) {
    if (x.length < ALLDIFF_SUM_MIN_VARIABLES || x.length > ALLDIFF_SUM_MAX_VARIABLES) {
      return;
    }
    unitSums.add(new UnitSum(List.of(x), rel, sum));
  }

  /**
   * Posts an {@link AlldiffSum} next to each linear constraint with unit coefficients whose
   * variables are pairwise different by the all_different constraints of the model (each pair is in
   * some all_different), such as the cages of a killer sudoku or the rows of a magic square. The
   * linear constraint alone sees only the sum of the bounds; the AlldiffSum also sees that the
   * values are distinct. The system property {@code org.jacop.fz.alldiffSum} set to false turns it
   * off.
   */
  void poseAlldiffSums() {
    if (DISABLED.equalsIgnoreCase(System.getProperty("org.jacop.fz.alldiffSum"))
        || unitSums.isEmpty()) {
      return;
    }
    List<IntVar[]> lists = new ArrayList<>(alldifferentLists);
    lists.addAll(detectedAlldifferentLists);
    if (lists.isEmpty()) {
      return;
    }
    Map<IntVar, BitSet> occurs = new IdentityHashMap<>();
    for (int i = 0; i < lists.size(); i++) {
      for (IntVar v : lists.get(i)) {
        occurs.computeIfAbsent(v, k -> new BitSet()).set(i);
      }
    }
    Set<UnitSum> posted = new HashSet<>();
    for (UnitSum u : unitSums) {
      IntVar[] x = u.x().toArray(new IntVar[0]);
      if (pairwiseDifferent(x, occurs) && posted.add(u)) {
        // an alldifferent on all of x (or a superset) does the pruning on Hall intervals
        BitSet common = (BitSet) occurs.get(x[0]).clone();
        for (IntVar v : x) {
          common.and(occurs.get(v));
        }
        AlldiffSum c = new AlldiffSum(x, u.rel(), u.sum(), common.isEmpty());
        store.impose(c);
        if (options.debug()) {
          FzConsole.println("% " + c);
        }
      }
    }
  }

  private static boolean pairwiseDifferent(IntVar[] x, Map<IntVar, BitSet> occurs) {
    BitSet[] in = new BitSet[x.length];
    for (int i = 0; i < x.length; i++) {
      in[i] = occurs.get(x[i]);
      if (in[i] == null) {
        return false;
      }
      for (int j = 0; j < i; j++) {
        if (x[i] == x[j] || !in[i].intersects(in[j])) {
          return false;
        }
      }
    }
    return true;
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
      FzConsole.println(s.replace("\n", "\n% "));
    }
  }

  /**
   * The control {@code from} of a half-reified constraint replaced by the literal {@code to}, or by
   * its negation, when the constraint is posted ({@link EnforcementInliner}).
   *
   * @param from the eliminated control.
   * @param to the variable of the literal that replaces it.
   * @param negated true when the literal is {@code to = 0}.
   */
  public record ControlSubstitution(IntVar from, IntVar to, boolean negated) {}

  /** The constraint nodes posted with a substituted control. */
  Map<SimpleNode, ControlSubstitution> controlSubstitutions = new IdentityHashMap<>();

  /** The substitutions by eliminated control, for detectors that read controls as literals. */
  Map<IntVar, ControlSubstitution> substitutedControls = new IdentityHashMap<>();

  private ControlSubstitution activeControl;

  private boolean activeConverted;

  private boolean activeOther;

  /**
   * The substitution of an eliminated control, or null.
   *
   * @param b a control of a half-reified constraint.
   * @return the substitution of b, or null if b was not eliminated.
   */
  public ControlSubstitution substitutedControl(IntVar b) {
    return substitutedControls.isEmpty() ? null : substitutedControls.get(b);
  }

  /**
   * The substitution to apply while the given constraint node is posted, or null.
   *
   * @param node a constraint node.
   * @return its substitution, or null.
   */
  public ControlSubstitution controlSubstitution(SimpleNode node) {
    return controlSubstitutions.isEmpty() ? null : controlSubstitutions.get(node);
  }

  /**
   * Forgets the constraint nodes posted with a substituted control once all constraints are posted,
   * since through their parents they hold the parse tree of every such constraint, and the
   * substitutions by eliminated control, which only detectors read (4.5 MB of rcpsp_max
   * psp_ubo500_33 during the search).
   */
  public void releaseControlSubstitutions() {
    // new maps, since a cleared one keeps its table
    controlSubstitutions = new IdentityHashMap<>();
    substitutedControls = new IdentityHashMap<>();
  }

  /**
   * Forgets the sums recorded for {@link #poseAlldiffSums()} once all constraints are posted: one
   * record per sum of unit coefficients, 146 MB on XCSP 2022 DiamondFree-80 (1.6 million sums).
   */
  public void releaseUnitSums() {
    unitSums.clear();
    unitSums.trimToSize();
  }

  /** Forgets the equalities collected for the channel constraints once all are posted. */
  public void releaseChannelMaps() {
    reif.release();
    imply.release();
  }

  /**
   * Starts posting a constraint node with a substituted control.
   *
   * @param s the substitution.
   */
  public void beginControlSubstitution(ControlSubstitution s) {
    activeControl = s;
    activeConverted = false;
    activeOther = false;
  }

  /**
   * Ends posting a node with a substituted control. A negated control that no constraint posted for
   * the node could take is linked to its literal instead, so the model stays the same.
   *
   * @return true if the control is no longer needed by the node's constraints.
   */
  public boolean endControlSubstitution() {
    ControlSubstitution s = activeControl;
    activeControl = null;
    if (s == null || !s.negated()) {
      return true;
    }
    if (activeConverted && !activeOther) {
      return true;
    }
    // from = not to, as the removed clause to \/ from allowed
    pose(new XneqY(s.from(), s.to()));
    return false;
  }

  // whether b => c over x and y is posted while b stands for a negated literal; marks it converted
  private boolean negatedControl(IntVar b, IntVar x, IntVar y) {
    ControlSubstitution s = activeControl;
    if (s == null || !s.negated() || b != s.from() || x == s.to() || y == s.to()) {
      return false;
    }
    activeConverted = true;
    return true;
  }

  // b => c over the eliminated control becomes to = 0 => c
  private Constraint negateControl(Constraint c) {
    ControlSubstitution s = activeControl;
    if (c.getClass() == Implies.class && ((Implies) c).b == s.from()) {
      Implies i = (Implies) c;
      if (!i.c.arguments().contains(s.from()) && !i.c.arguments().contains(s.to())) {
        activeConverted = true;
        return new ImpliesNot(s.to(), i.c);
      }
    } else if (c.getClass() == XplusClteqZImplied.class && ((XplusClteqZImplied) c).b == s.from()) {
      XplusClteqZImplied i = (XplusClteqZImplied) c;
      if (i.x != s.to() && i.z != s.to()) {
        activeConverted = true;
        return new XplusClteqZImpliedNot(s.to(), i.x, i.c, i.z);
      }
    }
    if (c.arguments().contains(s.from())) {
      activeOther = true;
    }
    return c;
  }

  /**
   * The time-out of the run as given by {@link System#currentTimeMillis()}, for {@link
   * Store#consistencyUntil(long)}.
   *
   * @return the deadline, or 0 when there is no time-out
   */
  public long timeOutDeadline() {
    return options != null && options.getTimeOut() > 0
        ? System.currentTimeMillis() + options.getRemainingTimeOut()
        : 0;
  }

  /**
   * Runs a propagation of the model being built, which stops with {@link ModelTimeOut} once the
   * time-out has passed: bounds that converge one unit per step (x &lt; y &lt; z &lt; x over wide
   * domains) take minutes to fail. A failure at the time-out proves nothing, so it is no failure.
   *
   * @param propagation the propagation, which throws FailException when the model fails
   * @throws FailException when the model fails before the time-out
   */
  public void propagateUntilTimeOut(Runnable propagation) throws FailException {
    boolean deadline =
        options != null && options.getTimeOut() > 0 && store.getConsistencyDeadline() == 0;
    if (deadline) {
      store.setConsistencyDeadline(System.currentTimeMillis() + options.getRemainingTimeOut());
    }
    try {
      propagation.run();
    } catch (FailException e) {
      if (deadline && store.isConsistencyDeadlinePassed()) {
        throw new ModelTimeOut();
      }
      throw e;
    } finally {
      if (deadline) {
        store.setConsistencyDeadline(0);
      }
    }
  }

  /**
   * Poses the count of value in list, between lo and hi or equal to counter. With lazy clause
   * generation a count of more than {@code lcg-split} variables is split as {@link LinearSplit}
   * splits a sum: a Count over each block of about sqrt(n) variables defines the block's count, and
   * the sum of the block counts is the counter. The explanation of a count cites every variable
   * that is or cannot be the value, about n literals; over blocks a reason cites the counts of the
   * other blocks, and learnt clauses can speak of a block's count. This is the totalizer of
   * Bailleux and Boufkhad ("Efficient CNF encoding of Boolean cardinality constraints", CP 2003)
   * with lazily created count literals, as lazy clause generation splits long sums (Abio and
   * Stuckey, "Encoding linear constraints into SAT", CP 2014). Peaceable queens 8 (MiniZinc
   * Challenge 2021), whose objective counts one colour over 64 squares, is proved only with it.
   * {@code lcg-split-count=0} keeps counts whole.
   *
   * @param list the counted variables, each of which can take value
   * @param value the counted value
   * @param counter the number of variables equal to value, or null for the bounds lo and hi
   * @param lo the least count when counter is null
   * @param hi the largest count when counter is null
   */
  void poseCount(List<IntVar> list, int value, IntVar counter, int lo, int hi) {
    int limit = options.lcg() ? Integer.parseInt(options.freeConfig("lcg-split", "20")) : 0;
    int n = list.size();
    if (limit <= 1 || n <= limit || "0".equals(options.freeConfig("lcg-split-count", "1"))) {
      pose(
          counter == null ? new CountBounds(list, value, lo, hi) : new Count(list, counter, value));
      return;
    }
    int size = Math.min((int) Math.ceil(Math.sqrt(n)), limit);
    List<IntVar> sums = new ArrayList<>();
    int from = 0;
    while (from < n) {
      // a last block of one variable joins the block before it
      int to = n - (from + size) == 1 ? n : Math.min(n, from + size);
      List<IntVar> block = list.subList(from, to);
      IntVar s = new IntVar(store, 0, block.size());
      Constraint blockCount = new Count(block, s, value);
      propagateUntilTimeOut(() -> store.imposeWithConsistency(blockCount));
      dictionary.addSplitCount(s);
      sums.add(s);
      from = to;
    }
    IntVar c = counter == null ? new IntVar(store, lo, hi) : counter;
    IntVar[] top = new IntVar[sums.size() + 1];
    int[] w = new int[top.length];
    for (int i = 0; i < sums.size(); i++) {
      top[i] = sums.get(i);
      w[i] = 1;
    }
    top[sums.size()] = c;
    w[sums.size()] = -1;
    LinearInt sum = new LinearInt(top, w, "==", 0);
    // dom/wdeg weighs the counted variables when the sum of the blocks fails
    sum.setWeightedVariables(list.toArray(new IntVar[0]));
    pose(sum);
  }

  /**
   * Poses CountValues over a list, or under lazy clause generation, for a list longer than
   * lcg-split (20) variables, CountValues over blocks of about sqrt(n) variables and, for each
   * value, a sum of the block counters equal to its counter, as {@link #poseCount} does for one
   * value. A constraint whose block counters would outnumber its variables stays whole, and so does
   * every one with --free-config lcg-split-count-values=0.
   *
   * @param list the counted variables
   * @param counters the counter of each value
   * @param values the counted values
   * @return whether the constraint was split
   */
  boolean poseCountValuesSplit(IntVar[] list, IntVar[] counters, int[] values) {
    int limit = options.lcg() ? Integer.parseInt(options.freeConfig("lcg-split", "20")) : 0;
    int n = list.length;
    if (limit <= 1
        || n <= limit
        || "0".equals(options.freeConfig("lcg-split-count-values", "1"))
        || "0".equals(options.freeConfig("lcg-split-count", "1"))) {
      return false;
    }
    int size = Math.min((int) Math.ceil(Math.sqrt(n)), limit);
    // a counter per block and value: more of them than counted variables (many values, as in
    // warehouse assignments) costs more than the shorter reasons give back
    if ((long) Math.ceilDiv(n, size) * values.length > n) {
      return false;
    }
    List<List<IntVar>> blockCounters = new ArrayList<>();
    int from = 0;
    while (from < n) {
      int to = n - (from + size) == 1 ? n : Math.min(n, from + size);
      IntVar[] block = Arrays.copyOfRange(list, from, to);
      IntVar[] bc = new IntVar[values.length];
      for (int k = 0; k < values.length; k++) {
        bc[k] = new IntVar(store, 0, block.length);
        dictionary.addSplitCount(bc[k]);
      }
      Constraint blockCount = new CountValues(block, bc, values);
      propagateUntilTimeOut(() -> store.imposeWithConsistency(blockCount));
      blockCounters.add(List.of(bc));
      from = to;
    }
    for (int k = 0; k < values.length; k++) {
      IntVar[] top = new IntVar[blockCounters.size() + 1];
      int[] w = new int[top.length];
      for (int b = 0; b < blockCounters.size(); b++) {
        top[b] = blockCounters.get(b).get(k);
        w[b] = 1;
      }
      top[blockCounters.size()] = counters[k];
      w[blockCounters.size()] = -1;
      LinearInt sum = new LinearInt(top, w, "==", 0);
      sum.setWeightedVariables(list);
      pose(sum);
    }
    poseCounterTotal(list, counters, values);
    return true;
  }

  /**
   * Poses the total of the counters of a split CountValues: at most the number of variables, and
   * exactly that when every variable takes one of the values. The whole CountValues knows it, the
   * sums of the block counters do not: XCSP 2025 RoadefPlaning2-2022-10 (a count of 162 variables
   * over 5 values) was refuted at the root by the whole constraint and stayed open for 240 s after
   * the split.
   */
  private void poseCounterTotal(IntVar[] list, IntVar[] counters, int[] values) {
    IntervalDomain covered = new IntervalDomain();
    for (int v : values) {
      covered.unionAdapt(v, v);
    }
    boolean all = true;
    for (IntVar x : list) {
      if (!x.dom().isIntersecting(covered) || !covered.contains(x.dom())) {
        all = false;
        break;
      }
    }
    int[] ones = new int[counters.length];
    Arrays.fill(ones, 1);
    pose(new LinearInt(counters, ones, all ? "==" : "<=", list.length));
  }

  void pose(Constraint c) throws FailException {

    if (activeControl != null && activeControl.negated()) {
      c = negateControl(c);
    }

    if (options.lcg()) {
      Constraint split =
          LinearSplit.split(
              store,
              c,
              Integer.parseInt(options.freeConfig("lcg-split", "20")),
              !"0".equals(options.freeConfig("lcg-split-tree", "1")),
              // free LCG search branches on the block sums last, as on other defined variables, and
              // the linear relaxation replaces them by their blocks
              dictionary::addSplitSum);
      if (split != null) {
        c = split;
      }
    }

    Constraint posted = c;
    propagateUntilTimeOut(
        () -> {
          if (constraintPriority >= 0 && constraintPriority <= 4) {
            store.imposeWithConsistency(posted, constraintPriority);
          } else {
            store.imposeWithConsistency(posted);
          }
        });

    if (options.debug()) {
      String s = "% " + c;
      FzConsole.println(s.replace("\n", "\n% "));
    }
  }

  /** Largest domain of x for which z of x * c = z gets the holes of c * dom(x) at the root. */
  static final int MUL_C_HOLES_MAX_SIZE = 64;

  /**
   * Poses x * c = z. XmulCeqZ is bounds consistent, so when x has few values z is first restricted
   * to c * dom(x): for a 0/1 variable x, z gets {0, c}, and bounds on z then decide x both ways.
   *
   * @param x the variable multiplied by c
   * @param c the constant
   * @param z the result
   */
  void poseXmulCeqZ(IntVar x, int c, IntVar z) throws FailException {
    if (c != 0 && !z.singleton() && x.getSize() <= MUL_C_HOLES_MAX_SIZE) {
      IntDomain values = new IntervalDomain();
      ValueEnumeration e = x.dom().valueEnumeration();
      int[] products = new int[x.getSize()];
      int n = 0;
      while (e.hasMoreElements()) {
        long product = (long) e.nextElement() * c;
        if (product >= IntDomain.MIN_INT && product <= IntDomain.MAX_INT) {
          products[n++] = (int) product;
        }
      }
      Arrays.sort(products, 0, n);
      for (int i = 0; i < n; i++) {
        values.unionAdapt(products[i], products[i]);
      }
      z.domain.in(store.level, z, values);
    }
    pose(new XmulCeqZ(x, c, z));
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
      propagateFzXeqYwhenBzero(store, x, y, isReified, removeConstraint);
      return;
    }
    if (b.min() == 1) {
      propagateFzXeqYwhenBone(store, x, y);
    }
  }

  private void propagateFzXeqYwhenBzero(
      Store store, IntVar x, IntVar y, boolean isReified, Runnable removeConstraint) {
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
  }

  private void propagateFzXeqYwhenBone(Store store, IntVar x, IntVar y) {
    do {
      AtomicTrail.in(store, x, y.domain);
      store.propagationHasOccurred = false;
      AtomicTrail.in(store, y, x.domain);
    } while (store.propagationHasOccurred);
  }

  Constraint fzXeqC(IntVar x, int c, IntVar b, boolean isReified) {
    return new FzXeqC(x, c, b, isReified);
  }

  /** The constraint x = c, reified with b or implied by b. */
  final class FzXeqC extends Constraint
      implements Violation,
          Copyable<FzXeqC>,
          Explainable,
          ValueIndicator,
          PbEncodable,
          ConflictRows,
          Linearizations.Relaxable {

    final IntVar x;
    final int c;
    final IntVar b;
    final boolean isReified;
    final int fzNumberId;

    FzXeqC(IntVar x, int c, IntVar b, boolean isReified) {
      super(new IntVar[] {x, b});
      this.x = x;
      this.c = c;
      this.b = b;
      this.isReified = isReified;
      this.fzNumberId = isReified ? n1.incrementAndGet() : n2.incrementAndGet();
    }

    @Override
    public boolean encode(PbModel model) {
      if (x == b) {
        return false;
      }
      model.reified(
          b, new LinearForm(new IntVar[] {x}, new long[] {1}, c, LinearForm.EQ), isReified);
      return true;
    }

    @Override
    public IntVar indicator() {
      return isReified ? b : null;
    }

    @Override
    public IntVar variable() {
      return x;
    }

    @Override
    public int value() {
      return c;
    }

    @Override
    public void consistency(final Store store) {
      propagateFzXeqC(store, x, c, b, isReified, this::removeConstraint);
    }

    // b -> x = c (x != c when b is false is not linear)
    @Override
    public List<LinearForm> conflictRows() {
      return Linearizations.of(new Implies(b, new XeqC(x, c)));
    }

    // b -> x = c, and !b -> x != c when c is a bound of x
    @Override
    public List<LinearForm> relaxation() {
      return Linearizations.valueRows(x, c, b, isReified, true);
    }

    @Override
    public String toString() {
      if (isReified) {
        return "fzXeqCreified" + fzNumberId + ": XeqC_Reified(" + x + ", " + c + ", " + b + " )";
      } else {
        return "fzXeqCimplied" + fzNumberId + ": XeqC_Implied(" + b + ", " + x + ", " + c + " )";
      }
    }

    @Override
    public String id() {
      return isReified ? "fzXeqCreified" + fzNumberId : "fzXeqCimplied" + fzNumberId;
    }

    // the reified constraint, for its explanations
    private XeqC lcgNested;

    @Override
    public boolean explain(AtomicTrail trail, int entry, EntryList out) {
      return x != b && ReifiedExplanation.explain(trail, entry, b, nested(), isReified, out);
    }

    @Override
    public boolean explainFailure(AtomicTrail trail, EntryList out) {
      return x != b && ReifiedExplanation.explainFailure(trail, b, nested(), isReified, out);
    }

    private XeqC nested() {
      if (lcgNested == null) {
        lcgNested = new XeqC(x, c);
      }
      return lcgNested;
    }

    @Override
    public FzXeqC copy(VarMap map) {
      return new FzXeqC(map.get(x), c, map.get(b), isReified);
    }

    @Override
    public long violation(ToIntFunction<IntVar> value) {
      boolean holds = value.applyAsInt(x) == c;
      boolean on = value.applyAsInt(b) == 1;
      return (isReified ? on == holds : !on || holds) ? 0 : 1;
    }
  }

  Constraint fzXeqCreified(IntVar x, int c, IntVar b) {
    return fzXeqC(x, c, b, true);
  }

  Constraint fzXeqCimplied(IntVar x, int c, IntVar b) {
    if (negatedControl(b, x, x)) {
      return new ImpliesNot(activeControl.to(), new XeqC(x, c));
    }
    return fzXeqC(x, c, b, false);
  }

  Constraint fzXneqC(IntVar x, int c, IntVar b, boolean isReified) {
    return new FzXneqC(x, c, b, isReified);
  }

  /** The constraint x != c, reified with b or implied by b. */
  final class FzXneqC extends Constraint
      implements Violation,
          Copyable<FzXneqC>,
          Explainable,
          PbEncodable,
          ValueExclusion,
          Linearizations.Relaxable {

    final IntVar x;
    final int c;
    final IntVar b;
    final boolean isReified;
    final int fzNumberId;

    FzXneqC(IntVar x, int c, IntVar b, boolean isReified) {
      super(new IntVar[] {x, b});
      this.x = x;
      this.c = c;
      this.b = b;
      this.isReified = isReified;
      this.fzNumberId = isReified ? n3.incrementAndGet() : n4.incrementAndGet();
    }

    @Override
    public boolean encode(PbModel model) {
      if (x == b) {
        return false;
      }
      model.reified(
          b, new LinearForm(new IntVar[] {x}, new long[] {1}, c, LinearForm.NE), isReified);
      return true;
    }

    @Override
    public void consistency(final Store store) {
      propagateFzXneqC(store, x, c, b, isReified, this::removeConstraint);
    }

    // !b -> x = c when reified, and b -> x != c when c is a bound of x
    @Override
    public List<LinearForm> relaxation() {
      return Linearizations.valueRows(x, c, b, isReified, false);
    }

    @Override
    public IntVar control() {
      return x == b ? null : b;
    }

    @Override
    public IntVar variable() {
      return x;
    }

    @Override
    public int value() {
      return c;
    }

    @Override
    public String toString() {
      if (isReified) {
        return "fzXneqCreified" + fzNumberId + ": XneqC_Reified(" + x + ", " + c + ", " + b + " )";
      } else {
        return "fzXneqCImpled" + fzNumberId + ": XneqC_Implied(" + b + ", " + x + ", " + c + " )";
      }
    }

    @Override
    public String id() {
      return isReified ? "fzXneqCreified" + fzNumberId : "fzXneqCimplied" + fzNumberId;
    }

    // the reified constraint, for its explanations
    private XneqC lcgNested;

    @Override
    public boolean explain(AtomicTrail trail, int entry, EntryList out) {
      return x != b && ReifiedExplanation.explain(trail, entry, b, nested(), isReified, out);
    }

    @Override
    public boolean explainFailure(AtomicTrail trail, EntryList out) {
      return x != b && ReifiedExplanation.explainFailure(trail, b, nested(), isReified, out);
    }

    private XneqC nested() {
      if (lcgNested == null) {
        lcgNested = new XneqC(x, c);
      }
      return lcgNested;
    }

    @Override
    public FzXneqC copy(VarMap map) {
      return new FzXneqC(map.get(x), c, map.get(b), isReified);
    }

    @Override
    public long violation(ToIntFunction<IntVar> value) {
      boolean holds = value.applyAsInt(x) != c;
      boolean on = value.applyAsInt(b) == 1;
      return (isReified ? on == holds : !on || holds) ? 0 : 1;
    }
  }

  Constraint fzXneqCreified(IntVar x, int c, IntVar b) {
    return fzXneqC(x, c, b, true);
  }

  Constraint fzXneqCimplied(IntVar x, int c, IntVar b) {
    if (negatedControl(b, x, x)) {
      return new ImpliesNot(activeControl.to(), new XneqC(x, c));
    }
    return fzXneqC(x, c, b, false);
  }

  Constraint fzXeqY(IntVar x, IntVar y, IntVar b, boolean isReified) {
    return new FzXeqY(x, y, b, isReified);
  }

  /** The constraint x = y, reified with b or implied by b. */
  final class FzXeqY extends Constraint
      implements Violation,
          Copyable<FzXeqY>,
          Explainable,
          PbEncodable,
          ConflictRows,
          Linearizations.Relaxable,
          PartitionCuts.Equality {

    final IntVar x;
    final IntVar y;
    final IntVar b;
    final boolean isReified;
    final int fzNumberId;

    @Override
    public IntVar left() {
      return x;
    }

    @Override
    public IntVar right() {
      return y;
    }

    @Override
    public IntVar indicator() {
      return isReified ? b : null;
    }

    FzXeqY(IntVar x, IntVar y, IntVar b, boolean isReified) {
      super(new IntVar[] {x, y, b});
      this.x = x;
      this.y = y;
      this.b = b;
      this.isReified = isReified;
      this.fzNumberId = isReified ? n5.incrementAndGet() : n6.incrementAndGet();
    }

    @Override
    public void consistency(final Store store) {
      propagateFzXeqY(store, x, y, b, isReified, this::removeConstraint);
    }

    // b -> x = y (x != y when b is false is not linear)
    @Override
    public List<LinearForm> conflictRows() {
      return Linearizations.of(new Implies(b, new XeqY(x, y)));
    }

    @Override
    public List<LinearForm> relaxation() {
      return conflictRows();
    }

    @Override
    public String toString() {
      if (isReified) {
        return "fzXeYCReified" + fzNumberId + ": XeqY_Reified(" + x + ", " + y + ", " + b + " )";
      } else {
        return "fzXeqYimplied" + fzNumberId + ": XeqY_Implied(" + x + ", " + y + ", " + b + " )";
      }
    }

    @Override
    public String id() {
      return isReified ? "fzXeqYreified" + fzNumberId : "fzXeqYimplied" + fzNumberId;
    }

    // the reified constraint, for its explanations
    private XeqY lcgNested;

    @Override
    public boolean explain(AtomicTrail trail, int entry, EntryList out) {
      return x != b
          && y != b
          && x != y
          && ReifiedExplanation.explain(trail, entry, b, nested(), isReified, out);
    }

    @Override
    public boolean explainFailure(AtomicTrail trail, EntryList out) {
      return x != b
          && y != b
          && x != y
          && ReifiedExplanation.explainFailure(trail, b, nested(), isReified, out);
    }

    @Override
    public boolean encode(PbModel model) {
      if (x == b || y == b || x == y) {
        return false;
      }
      model.reified(
          b, new LinearForm(new IntVar[] {x, y}, new long[] {1, -1}, 0, LinearForm.EQ), isReified);
      return true;
    }

    private XeqY nested() {
      if (lcgNested == null) {
        lcgNested = new XeqY(x, y);
      }
      return lcgNested;
    }

    @Override
    public FzXeqY copy(VarMap map) {
      return new FzXeqY(map.get(x), map.get(y), map.get(b), isReified);
    }

    @Override
    public long violation(ToIntFunction<IntVar> value) {
      boolean holds = value.applyAsInt(x) == value.applyAsInt(y);
      boolean on = value.applyAsInt(b) == 1;
      return (isReified ? on == holds : !on || holds) ? 0 : 1;
    }
  }

  Constraint fzXeqYreified(IntVar x, IntVar y, IntVar b) {
    return fzXeqY(x, y, b, true);
  }

  Constraint fzXeqYimplied(IntVar x, IntVar y, IntVar b) {
    if (negatedControl(b, x, y)) {
      return new ImpliesNot(activeControl.to(), new XeqY(x, y));
    }
    return fzXeqY(x, y, b, false);
  }

  Constraint fzIfThenBool(IntVar b, IntVar x) {
    if (negatedControl(b, x, x)) {
      return new ImpliesNot(activeControl.to(), new XeqC(x, 1));
    }
    return new FzIfThenBool(b, x);
  }

  /** The constraint b implies x, for 0/1 variables. */
  final class FzIfThenBool extends Constraint implements Copyable<FzIfThenBool>, PbEncodable {

    final IntVar b;
    final IntVar x;
    final int fzNumberId;

    FzIfThenBool(IntVar b, IntVar x) {
      super(new IntVar[] {b, x});
      this.b = b;
      this.x = x;
      this.fzNumberId = n7.incrementAndGet();
    }

    @Override
    public boolean encode(PbModel model) {
      model.clause(new IntVar[] {x}, new IntVar[] {b});
      return true;
    }

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
      return "fzIfThenBool" + fzNumberId + ": IfThenBool(" + b + ", " + x + " )";
    }

    @Override
    public String id() {
      return "fzIfThenBool" + fzNumberId;
    }

    @Override
    public FzIfThenBool copy(VarMap map) {
      return new FzIfThenBool(map.get(b), map.get(x));
    }
  }
}
