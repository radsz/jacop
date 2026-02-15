/*
 * VariablesParameters.java
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

package org.jacop.fz;

import java.util.ArrayList;
import java.util.HashSet;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XeqY;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.PeqQ;
import org.jacop.floats.core.FloatVar;
import org.jacop.set.constraints.AeqB;
import org.jacop.set.constraints.AeqS;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * TODO, a short description what it does and how it is used. Remark, it would be beneficial if all
 * the methods were described, like generateParameters(...) below.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class VariablesParameters implements ParserTreeConstants {

  public static final double MIN_FLOAT = -1e150;
  // for variables
  public static final double MAX_FLOAT = 1e150;
  // if they are not in interval
  // IntDomain.MIN_INT..IntDomainMaxInt raise Arithmetic
  // exception
  public static final int MIN_INT = IntDomain.MIN_INT;
  public static final int MAX_INT = IntDomain.MAX_INT;
  static final boolean INTERVAL = false; // selection of interval or dense, if possible, domain
  static final boolean CHECK_BOUNDS = false; // whether to check bounds of IntVar before creation;
  Tables dictionary;
  int lowInterval;
  int highInterval;
  double lowFloatInterval;
  double highFloatInterval;

  ArrayList<Integer> intList;
  IntervalDomain rangeDomain;
  HashSet<String> annotations;
  ArrayList<IntDomain> indexBounds;

  int numberBooleanVariables;
  int numberFloatVariables;
  int numberSetVariables;

  Options options;
  boolean debug;

  /** It constructs variables parameters. */
  public VariablesParameters() {
    // Default constructor; fields are initialized by setters and initContext.
  }

  void setOptions(Options options) {
    this.options = options;
    debug = options.debug();
  }

  /**
   * Initializes the dictionary and annotations for a generation method.
   *
   * @param table the table to use as dictionary
   */
  private void initContext(Tables table) {
    dictionary = table;
    annotations = new HashSet<>();
  }

  /**
   * Validates and adjusts float interval bounds, printing warnings if they exceed MIN_FLOAT or
   * MAX_FLOAT.
   *
   * @param ident the variable identifier for error messages
   * @param varKind the kind of variable (e.g., "float variable" or "array float variable")
   */
  private void validateFloatInterval(String ident, String varKind) {
    if (lowFloatInterval > highFloatInterval) {
      throw Store.failException;
    }
    if (lowFloatInterval < MIN_FLOAT) {
      System.err.println(
          "Minimal value for " + varKind + " " + ident + " too low; changed to " + MIN_FLOAT);
      lowFloatInterval = MIN_FLOAT;
    }
    if (highFloatInterval > MAX_FLOAT) {
      System.err.println(
          "Maximal value for " + varKind + " " + ident + " too high; changed to " + MAX_FLOAT);
      highFloatInterval = MAX_FLOAT;
    }
  }

  /**
   * Extracts and validates an integer interval from an AST node, storing the result in
   * lowInterval/highInterval.
   *
   * @param tail the AST node containing interval bounds
   */
  private void extractIntInterval(ASTIntTiExprTail tail) {
    lowInterval = tail.getLow();
    highInterval = tail.getHigh();
    if (CHECK_BOUNDS) {
      if (lowInterval < IntDomain.MIN_INT || highInterval > IntDomain.MAX_INT) {
        throw new ArithmeticException(
            "Too large bounds on intervals " + lowInterval + ".." + highInterval);
      }
    }
  }

  /**
   * Extracts and validates an integer list from an AST node, storing the result in intList.
   *
   * @param intLiterals the AST node containing the list of integers
   */
  private void extractIntList(ASTIntLiterals intLiterals) {
    intList = intLiterals.getList();
    if (CHECK_BOUNDS) {
      for (Integer e : intList) {
        if (e < IntDomain.MIN_INT || e > IntDomain.MAX_INT) {
          throw new ArithmeticException("Too large element in set " + e);
        }
      }
    }
  }

  /**
   * It generates a parameter from a given node and stores information about it in the table.
   *
   * @param node the node from which the parameter is being generated.
   * @param table the table where the parameters are being stored.
   */
  void generateParameters(SimpleNode node, Tables table) {

    initContext(table);

    int type = getType(node);

    int initChild = getAnnotations(node, 1);

    String ident;
    int val;
    IntDomain setValue;
    switch (type) {
      case 0: // int
      case 1: // int interval
      case 2: // int list
      case 3: // bool
        ident = ((ASTVarDeclItem) node).getIdent();
        val = getScalarFlatExpr(node, initChild);
        table.addInt(ident, val);
        break;
      case 4: // set int
      case 5: // set interval
      case 6: // set list
      case 7: // bool set
      case 10: // range set
        ident = ((ASTVarDeclItem) node).getIdent();
        setValue = getSetLiteral(node, initChild);
        table.addSet(ident, setValue);
        break;
      case 8: // float
        ident = ((ASTVarDeclItem) node).getIdent();
        double valFloat = getScalarFlatExprFloat(node, initChild);
        table.addFloat(ident, valFloat);
        break;
      default:
        throw new IllegalArgumentException("Not supported type in parameter; compilation aborted.");
    }
  }

  void generateVariables(SimpleNode node, Tables table, Store store) {

    initContext(table);
    boolean outputVar = false;

    int type = getType(node);
    int initChild = getAnnotations(node, 1);

    if (annotations.contains("output_var")) {
      outputVar = true;
    }

    String ident;
    IntVar varInt;
    SetVar varSet;
    FloatVar varFloat;

    switch (type) {
      case 0: // int
        ident = ((ASTVarDeclItem) node).getIdent();
        varInt = new IntVar(store, ident, MIN_INT, MAX_INT);
        initAndRegisterIntVar(store, ident, varInt, node, initChild, table, outputVar);
        break;
      case 1: // int interval
        generateIntIntervalVariable(store, node, initChild, table, outputVar);
        break;
      case 2: // int list
        generateIntListVariable(store, node, initChild, table, outputVar);
        break;
      case 3: // bool
        ident = ((ASTVarDeclItem) node).getIdent();
        varInt = new BooleanVar(store, ident);
        initAndRegisterIntVar(store, ident, varInt, node, initChild, table, outputVar);
        numberBooleanVariables++;
        break;
      case 4: // set int
        ident = ((ASTVarDeclItem) node).getIdent();
        varSet = new SetVar(store, ident, new BoundSetDomain(MIN_INT, MAX_INT));
        initAndRegisterSetVar(store, ident, varSet, node, initChild, table, outputVar);
        break;
      case 5: // set interval
        ident = ((ASTVarDeclItem) node).getIdent();
        if (lowInterval > highInterval) {
          varSet = new SetVar(store, ident, new BoundSetDomain());
        } else {
          varSet =
              new SetVar(
                  store,
                  ident,
                  new BoundSetDomain(
                      new IntervalDomain(), new IntervalDomain(lowInterval, highInterval)));
        }
        initAndRegisterSetVar(store, ident, varSet, node, initChild, table, outputVar);
        break;
      case 6: // set list
        ident = ((ASTVarDeclItem) node).getIdent();
        SetDomain dom = new BoundSetDomain();
        for (Integer e : intList) {
          dom.addDom(e, e);
        }
        varSet = new SetVar(store, ident, dom);
        initAndRegisterSetVar(store, ident, varSet, node, initChild, table, outputVar);
        break;
      case 10: // range set
        ident = ((ASTVarDeclItem) node).getIdent();
        varSet = new SetVar(store, ident, new BoundSetDomain(new IntervalDomain(), rangeDomain));
        initAndRegisterSetVar(store, ident, varSet, node, initChild, table, outputVar);
        break;
      case 7: // bool set
        ident = ((ASTVarDeclItem) node).getIdent();
        varSet = new SetVar(store, ident, new BoundSetDomain(0, 1));
        initAndRegisterSetVar(store, ident, varSet, node, initChild, table, outputVar);
        break;
      case 8: // float
        ident = ((ASTVarDeclItem) node).getIdent();
        varFloat = new FloatVar(store, ident, MIN_FLOAT, MAX_FLOAT);
        initAndRegisterFloatVar(store, ident, varFloat, node, initChild, table, outputVar);
        break;
      case 9: // float interval
        ident = ((ASTVarDeclItem) node).getIdent();
        validateFloatInterval(ident, "float variable");
        varFloat = new FloatVar(store, ident, lowFloatInterval, highFloatInterval);
        initAndRegisterFloatVar(store, ident, varFloat, node, initChild, table, outputVar);
        break;
      default:
        throw new IllegalArgumentException("Not supported type in parameter; compilation aborted.");
    }
  }

  private void generateIntIntervalVariable(
      Store store, SimpleNode node, int initChild, Tables table, boolean outputVar) {
    String ident = ((ASTVarDeclItem) node).getIdent();
    if (lowInterval > highInterval) {
      throw Store.failException;
    }
    if (CHECK_BOUNDS && (lowInterval < IntDomain.MIN_INT || highInterval > IntDomain.MAX_INT)) {
      throw new ArithmeticException(
          "Bounds for " + ident + ": " + lowInterval + ".." + highInterval + " are too low/high");
    }
    IntVar varInt =
        INTERVAL
            ? new IntVar(store, ident, new IntervalDomain(lowInterval, highInterval))
            : new IntVar(store, ident, lowInterval, highInterval);
    initAndRegisterIntVar(store, ident, varInt, node, initChild, table, outputVar);
  }

  private void generateIntListVariable(
      Store store, SimpleNode node, int initChild, Tables table, boolean outputVar) {
    String ident = ((ASTVarDeclItem) node).getIdent();
    IntVar varInt = new IntVar(store, ident);
    for (Integer e : intList) {
      int element = e;
      if (CHECK_BOUNDS && (element < IntDomain.MIN_INT || element > IntDomain.MAX_INT)) {
        throw new ArithmeticException(
            "Domain value for " + ident + " is too high/low (" + element + ")");
      }
      varInt.addDom(element, element);
    }
    initAndRegisterIntVar(store, ident, varInt, node, initChild, table, outputVar);
  }

  /**
   * Registers an integer variable in the table, optionally initializes it from the AST node, adds
   * it to search variables, and marks it as output if needed.
   */
  private void initAndRegisterIntVar(
      Store store,
      String ident,
      IntVar var,
      SimpleNode node,
      int initChild,
      Tables table,
      boolean outputVar) {
    table.addVariable(ident, var);
    if (initChild < node.jjtGetNumChildren()) {
      if (constant_int(node, initChild)) {
        int initVal = getScalarFlatExpr(node, initChild);
        var.domain.inValue(store.level, var, initVal);
      } else {
        IntVar initVar = getScalarFlatExpr_var(store, node, initChild);
        pose(store, new XeqY(var, initVar));
      }
    }
    table.addSearchVar(var);
    if (outputVar) {
      table.addOutVar(var);
    }
  }

  /**
   * Registers a set variable in the table, optionally initializes it from the AST node, adds it to
   * search variables, and marks it as output if needed.
   */
  private void initAndRegisterSetVar(
      Store store,
      String ident,
      SetVar var,
      SimpleNode node,
      int initChild,
      Tables table,
      boolean outputVar) {
    table.addSetVariable(ident, var);
    if (initChild < node.jjtGetNumChildren()) {
      if (constant_set(node, initChild)) {
        IntDomain setValue = getSetLiteral(node, initChild);
        pose(store, new AeqS(var, setValue));
      } else {
        SetVar initSetVar = getSetFlatExpr_var(store, node, initChild);
        pose(store, new AeqB(var, initSetVar));
      }
    }
    table.addSearchSetVar(var);
    if (outputVar) {
      table.addOutVar(var);
    }
    numberSetVariables++;
  }

  /**
   * Registers a float variable in the table, optionally initializes it from the AST node, adds it
   * to search variables, and marks it as output if needed.
   */
  private void initAndRegisterFloatVar(
      Store store,
      String ident,
      FloatVar var,
      SimpleNode node,
      int initChild,
      Tables table,
      boolean outputVar) {
    table.addFloatVariable(ident, var);
    if (initChild < node.jjtGetNumChildren()) {
      if (constant_float(node, initChild)) {
        double initValFloat = getScalarFlatExprFloat(node, initChild);
        var.domain.in(store.level, var, initValFloat, initValFloat);
      } else {
        FloatVar initVarFloat = getScalarFlatExpr_varFloat(store, node, initChild);
        pose(store, new PeqQ(var, initVarFloat));
      }
    }
    table.addSearchFloatVar(var);
    if (outputVar) {
      table.addOutVar(var);
    }
    numberFloatVariables++;
  }

  private int computeArraySize(SimpleNode node) {
    return ((ASTVarDeclItem) node).getHighIndex() - ((ASTVarDeclItem) node).getLowIndex() + 1;
  }

  void generateArray(SimpleNode node, Tables table, Store store) {
    if (((ASTVarDeclItem) node).getKind() == 2) {
      generateArrayVariables(node, table, store);
    } else if (((ASTVarDeclItem) node).getKind() == 3) {
      generateArrayParameters(node, table);
    } else {
      throw new IllegalArgumentException("Internal error");
    }
  }

  void generateArrayParameters(SimpleNode node, Tables table) {

    initContext(table);

    int type = getType(node);

    int initChild = getAnnotations(node, 1);

    String ident = ((ASTVarDeclItem) node).getIdent();

    int size;
    int[] val;
    IntDomain[] setValue;
    switch (type) {
      case 0: // array of int
      case 1: // array of int interval
      case 2: // array of int list
      case 3: // array of bool
        size = computeArraySize(node);
        val = getArrayOfScalarFlatExpr(node, initChild, size);
        table.addIntArray(ident, val);
        break;
      case 4: // array of set int
      case 5: // array of set interval
      case 6: // array of set list
      case 7: // array of bool set
      case 10: // array of range set
        size = computeArraySize(node);
        setValue = getSetLiteralArray(node, initChild, size);
        table.addSetArray(ident, setValue);
        break;
      case 8: // array of float
      case 9:
        size = computeArraySize(node);
        double[] valFloat = getArrayOfScalarFlatExprFloat(node, initChild, size);
        table.addFloatArray(ident, valFloat);
        break;
      default:
        throw new IllegalArgumentException(
            "Not supported type in array parameter; compilation aborted.");
    }
  }

  void generateArrayVariables(SimpleNode node, Tables table, Store store) {

    initContext(table);
    indexBounds = new ArrayList<>();
    boolean outputArray = false;
    OutputArrayAnnotation outArrayAnn = null;

    int type = getType(node);
    int initChild = getArrayAnnotations(node, 1);
    String ident = ((ASTVarDeclItem) node).getIdent();

    if (annotations.contains("output_array")) {
      outputArray = true;
      outArrayAnn = new OutputArrayAnnotation(ident, indexBounds);
    }

    int size;
    IntVar[] varArrayInt;
    FloatVar[] varArrayFloat;
    SetVar[] varArraySet;

    switch (type) {
      case 0: // array of int
        size = computeArraySize(node);
        if (initChild < node.jjtGetNumChildren()) {
          varArrayInt = getScalarFlatExpr_ArrayVar(store, node, initChild);
        } else {
          varArrayInt = new IntVar[size];
          for (int i = 0; i < size; i++) {
            varArrayInt[i] = new IntVar(store, ident + "[" + i + "]", MIN_INT, MAX_INT);
          }
          table.addSearchArray(varArrayInt);
        }
        registerIntArray(table, ident, varArrayInt, outputArray, outArrayAnn);
        break;
      case 1: // array of int interval
        size = computeArraySize(node);
        if (lowInterval > highInterval) {
          throw Store.failException;
        }
        if (initChild < node.jjtGetNumChildren()) {
          varArrayInt = getScalarFlatExpr_ArrayVar(store, node, initChild);
        } else {
          varArrayInt = new IntVar[size];
          for (int i = 0; i < size; i++) {
            if (INTERVAL) {
              varArrayInt[i] =
                  new IntVar(
                      store, ident + "[" + i + "]", new IntervalDomain(lowInterval, highInterval));
            } else {
              varArrayInt[i] = new IntVar(store, ident + "[" + i + "]", lowInterval, highInterval);
            }
          }
          table.addSearchArray(varArrayInt);
        }
        registerIntArray(table, ident, varArrayInt, outputArray, outArrayAnn);
        break;
      case 2: // array of int list
        size = computeArraySize(node);
        if (initChild < node.jjtGetNumChildren()) {
          varArrayInt = getScalarFlatExpr_ArrayVar(store, node, initChild);
        } else {
          varArrayInt = new IntVar[size];
          for (int i = 0; i < size; i++) {
            IntervalDomain dom = new IntervalDomain();
            for (Integer e : intList) {
              dom.unionAdapt(e, e);
            }
            varArrayInt[i] = new IntVar(store, ident + "[" + i + "]", dom);
          }
          table.addSearchArray(varArrayInt);
        }
        registerIntArray(table, ident, varArrayInt, outputArray, outArrayAnn);
        break;
      case 3: // array of bool
        size = computeArraySize(node);
        if (initChild < node.jjtGetNumChildren()) {
          varArrayInt = getScalarFlatExpr_ArrayVar(store, node, initChild);
        } else {
          varArrayInt = new IntVar[size];
          for (int i = 0; i < size; i++) {
            varArrayInt[i] = new BooleanVar(store, ident + "[" + i + "]");
          }
          table.addSearchArray(varArrayInt);
          numberBooleanVariables += size;
        }
        registerIntArray(table, ident, varArrayInt, outputArray, outArrayAnn);
        break;
      case 4: // array of set int
        size = computeArraySize(node);
        if (initChild < node.jjtGetNumChildren()) {
          varArraySet = getSetFlatExpr_ArrayVar(store, node, initChild);
        } else {
          varArraySet = new SetVar[size];
          for (int i = 0; i < size; i++) {
            varArraySet[i] =
                new SetVar(store, ident + "[" + i + "]", new BoundSetDomain(MIN_INT, MAX_INT));
          }
          table.addSearchSetArray(varArraySet);
          numberSetVariables += size;
        }
        registerSetArray(table, ident, varArraySet, outputArray, outArrayAnn);
        break;
      case 5: // array of set interval
        size = computeArraySize(node);
        if (initChild < node.jjtGetNumChildren()) {
          varArraySet = getSetFlatExpr_ArrayVar(store, node, initChild);
        } else {
          varArraySet = new SetVar[size];
          for (int i = 0; i < size; i++) {
            if (lowInterval > highInterval) {
              varArraySet[i] = new SetVar(store, ident + "[" + i + "]", new BoundSetDomain());
            } else {
              varArraySet[i] =
                  new SetVar(
                      store,
                      ident + "[" + i + "]",
                      new BoundSetDomain(
                          new IntervalDomain(), new IntervalDomain(lowInterval, highInterval)));
            }
          }
          table.addSearchSetArray(varArraySet);
          numberSetVariables += size;
        }
        registerSetArray(table, ident, varArraySet, outputArray, outArrayAnn);
        break;
      case 6: // array of set list
        size = computeArraySize(node);
        if (initChild < node.jjtGetNumChildren()) {
          varArraySet = getSetFlatExpr_ArrayVar(store, node, initChild);
        } else {
          varArraySet = new SetVar[size];
          for (int i = 0; i < size; i++) {
            IntDomain sd = new IntervalDomain();
            for (Integer e : intList) {
              sd.unionAdapt(e, e);
            }
            varArraySet[i] =
                new SetVar(
                    store, ident + "[" + i + "]", new BoundSetDomain(new IntervalDomain(), sd));
          }
          table.addSearchSetArray(varArraySet);
          numberSetVariables += size;
        }
        registerSetArray(table, ident, varArraySet, outputArray, outArrayAnn);
        break;
      case 7: // array of bool set
        size = computeArraySize(node);
        if (initChild < node.jjtGetNumChildren()) {
          varArraySet = getSetFlatExpr_ArrayVar(store, node, initChild);
        } else {
          varArraySet = new SetVar[size];
          for (int i = 0; i < size; i++) {
            varArraySet[i] = new SetVar(store, ident + "[" + i + "]", new BoundSetDomain(0, 1));
          }
          table.addSearchSetArray(varArraySet);
          numberSetVariables += size;
        }
        registerSetArray(table, ident, varArraySet, outputArray, outArrayAnn);
        break;
      case 10: // array of range set
        size = computeArraySize(node);
        if (initChild < node.jjtGetNumChildren()) {
          varArraySet = getSetFlatExpr_ArrayVar(store, node, initChild);
        } else {
          varArraySet = new SetVar[size];
          for (int i = 0; i < size; i++) {
            varArraySet[i] =
                new SetVar(
                    store,
                    ident + "[" + i + "]",
                    new BoundSetDomain(new IntervalDomain(), rangeDomain));
          }
          table.addSearchSetArray(varArraySet);
          numberSetVariables += size;
        }
        registerSetArray(table, ident, varArraySet, outputArray, outArrayAnn);
        break;
      case 8: // array of float
        size = computeArraySize(node);
        if (initChild < node.jjtGetNumChildren()) {
          varArrayFloat = getScalarFlatExpr_ArrayVarFloat(store, node, initChild);
        } else {
          varArrayFloat = new FloatVar[size];
          for (int i = 0; i < size; i++) {
            varArrayFloat[i] = new FloatVar(store, ident + "[" + i + "]", MIN_FLOAT, MAX_FLOAT);
          }
          table.addSearchFloatArray(varArrayFloat);
          numberFloatVariables += size;
        }
        registerFloatArray(table, ident, varArrayFloat, outputArray, outArrayAnn);
        break;
      case 9: // array of float interval
        size = computeArraySize(node);
        validateFloatInterval(ident, "array float variable");
        if (initChild < node.jjtGetNumChildren()) {
          varArrayFloat = getScalarFlatExpr_ArrayVarFloat(store, node, initChild);
        } else {
          varArrayFloat = new FloatVar[size];
          for (int i = 0; i < size; i++) {
            varArrayFloat[i] =
                new FloatVar(store, ident + "[" + i + "]", lowFloatInterval, highFloatInterval);
          }
          table.addSearchFloatArray(varArrayFloat);
          numberFloatVariables += size;
        }
        registerFloatArray(table, ident, varArrayFloat, outputArray, outArrayAnn);
        break;
      default:
        throw new IllegalArgumentException(
            "Not supported type in array parameter; compilation aborted.");
    }
  }

  private void registerIntArray(
      Tables table,
      String ident,
      IntVar[] array,
      boolean outputArray,
      OutputArrayAnnotation outArrayAnn) {
    table.addVariableArray(ident, array);
    registerOutputArray(table, outputArray, outArrayAnn, array);
  }

  private void registerSetArray(
      Tables table,
      String ident,
      SetVar[] array,
      boolean outputArray,
      OutputArrayAnnotation outArrayAnn) {
    table.addSetVariableArray(ident, array);
    registerOutputArray(table, outputArray, outArrayAnn, array);
  }

  private void registerFloatArray(
      Tables table,
      String ident,
      FloatVar[] array,
      boolean outputArray,
      OutputArrayAnnotation outArrayAnn) {
    table.addVariableFloatArray(ident, array);
    registerOutputArray(table, outputArray, outArrayAnn, array);
  }

  private void registerOutputArray(
      Tables table, boolean outputArray, OutputArrayAnnotation outArrayAnn, Var[] array) {
    if (outputArray) {
      outArrayAnn.setArray(array);
      table.addOutArray(outArrayAnn);
    }
  }

  // 0 - int; 1 - int interval; 2 - int list; 3 - bool;
  // 4 - set int; 5 - set interval; 6 - set list; 7- bool set;
  // 8 - float; 9 - float interval;
  // 10- range set {|1..n, m, ...|}
  int getType(SimpleNode node) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(0);
    if (child.getId() == JJTINTTIEXPRTAIL) {
      return getTypeFromIntTail((ASTIntTiExprTail) child);
    }
    if (child.getId() == JJTBOOLTIEXPRTAIL) {
      return 3;
    }
    if (child.getId() == JJTSETTIEXPRTAIL) {
      return getTypeFromSetTail(child);
    }
    if (child.getId() == JJTFLOATTIEXPRTAIL) {
      return getTypeFromFloatTail((ASTFloatTiExprTail) child);
    }
    return -1;
  }

  private int getTypeFromIntTail(ASTIntTiExprTail child) {
    int intType = child.getType();
    switch (intType) {
      case 0:
        break;
      case 1:
        extractIntInterval(child);
        break;
      case 2:
        extractIntList((ASTIntLiterals) child.jjtGetChild(0));
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
    return intType;
  }

  private int getTypeFromSetTail(SimpleNode child) {
    SimpleNode grand_child = (SimpleNode) child.jjtGetChild(0);
    if (grand_child.getId() == JJTINTTIEXPRTAIL) {
      return getSetTypeFromIntTail(grand_child);
    }
    if (grand_child.getId() == JJTBOOLTIEXPRTAIL) {
      return 7;
    }
    return -1;
  }

  private int getSetTypeFromIntTail(SimpleNode grandChild) {
    int intType = ((ASTIntTiExprTail) grandChild).getType();
    switch (intType) {
      case 0:
        break;
      case 1:
        extractIntInterval((ASTIntTiExprTail) grandChild);
        break;
      case 2:
        extractIntList((ASTIntLiterals) grandChild.jjtGetChild(0));
        break;
      case 3: // range set
        rangeDomain = new IntervalDomain();
        int n = grandChild.jjtGetNumChildren();
        for (int i = 0; i < n; i++) {
          SimpleNode setElement = (SimpleNode) grandChild.jjtGetChild(i);
          if (setElement.getId() == JJTSETELEMENT) {
            SimpleNode e1 = (SimpleNode) setElement.jjtGetChild(0);
            if (e1.getId() == JJTSCALARFLATEXPR) {
              rangeDomain.unionAdapt(((ASTScalarFlatExpr) e1).getInt());
            } else if (e1.getId() == JJTINTFLATEXPR) {
              SimpleNode e2 = (SimpleNode) setElement.jjtGetChild(1);
              rangeDomain.unionAdapt(
                  new Interval(((ASTIntFlatExpr) e1).getInt(), ((ASTIntFlatExpr) e2).getInt()));
            }
          }
        }
        return 10;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
    return intType + 4;
  }

  private int getTypeFromFloatTail(ASTFloatTiExprTail child) {
    int doubleType = child.getType();
    switch (doubleType) {
      case 0:
        break;
      case 1:
        lowFloatInterval = child.getLow();
        highFloatInterval = child.getHigh();
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
    return doubleType + 8;
  }

  /**
   * Helper method to process annotation nodes.
   *
   * @param child the annotation node
   * @return true if annotation was processed, false otherwise
   */
  private boolean processAnnotation(SimpleNode child) {
    SimpleNode grandchild = (SimpleNode) child.jjtGetChild(0);
    if (grandchild.getId() == JJTANNEXPR) {
      annotations.add(parseAnnExpr(grandchild, 0));
      return true;
    }
    return false;
  }

  int getAnnotations(SimpleNode node, int i) {
    int j = i;
    int count = node.jjtGetNumChildren();
    if (j < count) {
      SimpleNode child = (SimpleNode) node.jjtGetChild(j);
      while (j < count && child.getId() == JJTANNOTATION) {
        processAnnotation(child);

        j++;
        if (j < count) {
          child = (SimpleNode) node.jjtGetChild(j);
        }
      }
    }

    return j;
  }

  String parseAnnExpr(SimpleNode node, int i) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(i);
    if (child.getId() == JJTSCALARFLATEXPR) {
      // string & float;
      return switch (((ASTScalarFlatExpr) child).getType()) {
        case 2 -> // ident
            ((ASTScalarFlatExpr) child).getIdent();
        default ->
            throw new IllegalArgumentException(
                "Not supported scalar in annotation; compilation aborted.");
      };
    } else {
      throw new IllegalArgumentException("Not supported annotation type; compilation aborted.");
    }
  }

  int getArrayAnnotations(SimpleNode node, int i) {

    int j = i;
    int count = node.jjtGetNumChildren();

    if (j < count) {
      SimpleNode child = (SimpleNode) node.jjtGetChild(j);
      while (j < count && child.getId() == JJTANNOTATION) {
        String id = ((ASTAnnotation) child).getAnnId();

        if ("output_array".equals(id)) {
          annotations.add(id);

          child = (SimpleNode) child.jjtGetChild(0);

          int noAnnotations = child.jjtGetNumChildren();
          for (int nc = 0; nc < noAnnotations; nc++) {

            SimpleNode nchild = (SimpleNode) child.jjtGetChild(nc);
            int no = nchild.jjtGetNumChildren();

            if (no > 1 || ((SimpleNode) nchild.jjtGetChild(0)).getId() != JJTANNEXPR) {
              throw new IllegalArgumentException(
                  "More than one annotation expression in output_array annotation; execution aborted");
            } else {
              SimpleNode grandchild = (SimpleNode) nchild.jjtGetChild(0);
              int number = grandchild.jjtGetNumChildren();
              if (number == 1) {
                SimpleNode setLiteral = (SimpleNode) grandchild.jjtGetChild(0);
                if (setLiteral.getId() == JJTSETLITERAL) {

                  if (((ASTSetLiteral) setLiteral).getType() == 0) { // interval
                    int s_n = setLiteral.jjtGetNumChildren();
                    if (s_n == 2) {
                      int low = ((ASTIntFlatExpr) setLiteral.jjtGetChild(0)).getInt();
                      int high = ((ASTIntFlatExpr) setLiteral.jjtGetChild(1)).getInt();
                      IntDomain indexes = new IntervalDomain(low, high);
                      indexBounds.add(indexes);
                    } else {
                      throw new IllegalArgumentException(
                          "Unexpected set literal in output_array annotation; execution aborted");
                    }
                  } else if (((ASTSetLiteral) setLiteral).getType() == 1) { // list
                    int s_n = setLiteral.jjtGetNumChildren();
                    IntDomain indexes = new IntervalDomain();
                    for (int k = 0; k < s_n; k++) {
                      int el = ((ASTScalarFlatExpr) setLiteral.jjtGetChild(k)).getInt();
                      indexes.unionAdapt(el);
                    }
                    indexBounds.add(indexes);
                  } else {
                    throw new IllegalArgumentException(
                        "Unexpected set literal in output_array annotation; execution aborted");
                  }
                } else {
                  throw new IllegalArgumentException(
                      "Wrong expression in output_array annotation; execution aborted");
                }
              }
            }
          }
        } else {
          // simple annotation id
          annotations.add(parseAnnExpr((SimpleNode) child.jjtGetChild(0), 0));
        }
        j++;
        if (j < count) {
          child = (SimpleNode) node.jjtGetChild(j);
        }
      }
    }

    return j;
  }

  boolean constant_int(SimpleNode node, int i) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(i);
    if (child.getId() == JJTSCALARFLATEXPR) {
      // string & float;
      return switch (((ASTScalarFlatExpr) child).getType()) { // int
        case 0, 1 -> // bool
            true;
        case 2 -> {
          Integer n = dictionary.checkInt(((ASTScalarFlatExpr) child).getIdent());
          yield n != null;
        }
        case 3 -> {
          int[] an = dictionary.getIntArray(((ASTScalarFlatExpr) child).getIdent());
          yield an != null;
        }
        default ->
            throw new IllegalArgumentException(
                "Not supported scalar in parameter; compilation aborted.");
      };
    } else {
      throw new IllegalArgumentException(
          "Not supported parameter assignment; compilation aborted.");
    }
  }

  boolean constant_float(SimpleNode node, int i) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(i);

    if (child.getId() == JJTSCALARFLATEXPR) {
      // string & float;
      return switch (((ASTScalarFlatExpr) child).getType()) {
        case 2 -> {
          Double n = dictionary.checkFloat(((ASTScalarFlatExpr) child).getIdent());
          yield n != null;
        }
        case 3 -> {
          double[] an = dictionary.getFloatArray(((ASTScalarFlatExpr) child).getIdent());
          yield an != null;
        }
        case 5 -> // float
            true;
        default ->
            throw new IllegalArgumentException(
                "Not supported scalar in parameter; compilation aborted.");
      };
    } else {
      throw new IllegalArgumentException(
          "Not supported parameter assignment; compilation aborted.");
    }
  }

  boolean constant_set(SimpleNode node, int i) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(i);
    if (child.getId() == JJTSETLITERAL) { // SCALARFLATEXPR) {
      // string & float;
      return switch (((ASTSetLiteral) child).getType()) { // interval
        // list
        case 0, 1, 2 -> // range set
            true;
        default ->
            throw new IllegalArgumentException(
                "Not supported scalar in parameter; compilation aborted.");
      };
    } else if (child.getId() == JJTSCALARFLATEXPR) {
      // int, bool, string & float;
      return switch (((ASTScalarFlatExpr) child).getType()) {
        case 2 -> {
          IntDomain n = dictionary.getSet(((ASTScalarFlatExpr) child).getIdent());
          yield n != null;
        }
        case 3 -> {
          IntDomain[] an = dictionary.getSetArray(((ASTScalarFlatExpr) child).getIdent());
          yield an != null;
        }
        default ->
            throw new IllegalArgumentException(
                "Not supported scalar in parameter; compilation aborted.");
      };
    } else {
      throw new IllegalArgumentException(
          "Not supported parameter assignment; compilation aborted.");
    }
  }

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

  double getScalarFlatExprFloat(SimpleNode node, int i) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(i);

    if (child.getId() == JJTSCALARFLATEXPR) {
      // string & float;
      return switch (((ASTScalarFlatExpr) child).getType()) {
        case 5 -> // float
            ((ASTScalarFlatExpr) child).getFloat();
        default ->
            throw new IllegalArgumentException(
                "Not supported scalar in parameter; compilation aborted.");
      };
    } else {
      throw new IllegalArgumentException(
          "Not supported parameter assignment; compilation aborted.");
    }
  }

  IntVar[] getScalarFlatExpr_ArrayVar(Store store, SimpleNode node, int index) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(index);
    if (child.getId() == JJTARRAYLITERAL) {
      int count = child.jjtGetNumChildren();
      IntVar[] av = new IntVar[count];
      for (int i = 0; i < count; i++) {
        av[i] = getScalarFlatExpr_var(store, child, i);
      }
      return av;
    } else {
      throw new IllegalArgumentException(
          "Expeceted array literal, found " + child.getId() + " ; compilation aborted.");
    }
  }

  FloatVar[] getScalarFlatExpr_ArrayVarFloat(Store store, SimpleNode node, int index) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(index);
    if (child.getId() == JJTARRAYLITERAL) {
      int count = child.jjtGetNumChildren();
      FloatVar[] av = new FloatVar[count];
      for (int i = 0; i < count; i++) {
        av[i] = getScalarFlatExpr_varFloat(store, child, i);
      }
      return av;
    } else {
      throw new IllegalArgumentException(
          "Expeceted array literal, found " + child.getId() + " ; compilation aborted.");
    }
  }

  IntVar getScalarFlatExpr_var(Store store, SimpleNode node, int i) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(i);
    if (child.getId() == JJTSCALARFLATEXPR) {
      switch (((ASTScalarFlatExpr) child).getType()) {
        case 0: // int
          int val = ((ASTScalarFlatExpr) child).getInt();
          return dictionary.getConstant(val); // new IntVar(store, val, val);
        case 1: // bool
          val = ((ASTScalarFlatExpr) child).getInt();
          return dictionary.getConstantBoolean(val);
        case 2: // ident
          IntVar v = dictionary.getVariable(((ASTScalarFlatExpr) child).getIdent());
          if (v != null) {
            return v;
          } else {
            Integer n = dictionary.getInt(((ASTScalarFlatExpr) child).getIdent());
            return dictionary.getConstant(n); // new IntVar(store, n.intValue(), n.intValue());
          }
        case 3: // array acces
          IntVar avar =
              dictionary
                  .getVariableArray(((ASTScalarFlatExpr) child).getIdent())[
                  ((ASTScalarFlatExpr) child).getInt()];
          if (avar != null) {
            return avar;
          } else {
            Integer an =
                dictionary
                    .getIntArray(((ASTScalarFlatExpr) child).getIdent())[
                    ((ASTScalarFlatExpr) child).getInt()];
            return dictionary.getConstant(an); // new IntVar(store, an.intValue(), an.intValue());
          }
        default: // string & float;
          throw new IllegalArgumentException(
              "Not supported scalar in parameter; compilation aborted.");
      }
    } else {
      throw new IllegalArgumentException(
          "Not supported parameter assignment; compilation aborted.");
    }
  }

  FloatVar getScalarFlatExpr_varFloat(Store store, SimpleNode node, int i) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(i);
    if (child.getId() == JJTSCALARFLATEXPR) {
      switch (((ASTScalarFlatExpr) child).getType()) {
        case 2: // ident
          FloatVar v = dictionary.getFloatVariable(((ASTScalarFlatExpr) child).getIdent());
          if (v != null) {
            return v;
          } else {
            Double n = dictionary.getFloat(((ASTScalarFlatExpr) child).getIdent());
            return dictionary.getFloatConstant(
                n); // new FloatVar(store, n.doubleValue(), n.doubleValue());
          }
        case 3: // array acces
          FloatVar avar =
              dictionary
                  .getVariableFloatArray(((ASTScalarFlatExpr) child).getIdent())[
                  ((ASTScalarFlatExpr) child).getInt()];
          if (avar != null) {
            return avar;
          } else {
            Double an =
                dictionary
                    .getFloatArray(((ASTScalarFlatExpr) child).getIdent())[
                    ((ASTScalarFlatExpr) child).getInt()];
            return dictionary.getFloatConstant(
                an); // new FloatVar(store, an.doubleValue(), an.doubleValue());
          }
        case 5: // float
          return dictionary.getFloatConstant(((ASTScalarFlatExpr) child).getFloat());
        default: // string & float;
          throw new IllegalArgumentException(
              "Not supported scalar in parameter; compilation aborted.");
      }
    } else {
      throw new IllegalArgumentException(
          "Not supported parameter assignment; compilation aborted.");
    }
  }

  SetVar[] getSetFlatExpr_ArrayVar(Store store, SimpleNode node, int index) {

    SimpleNode child = (SimpleNode) node.jjtGetChild(index);

    if (child.getId() == JJTARRAYLITERAL) {
      int count = child.jjtGetNumChildren();
      SetVar[] av = new SetVar[count];
      for (int i = 0; i < count; i++) {
        av[i] = getSetFlatExpr_var(store, child, i);
      }
      return av;
    } else {
      throw new IllegalArgumentException(
          "Expeceted array literal, found " + child.getId() + " ; compilation aborted.");
    }
  }

  SetVar getSetFlatExpr_var(Store store, SimpleNode node, int i) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(i);
    if (child.getId() == JJTSCALARFLATEXPR) {
      return getSetVarFromScalarFlatExpr(store, (ASTScalarFlatExpr) child);
    }
    if (child.getId() == JJTSETLITERAL) {
      IntDomain s = getSetLiteral(node, i);
      return new SetVar(store, new BoundSetDomain(s, s));
    }
    throw new IllegalArgumentException(
        "Not supported parameter assignment "
            + ((ASTScalarFlatExpr) child).getIdent()
            + "; compilation aborted.");
  }

  private SetVar getSetVarFromScalarFlatExpr(Store store, ASTScalarFlatExpr child) {
    switch (child.getType()) {
      case 2: // ident
        SetVar v = dictionary.getSetVariable(child.getIdent());
        if (v != null) {
          return v;
        }
        IntDomain n = dictionary.getSet(child.getIdent());
        if (n != null) {
          return new SetVar(store, new BoundSetDomain(n, n));
        }
        break;
      case 3: // array access
        SetVar avar = dictionary.getSetVariableArray(child.getIdent())[child.getInt()];
        if (avar != null) {
          return avar;
        }
        IntDomain an = dictionary.getSetArray(child.getIdent())[child.getInt()];
        if (an != null) {
          return new SetVar(store, new BoundSetDomain(an, an));
        }
        break;
      default:
        throw new IllegalArgumentException(
            "Not supported scalar in parameter " + child.getIdent() + "; compilation aborted.");
    }
    throw new IllegalArgumentException(
        "Not supported parameter assignment " + child.getIdent() + "; compilation aborted.");
  }

  int[] getArrayOfScalarFlatExpr(SimpleNode node, int index, int size) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(index);
    int count = child.jjtGetNumChildren();
    if (count == size) {
      int[] aa = new int[size];
      for (int i = 0; i < count; i++) {
        aa[i] = getScalarFlatExpr(child, i);
      }
      return aa;
    } else {
      throw new IllegalArgumentException(
          "Different size declaration and intiallization of int array; compilation aborted.");
    }
  }

  double[] getArrayOfScalarFlatExprFloat(SimpleNode node, int index, int size) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(index);
    int count = child.jjtGetNumChildren();
    if (count == size) {
      double[] aa = new double[size];
      for (int i = 0; i < count; i++) {
        aa[i] = getScalarFlatExprFloat(child, i);
      }
      return aa;
    } else {
      throw new IllegalArgumentException(
          "Different size declaration and intiallization of float array; compilation aborted.");
    }
  }

  IntDomain getSetLiteral(SimpleNode node, int index) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(index);
    if (child.getId() == JJTSETLITERAL) {
      return getSetLiteralFromSetLiteralNode((ASTSetLiteral) child);
    }
    if (child.getId() == JJTSCALARFLATEXPR) {
      return getSetLiteralFromScalarExpr((ASTScalarFlatExpr) child);
    }
    return new IntervalDomain();
  }

  private IntDomain getSetLiteralFromSetLiteralNode(ASTSetLiteral child) {
    switch (child.getType()) {
      case 0: // interval
        SimpleNode grand_child_1 = (SimpleNode) child.jjtGetChild(0);
        SimpleNode grand_child_2 = (SimpleNode) child.jjtGetChild(1);
        if (grand_child_1.getId() == JJTINTFLATEXPR && grand_child_2.getId() == JJTINTFLATEXPR) {
          int i1 = ((ASTIntFlatExpr) grand_child_1).getInt();
          int i2 = ((ASTIntFlatExpr) grand_child_2).getInt();
          return i1 > i2 ? new IntervalDomain() : new IntervalDomain(i1, i2);
        }
        break;
      case 1: // list
        IntDomain s = new IntervalDomain();
        int count = child.jjtGetNumChildren();
        for (int i = 0; i < count; i++) {
          s.unionAdapt(getScalarFlatExpr(child, i));
        }
        return s;
      case 2: // range
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
      default:
        throw new IllegalArgumentException("Set type not supported; compilation aborted.");
    }
    return new IntervalDomain();
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

  IntDomain[] getSetLiteralArray(SimpleNode node, int index, int size) {
    IntDomain[] s = new IntDomain[size];
    int arrayIndex = 0;

    SimpleNode child = (SimpleNode) node.jjtGetChild(index);
    if (child.getId() == JJTARRAYLITERAL) {
      int count = child.jjtGetNumChildren();
      if (count == size) {
        for (int i = 0; i < count; i++) {
          s[arrayIndex++] = getSetLiteral(child, i);
        }
      } else {
        throw new IllegalArgumentException(
            "Different array sizes in specification and initialization; compilation aborted.");
      }
    }
    return s;
  }

  boolean ground(Var v) {

    return v.singleton();
  }

  void pose(Store store, Constraint c) throws FailException {

    store.imposeWithConsistency(c);

    if (options.debug()) {
      IO.println("% " + c);
    }
  }
}
