/*
 * Constraints.java
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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.constraints.AlldifferentDetector;
import org.jacop.fz.constraints.BalanceDetector;
import org.jacop.fz.constraints.CardinalityDetector;
import org.jacop.fz.constraints.CircuitCostDetector;
import org.jacop.fz.constraints.ConstraintFncs;
import org.jacop.fz.constraints.DisjunctiveCliqueDetector;
import org.jacop.fz.constraints.IncreasingDetector;
import org.jacop.fz.constraints.KnapsackDetector;
import org.jacop.fz.constraints.LinearRelaxationCheck;
import org.jacop.fz.constraints.PrecedenceDetector;
import org.jacop.fz.constraints.StockingCostDetector;
import org.jacop.fz.constraints.Support;
import org.jacop.fz.constraints.WeightedCompletionDetector;
import org.jacop.satwrapper.SatTranslation;

/**
 * The part of the parser responsible for parsing constraints.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class Constraints implements ParserTreeConstants {

  static final int EQ = 0;
  static final int NE = 1;
  static final int LT = 2;
  static final int GT = 3;
  static final int LE = 4;
  static final int GE = 5;
  final ConstraintFncs cf; // = new org.jacop.fz.constraints.ConstraintFncs(store, dict, sat);
  final Tables dictionary;
  final Store store;
  // ============ SAT solver interface ==============
  final float satThreshold = 1.0f; // 1.0 pure SAT problem, 0.85 good heuristic ;)
  final SatTranslation sat;
  final Support support;
  String p;

  // constraint generators by name; getMethod scans every public method on each call
  final Map<String, java.lang.reflect.Method> generators = new HashMap<>();
  boolean debug;
  long boolClauses;
  long noConstraints;
  long bool2Int;

  /**
   * It creates an object to parse the constraint part of the flatzinc file.
   *
   * @param store the constraint store in which the constraints are being created.
   * @param dict the current dictionary (tables of all variables and constants)
   */
  public Constraints(Store store, Tables dict) {
    this.store = store;
    this.dictionary = dict;

    sat = new SatTranslation(store);
    // impose SAT-solver
    sat.impose();

    support = new Support(store, dict, sat);

    cf = new ConstraintFncs(support);
  }

  void setOptions(Options options) {
    support.options = options;
    debug = options.debug();
    if (options.lcg() || options.useSat() && options.presolve() != Options.Presolve.OFF) {
      // Boolean constraints become clauses of the LCG solver, or of the SAT solver of -sat once
      // presolve has preprocessed them; Solve posts them
      sat.collectClauses();
    }
  }

  void generateAllConstraints(SimpleNode astTree) throws Throwable {

    if (support.options.debug()) {
      FzConsole.println(
          "% bool constraints = "
              + boolClauses
              + " of "
              + (noConstraints - bool2Int)
              + " p = "
              + (float) boolClauses / (float) (noConstraints - bool2Int));
    }

    if ((float) boolClauses / (float) (noConstraints - bool2Int) >= satThreshold) {
      support.options.setSat();
    }

    sat.setDebug(debug);

    support.objective = objective(astTree);

    // disequalities that are part of a detected all-different constraint
    Set<SimpleNode> replaced = Set.of();
    if (AlldifferentDetector.enabled()) {
      AlldifferentDetector alldifferent = new AlldifferentDetector(support);
      alldifferent.detect(astTree);
      replaced = alldifferent.replaced();
    }

    IncreasingDetector increasing = null;
    if (IncreasingDetector.sumEnabled() || IncreasingDetector.nvalueEnabled()) {
      increasing = new IncreasingDetector(support);
      increasing.scan(astTree);
      if (IncreasingDetector.nvalueEnabled()) {
        Set<SimpleNode> nvalues = increasing.replaceNValues();
        if (!nvalues.isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(nvalues);
        }
      }
    }

    int n = astTree.jjtGetNumChildren();

    for (int i = 0; i < n; i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      // go for ConstraintItems
      if (node.getId() == JJTCONSTRAINTITEMS) {

        int k = node.jjtGetNumChildren();
        for (int j = 0; j < k; j++) {
          if (support.options.timeOutPassed()) {
            throw new ModelTimeOut();
          }
          SimpleNode snode = (SimpleNode) node.jjtGetChild(j);
          if (!replaced.contains(snode.jjtGetChild(0))) {
            generateConstraint(snode);
          }
        }
      }
    }

    cf.poseCounts();
    cf.poseDiffnProjections();

    if (CircuitCostDetector.enabled()) {
      new CircuitCostDetector(support).detect(astTree);
    }

    if (DisjunctiveCliqueDetector.enabled()) {
      new DisjunctiveCliqueDetector(support).detect(astTree);
    }

    // energy precedence when enabled, and the reservoirs
    new PrecedenceDetector(support).detect(astTree);
    if (WeightedCompletionDetector.enabled()) {
      new WeightedCompletionDetector(support).detect(astTree);
    }

    if (CardinalityDetector.enabled()) {
      new CardinalityDetector(support).detect(astTree);
    }

    if (increasing != null && IncreasingDetector.sumEnabled()) {
      increasing.postSums();
    }

    if (BalanceDetector.enabled()) {
      new BalanceDetector(support).detect(astTree);
    }

    if (StockingCostDetector.enabled()) {
      new StockingCostDetector(support).detect(astTree);
    }

    if (KnapsackDetector.enabled()) {
      new KnapsackDetector(support).detect(astTree);
    }

    support.poseDelayedConstraints();

    // to be sure that all constraints queues are empty and the
    // model is consistent; it can happen that search will not
    // find out inconsistency if all variables are ground
    if (!store.consistency()) {
      throw Store.failException;
    }

    if (LinearRelaxationCheck.enabled() && new LinearRelaxationCheck(support).infeasible(astTree)) {
      throw Store.failException;
    }

    if (!support.probeDiffnKHandles()) {
      throw Store.failException;
    }
  }

  // the variable the solve item minimises or maximises, or null
  private IntVar objective(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTMODELEND
          && node.jjtGetChild(0) instanceof ASTSolveItem item
          && item.jjtGetChild(item.jjtGetNumChildren() - 1) instanceof ASTSolveKind kind
          && kind.jjtGetNumChildren() > 0
          && kind.jjtGetChild(0) instanceof ASTSolveExpr expr) {
        return switch (expr.getType()) {
          case 0 -> dictionary.getVariable(expr.getIdent());
          case 1 -> {
            IntVar[] a = dictionary.getVariableArray(expr.getIdent());
            yield a == null ? null : a[expr.getIndex()];
          }
          default -> null;
        };
      }
    }
    return null;
  }

  void generateConstraint(SimpleNode constraintWithAnnotations) throws Throwable {

    // default consistency - bounds
    support.boundsConsistency = true;
    support.domainConsistency = false;
    support.definedVar = null;

    int numberChildren = constraintWithAnnotations.jjtGetNumChildren();
    if (numberChildren > 1) {
      support.parseAnnotations(constraintWithAnnotations);
    }

    SimpleNode node = (SimpleNode) constraintWithAnnotations.jjtGetChild(0);

    // Generate constraint
    if (node.getId() == JJTCONSTELEM) {

      p = ((ASTConstElem) node).getName();

      try {

        java.lang.reflect.Method method = generators.get(p);
        if (method == null) {
          method = cf.getClass().getMethod(p, SimpleNode.class);
          generators.put(p, method);
        }
        method.invoke(cf, node);

      } catch (NoSuchMethodException _) {
        throw new IllegalArgumentException(
            "JaCoP flatzinc back-end: constraint " + p + " is not supported.");
      } catch (IllegalAccessException e) {
        FzConsole.println(e);
      } catch (java.lang.reflect.InvocationTargetException e) {
        Throwable cause = e.getCause();
        if (cause instanceof FailException) {
          // the comment explains an unsatisfiable model; other errors go to stderr
          FzConsole.println("%% problem detected for " + p);
        } else {
          FzConsole.printlnErr("%% problem detected for " + p);
        }
        throw cause;
      }
    }
  }

  void generateAlias(SimpleNode constraintWithAnnotations) {

    SimpleNode node = (SimpleNode) constraintWithAnnotations.jjtGetChild(0);

    if (node.getId() != JJTCONSTELEM) {
      return;
    }

    p = ((ASTConstElem) node).getName();
    noConstraints++;

    if (isBoolClauseConstraint(p)) {
      boolClauses++;
      return;
    }
    if (p.startsWith("bool2int") || p.startsWith("int2bool")) {
      handleBool2IntAlias(node);
      return;
    }
    if (p.startsWith("int_eq_reif")) {
      handleIntEqReif(node);
      return;
    }
    if (p.startsWith("int_eq_imp")) {
      handleIntEqImp(node);
    }
  }

  private boolean isBoolClauseConstraint(String name) {
    return name.startsWith("bool_clause")
        || name.startsWith("bool_not")
        || name.startsWith("bool_eq")
        || name.startsWith("array_bool_or");
  }

  private void handleBool2IntAlias(SimpleNode node) {
    bool2Int++;
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    dictionary.addAlias(v1, v2);
    if (v1.singleton() || v2.singleton()) {
      v1.domain.in(store.level, v1, v2.domain);
      v2.domain.in(store.level, v2, v1.domain);
    }
    if (debug) {
      FzConsole.println("% Alias: " + v1 + " == " + v2);
    }
  }

  private void handleIntEqReif(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);
    IntVar b = support.getVariable(p3);
    IntVarAndValue xv = extractIntVarAndValue(p1, p2);
    if (xv != null) {
      support.addReified(xv.x, xv.v, b);
    }
  }

  private void handleIntEqImp(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);
    IntVar b = support.getVariable(p3);
    IntVarAndValue xv = extractIntVarAndValue(p1, p2);
    if (xv != null) {
      support.addImplied(xv.x, xv.v, b);
    }
  }

  /**
   * Extracts an IntVar and integer value from two scalar expressions. One must be a variable and
   * the other an integer constant.
   *
   * @param p1 first expression
   * @param p2 second expression
   * @return IntVarAndValue if extraction successful, null otherwise
   */
  private IntVarAndValue extractIntVarAndValue(ASTScalarFlatExpr p1, ASTScalarFlatExpr p2) {
    IntVar x;
    int v;

    if (p2.getType() == 0) { // second argument integer
      x = support.getVariable(p1);
      v = support.getInt(p2);
    } else if (p1.getType() == 0) { // first argument integer
      x = support.getVariable(p2);
      v = support.getInt(p1);
    } else { // no integers
      return null;
    }

    return new IntVarAndValue(x, v);
  }

  /** Helper record for IntVar and integer value pair. */
  private record IntVarAndValue(IntVar x, int v) {}
}
