/*
 * ObjectiveDetector.java
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

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.fz.ASTAnnExpr;
import org.jacop.fz.ASTAnnotation;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.presolve.ObjectivePresolve;

/**
 * It reads the facts objective presolve needs from the constraint items of a model: the linear
 * equations ({@code int_lin_eq}, {@code bool_lin_eq}) with their {@code defines_var} annotations,
 * the value literals ({@code int_eq_reif} of a variable and a constant), the counts of a constant
 * ({@code jacop_count}), the elements of constant arrays, the disjunctions ({@code array_bool_or},
 * {@code bool_clause_reif} without negative literals), the all-different constraints and the
 * equalities ({@code bool2int}, {@code bool_eq}). Variables are those of the loaded store; see
 * {@link ObjectivePresolve}.
 *
 * <p>Setting the system property {@code org.jacop.fz.objectivePresolve} to false turns objective
 * presolve off.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class ObjectiveDetector implements ParserTreeConstants {

  private static final IntVar[] NONE = new IntVar[0];

  private final Support support;

  private final Set<Var> removed;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public ObjectiveDetector(Support support) {
    this(support, Set.of());
  }

  /**
   * It creates a detector that leaves out the constraints over variables the front end removed.
   *
   * <p>A pass such as affine folding replaces the definition of a variable and leaves the variable
   * in no constraint. The replaced item is still in the parsed model, but it no longer holds in the
   * store, so no fact may be drawn from it.
   *
   * @param support the support of the FlatZinc front end.
   * @param removed the variables the front end left unconstrained.
   */
  public ObjectiveDetector(Support support, Collection<? extends Var> removed) {
    this.support = support;
    Set<Var> set = Collections.newSetFromMap(new IdentityHashMap<>());
    set.addAll(removed);
    this.removed = set;
  }

  /**
   * It tells if objective presolve is on.
   *
   * @return false if the system property org.jacop.fz.objectivePresolve is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.objectivePresolve"));
  }

  /**
   * It collects the equations and value literals of the model for an objective.
   *
   * @param astTree the root of the parsed model.
   * @param objective the objective variable.
   * @param minimize true when the objective is minimised.
   * @return the objective presolve holding the facts.
   */
  public ObjectivePresolve collect(SimpleNode astTree, IntVar objective, boolean minimize) {
    ObjectivePresolve presolve = new ObjectivePresolve(objective, minimize);
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) node.jjtGetChild(j);
          if (item.jjtGetChild(0) instanceof ASTConstElem c) {
            collect(presolve, item, c);
          }
        }
      }
    }
    return presolve;
  }

  private void collect(ObjectivePresolve presolve, SimpleNode item, ASTConstElem node) {
    switch (node.getName()) {
      case "int_lin_eq", "bool_lin_eq" -> {
        int[] a = support.getIntArray(child(node, 0));
        IntVar[] x = support.getVarArray(child(node, 1));
        if (a == null || a.length != x.length) {
          return;
        }
        IntVar rhs = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (gone(x, rhs)) {
          return;
        }
        if (rhs.singleton()) {
          presolve.addEquation(x, a, rhs.value(), definedVar(item));
        } else {
          // bool_lin_eq has a variable right-hand side: sum(a * x) - rhs = 0
          IntVar[] vars = Arrays.copyOf(x, x.length + 1);
          int[] coefs = Arrays.copyOf(a, a.length + 1);
          vars[x.length] = rhs;
          coefs[a.length] = -1;
          presolve.addEquation(vars, coefs, 0, definedVar(item));
        }
      }
      case "int_lin_le", "bool_lin_le" -> {
        int[] a = support.getIntArray(child(node, 0));
        IntVar[] x = support.getVarArray(child(node, 1));
        IntVar rhs = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (a != null
            && a.length == x.length
            && rhs.singleton()
            && rhs.value() == 1
            && unit(a)
            && !gone(x)) {
          presolve.addAtMostOne(x);
        }
      }
      case "jacop_count" -> {
        IntVar[] x = support.getVarArray(child(node, 0));
        int value = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
        IntVar n = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (!gone(x, n)) {
          presolve.addCount(x, value, n);
        }
      }
      case "int_eq_reif" -> {
        IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (gone(NONE, x, y, b)) {
          return;
        }
        if (y.singleton() && !x.singleton()) {
          presolve.addValueLiteral(x, y.value(), b);
        } else if (x.singleton() && !y.singleton()) {
          presolve.addValueLiteral(y, x.value(), b);
        }
      }
      case "bool2int", "bool_eq" -> {
        IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        if (!gone(NONE, x, y)) {
          presolve.addEquality(x, y);
        }
      }
      case "array_bool_or" -> or(presolve, node, 1);
      case "bool_clause_reif" -> {
        if (support.getVarArray(child(node, 1)).length == 0) {
          or(presolve, node, 2);
        }
      }
      case "jacop_alldiff", "jacop_alldistinct" -> {
        IntVar[] x = support.getVarArray(child(node, 0));
        if (!gone(x)) {
          presolve.addAllDifferent(x);
        }
      }
      case "array_int_element" -> element(presolve, node, support.getIntArray(child(node, 1)), 1);
      case "array_var_int_element" -> element(presolve, node, constants(child(node, 1)), 1);
      case "jacop_array_var_int_element_nonshifted" ->
          element(
              presolve,
              node,
              constants(child(node, 1)),
              support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      default -> {
        // not used by objective presolve
      }
    }
  }

  private void or(ObjectivePresolve presolve, ASTConstElem node, int result) {
    IntVar r = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(result));
    IntVar[] x = support.getVarArray(child(node, 0));
    if (!gone(x, r)) {
      presolve.addOr(r, x);
    }
  }

  // true when the front end removed one of the variables, so their constraint is not posted
  private boolean gone(IntVar[] list, IntVar... others) {
    if (removed.isEmpty()) {
      return false;
    }
    for (IntVar v : list) {
      if (removed.contains(v)) {
        return true;
      }
    }
    for (IntVar v : others) {
      if (removed.contains(v)) {
        return true;
      }
    }
    return false;
  }

  private static boolean unit(int[] a) {
    for (int c : a) {
      if (c != 1) {
        return false;
      }
    }
    return a.length > 1;
  }

  private void element(ObjectivePresolve presolve, ASTConstElem node, int[] array, int firstIndex) {
    if (array == null || array.length == 0) {
      return;
    }
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar value = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (gone(NONE, index, value)) {
      return;
    }
    presolve.addElement(index, array, firstIndex, value);
  }

  // the values of an array of constants, or an empty array if one of them is a variable
  private int[] constants(SimpleNode node) {
    IntVar[] vars = support.getVarArray(node);
    int[] values = new int[vars.length];
    for (int i = 0; i < vars.length; i++) {
      if (!vars[i].singleton()) {
        return new int[0];
      }
      values[i] = vars[i].value();
    }
    return values;
  }

  private IntVar definedVar(SimpleNode item) {
    for (int i = 1; i < item.jjtGetNumChildren(); i++) {
      if (item.jjtGetChild(i) instanceof ASTAnnotation ann
          && "defines_var".equals(ann.getAnnId())
          && ann.jjtGetNumChildren() > 0
          && ann.jjtGetChild(0).jjtGetNumChildren() > 0
          && ann.jjtGetChild(0).jjtGetChild(0) instanceof ASTAnnExpr expr
          && expr.jjtGetChild(0) instanceof ASTScalarFlatExpr e) {
        Var v = e.getType() == 2 || e.getType() == 3 ? support.getVariable(e) : null;
        return v instanceof IntVar iv ? iv : null;
      }
    }
    return null;
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }
}
