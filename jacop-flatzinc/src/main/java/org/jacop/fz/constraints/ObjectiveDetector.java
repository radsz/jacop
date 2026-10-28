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
 * and the value literals ({@code int_eq_reif} of a variable and a constant). Variables are those of
 * the loaded store; see {@link ObjectivePresolve}.
 *
 * <p>Setting the system property {@code org.jacop.fz.objectivePresolve} to false turns objective
 * presolve off.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class ObjectiveDetector implements ParserTreeConstants {

  private final Support support;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public ObjectiveDetector(Support support) {
    this.support = support;
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
      case "int_eq_reif" -> {
        IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (y.singleton() && !x.singleton()) {
          presolve.addValueLiteral(x, y.value(), b);
        } else if (x.singleton() && !y.singleton()) {
          presolve.addValueLiteral(y, x.value(), b);
        }
      }
      default -> {
        // not used by objective presolve
      }
    }
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
