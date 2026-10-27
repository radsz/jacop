/*
 * RestartConstraints.java
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

import org.jacop.core.IntVar;
import org.jacop.floats.core.FloatVar;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.OnRestart;
import org.jacop.fz.SimpleNode;

/**
 * Generation of MiniZinc's on_restart built-ins ({@code jacop_on_restart_*}) in flatzinc. They post
 * no constraint; they register their variables with {@link OnRestart}, which fixes them at the root
 * of every run of the restart search.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 */
class RestartConstraints {

  final Support support;

  RestartConstraints(Support support) {
    this.support = support;
  }

  private OnRestart onRestart() {
    return support.dictionary.onRestart();
  }

  private IntVar intVar(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private FloatVar floatVar(SimpleNode node, int i) {
    return support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  void gen_jacop_on_restart_status(SimpleNode node) {
    onRestart().addStatus(intVar(node, 0));
  }

  void gen_jacop_on_restart_complete(SimpleNode node) {
    onRestart().addComplete(intVar(node, 0));
  }

  void gen_jacop_on_restart_sol_int(SimpleNode node) {
    onRestart().addSol(intVar(node, 0), intVar(node, 1));
  }

  void gen_jacop_on_restart_sol_float(SimpleNode node) {
    onRestart().addSol(floatVar(node, 0), floatVar(node, 1));
  }

  void gen_jacop_on_restart_last_val_int(SimpleNode node) {
    onRestart().addLastVal(intVar(node, 0), intVar(node, 1));
  }

  void gen_jacop_on_restart_last_val_float(SimpleNode node) {
    onRestart().addLastVal(floatVar(node, 0), floatVar(node, 1));
  }

  void gen_jacop_on_restart_uniform_int(SimpleNode node) {
    int low = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(0));
    int high = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    onRestart().addUniform(low, high, intVar(node, 2));
  }

  void gen_jacop_on_restart_uniform_float(SimpleNode node) {
    double low = support.getFloat((ASTScalarFlatExpr) node.jjtGetChild(0));
    double high = support.getFloat((ASTScalarFlatExpr) node.jjtGetChild(1));
    onRestart().addUniform(low, high, floatVar(node, 2));
  }
}
