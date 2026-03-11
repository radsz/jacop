/*
 * ComparisonConstraints.java
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

import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XorBool;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.satwrapper.SatTranslation;

/*
 * Generation of comparison constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski
 */
class ComparisonConstraints implements ParserTreeConstants {

  final Support support;
  final Store store;
  final SatTranslation sat;

  public ComparisonConstraints(Support support) {
    this.support = support;
    this.store = support.store;
    this.sat = support.sat;
  }

  // =========== bool =================
  void gen_bool_eq(SimpleNode node) {

    if (support.options.useSat()) {
      IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
      IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

      sat.generateEq(a, b);
      return;
    }
    int_comparison(Support.EQ, node);
  }

  void gen_bool_eq_reif(SimpleNode node) {

    if (support.options.useSat()) {

      IntVar v1 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
      IntVar v2 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
      IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

      sat.generateEqReif(v1, v2, v3);

      return;
    }

    int_comparison_reif(Support.EQ, node);
  }

  void gen_bool_eq_imp(SimpleNode node) {
    int_comparison_imp(Support.EQ, node);
  }

  void gen_bool_ne(SimpleNode node) {
    if (support.options.useSat()) {

      IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
      IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

      sat.generateNot(a, b);
      return;
    }

    int_comparison(Support.NE, node);
  }

  void gen_bool_ne_reif(SimpleNode node) {

    if (support.options.useSat()) {

      IntVar v1 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
      IntVar v2 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
      IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

      sat.generateNeqReif(v1, v2, v3);
      return;
    }

    int_comparison_reif(Support.NE, node);
  }

  void gen_bool_ne_imp(SimpleNode node) {
    int_comparison_imp(Support.NE, node);
  }

  void gen_bool_le(SimpleNode node) {

    if (support.options.useSat()) {

      IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
      IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

      sat.generateLe(a, b);
      return;
    }

    int_comparison(Support.LE, node);
  }

  void gen_bool_le_reif(SimpleNode node) {

    if (support.options.useSat()) {

      IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
      IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
      IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

      sat.generateLeReif(a, b, c);
      return;
    }

    int_comparison_reif(Support.LE, node);
  }

  void gen_bool_le_imp(SimpleNode node) {
    int_comparison_imp(Support.LE, node);
  }

  void gen_bool_lt(SimpleNode node) {

    if (support.options.useSat()) {

      IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
      IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

      sat.generateLt(a, b);
      return;
    }

    int_comparison(Support.LT, node);
  }

  void gen_bool_lt_reif(SimpleNode node) {

    if (support.options.useSat()) {

      IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
      IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
      IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

      sat.generateLtReif(a, b, c);
    }

    int_comparison_reif(Support.LT, node);
  }

  void gen_bool_lt_imp(SimpleNode node) {
    int_comparison_imp(Support.LT, node);
  }

  void gen_bool_gt_imp(SimpleNode node) {
    int_comparison_imp(Support.GT, node);
  }

  void gen_bool_ge_imp(SimpleNode node) {
    int_comparison_imp(Support.GE, node);
  }

  // =========== int =================
  void gen_int_eq(SimpleNode node) {
    int_comparison(Support.EQ, node);
  }

  void gen_int_eq_reif(SimpleNode node) {
    int_comparison_reif(Support.EQ, node);
  }

  void gen_int_eq_imp(SimpleNode node) {
    int_comparison_imp(Support.EQ, node);
  }

  void gen_int_ne(SimpleNode node) {
    int_comparison(Support.NE, node);
  }

  void gen_int_ne_reif(SimpleNode node) {
    int_comparison_reif(Support.NE, node);
  }

  void gen_int_ne_imp(SimpleNode node) {
    int_comparison_imp(Support.NE, node);
  }

  void gen_int_le(SimpleNode node) {
    int_comparison(Support.LE, node);
  }

  void gen_int_le_reif(SimpleNode node) {
    int_comparison_reif(Support.LE, node);
  }

  void gen_int_le_imp(SimpleNode node) {
    int_comparison_imp(Support.LE, node);
  }

  void gen_int_lt(SimpleNode node) {
    int_comparison(Support.LT, node);
  }

  void gen_int_lt_reif(SimpleNode node) {
    int_comparison_reif(Support.LT, node);
  }

  void gen_int_lt_imp(SimpleNode node) {
    int_comparison_imp(Support.LT, node);
  }

  void gen_int_gt_imp(SimpleNode node) {
    int_comparison_imp(Support.GT, node);
  }

  void gen_int_ge_imp(SimpleNode node) {
    int_comparison_imp(Support.GE, node);
  }

  void int_comparison(int operation, SimpleNode node) {

    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    boolean p1Const = p1.getType() == 0 || p1.getType() == 1;
    boolean p2Const = p2.getType() == 0 || p2.getType() == 1;

    if (p1Const && p2Const) {
      int i1 = support.getInt(p1);
      checkIntConstantInBounds(i1);
      int i2 = support.getInt(p2);
      checkIntConstantInBounds(i2);
      intComparisonTwoConstants(operation, i1, i2);
      return;
    }
    if (p1Const) {
      int i1 = support.getInt(p1);
      checkIntConstantInBounds(i1);
      intComparisonConstVar(operation, i1, support.getVariable(p2));
      return;
    }
    if (p2Const) {
      IntVar v1 = support.getVariable(p1);
      int i2 = support.getInt(p2);
      checkIntConstantInBounds(i2);
      intComparisonVarConst(operation, v1, i2);
      return;
    }
    intComparisonVarVar(operation, support.getVariable(p1), support.getVariable(p2));
  }

  private static void checkIntConstantInBounds(int value) {
    if (value < IntDomain.MIN_INT || value > IntDomain.MAX_INT) {
      throw new ArithmeticException(
          "Constant "
              + value
              + " outside variable bounds; must be in interval "
              + IntDomain.MIN_INT
              + ".."
              + IntDomain.MAX_INT);
    }
  }

  private void intComparisonTwoConstants(int operation, int i1, int i2) {
    switch (operation) {
      case Support.EQ:
        if (i1 != i2) {
          throw Store.failException;
        }
        break;
      case Support.NE:
        if (i1 == i2) {
          throw Store.failException;
        }
        break;
      case Support.LT:
        if (i1 >= i2) {
          throw Store.failException;
        }
        break;
      case Support.GT:
        if (i1 <= i2) {
          throw Store.failException;
        }
        break;
      case Support.LE:
        if (i1 > i2) {
          throw Store.failException;
        }
        break;
      case Support.GE:
        if (i1 < i2) {
          throw Store.failException;
        }
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
  }

  private void intComparisonConstVar(int operation, int i1, IntVar v2) {
    switch (operation) {
      case Support.EQ:
        v2.domain.inValue(store.level, v2, i1);
        break;
      case Support.NE:
        v2.domain.inComplement(store.level, v2, i1);
        break;
      case Support.LT:
        v2.domain.inMin(store.level, v2, i1 + 1);
        break;
      case Support.GT:
        v2.domain.inMax(store.level, v2, i1 - 1);
        break;
      case Support.LE:
        v2.domain.inMin(store.level, v2, i1);
        break;
      case Support.GE:
        v2.domain.inMax(store.level, v2, i1);
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
  }

  /** Returns null if already handled, or the constraint to pose. */
  private PrimitiveConstraint intComparisonConstVar(
      int operation, ASTScalarFlatExpr p1, ASTScalarFlatExpr p2, IntVar v3, boolean isReified) {
    IntVar v2 = support.getVariable(p2);
    int i1 = support.getInt(p1);
    validateConstantBounds(i1);
    return switch (operation) {
      case Support.EQ -> intComparisonConstVarEq(v2, i1, v3, isReified);
      case Support.NE -> intComparisonConstVarNe(v2, i1, v3, isReified);
      case Support.LT -> intComparisonConstVarLt(v2, i1, v3);
      case Support.GT -> intComparisonConstVarGt(v2, i1, v3);
      case Support.LE -> intComparisonConstVarLe(v2, i1, v3);
      case Support.GE -> intComparisonConstVarGe(v2, i1, v3);
      default -> throw new RuntimeException("Internal error in " + getClass().getName());
    };
  }

  private PrimitiveConstraint intComparisonConstVarEq(
      IntVar v2, int i1, IntVar v3, boolean isReified) {
    if (isReified && support.reif.size(v2) > support.reif.minSize) {
      return null;
    }
    if (!v2.domain.contains(i1)) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    if (v2.min() == i1 && v2.singleton()) {
      v3.domain.inValue(store.level, v3, 1);
      return null;
    }
    if (v3.max() == 0) {
      v2.domain.inComplement(store.level, v2, i1);
      return null;
    }
    if (v3.min() == 1) {
      v2.domain.inValue(store.level, v2, i1);
      return null;
    }
    if (isReified && generateForEqC(v2, i1, v3)) {
      return null;
    }
    if (isReified) {
      support.pose(support.fzXeqCreified(v2, i1, v3));
    } else {
      support.pose(support.fzXeqCimplied(v2, i1, v3));
    }
    return null;
  }

  private PrimitiveConstraint intComparisonConstVarNe(
      IntVar v2, int i1, IntVar v3, boolean isReified) {
    if (v2.min() > i1 || v2.max() < i1) {
      v3.domain.inValue(store.level, v3, 1);
      return null;
    }
    if (v2.min() == i1 && v2.singleton()) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    if (isReified && generateForNeqC(v2, i1, v3)) {
      return null;
    }
    if (isReified) {
      support.pose(support.fzXneqCreified(v2, i1, v3));
    } else {
      support.pose(support.fzXneqCimplied(v2, i1, v3));
    }
    return null;
  }

  private PrimitiveConstraint intComparisonConstVarLt(IntVar v2, int i1, IntVar v3) {
    if (i1 < v2.min()) {
      v3.domain.inValue(store.level, v3, 1);
      return null;
    }
    if (i1 >= v2.max()) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    return new XgtC(v2, i1);
  }

  private PrimitiveConstraint intComparisonConstVarGt(IntVar v2, int i1, IntVar v3) {
    if (i1 > v2.max()) {
      v3.domain.inValue(store.level, v3, 1);
      return null;
    }
    if (i1 <= v2.min()) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    return new XltC(v2, i1);
  }

  private PrimitiveConstraint intComparisonConstVarLe(IntVar v2, int i1, IntVar v3) {
    if (i1 <= v2.min()) {
      v3.domain.inValue(store.level, v3, 1);
      return null;
    }
    if (i1 > v2.max()) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    return new XgteqC(v2, i1);
  }

  private PrimitiveConstraint intComparisonConstVarGe(IntVar v2, int i1, IntVar v3) {
    if (i1 > v2.max()) {
      v3.domain.inValue(store.level, v3, 1);
      return null;
    }
    if (i1 < v2.min()) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    return new XlteqC(v2, i1);
  }

  private void intComparisonVarConst(int operation, IntVar v1, int i2) {
    switch (operation) {
      case Support.EQ:
        v1.domain.inValue(store.level, v1, i2);
        break;
      case Support.NE:
        v1.domain.inComplement(store.level, v1, i2);
        break;
      case Support.LT:
        v1.domain.inMax(store.level, v1, i2 - 1);
        break;
      case Support.GT:
        v1.domain.inMin(store.level, v1, i2 + 1);
        break;
      case Support.LE:
        v1.domain.inMax(store.level, v1, i2);
        break;
      case Support.GE:
        v1.domain.inMin(store.level, v1, i2);
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
  }

  /** Returns null if already handled (domain/pose), or the constraint to pose. */
  private PrimitiveConstraint intComparisonVarConst(
      int operation, ASTScalarFlatExpr p1, ASTScalarFlatExpr p2, IntVar v3, boolean isReified) {
    IntVar v1 = support.getVariable(p1);
    int i2 = support.getInt(p2);
    validateConstantBounds(i2);
    return switch (operation) {
      case Support.EQ -> intComparisonVarConstEq(v1, i2, v3, isReified);
      case Support.NE -> intComparisonVarConstNe(v1, i2, v3, isReified);
      case Support.LT -> intComparisonVarConstLt(v1, i2, v3, isReified);
      case Support.GT -> intComparisonVarConstGt(v1, i2, v3, isReified);
      case Support.LE -> intComparisonVarConstLe(v1, i2, v3, isReified);
      case Support.GE -> intComparisonVarConstGe(v1, i2, v3, isReified);
      default -> throw new RuntimeException("Internal error in " + getClass().getName());
    };
  }

  private void validateConstantBounds(int i2) {
    if (i2 < IntDomain.MIN_INT || i2 > IntDomain.MAX_INT) {
      throw new ArithmeticException(
          "Constant "
              + i2
              + " outside variable bounds ; must be in interval "
              + IntDomain.MIN_INT
              + ".."
              + IntDomain.MAX_INT);
    }
  }

  private PrimitiveConstraint intComparisonVarConstEq(
      IntVar v1, int i2, IntVar v3, boolean isReified) {
    if ((isReified ? support.reif.size(v1) : support.imply.size(v1))
        > (isReified ? support.reif.minSize : support.imply.minSize)) {
      return null;
    }
    if (!v1.domain.contains(i2)) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    if (isReified && v1.min() == i2 && v1.singleton()) {
      v3.domain.inValue(store.level, v3, 1);
      return null;
    }
    if (v3.max() == 0) {
      if (isReified) {
        v1.domain.inComplement(store.level, v1, i2);
      }
      return null;
    }
    if (v3.min() == 1) {
      v1.domain.inValue(store.level, v1, i2);
      return null;
    }
    if (isReified && generateForEqC(v1, i2, v3)) {
      return null;
    }
    if (isReified) {
      support.pose(support.fzXeqCreified(v1, i2, v3));
    } else {
      support.pose(support.fzXeqCimplied(v1, i2, v3));
    }
    return null;
  }

  private PrimitiveConstraint intComparisonVarConstNe(
      IntVar v1, int i2, IntVar v3, boolean isReified) {
    if (v1.min() > i2 || v1.max() < i2) {
      if (isReified) {
        v3.domain.inValue(store.level, v3, 1);
      }
      return null;
    }
    if (v1.min() == i2 && v1.singleton()) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    if (v3.max() == 0) {
      return null;
    }
    if (v3.min() == 1) {
      v1.domain.inComplement(store.level, v1, i2);
      return null;
    }
    if (isReified && generateForNeqC(v1, i2, v3)) {
      return null;
    }
    if (isReified) {
      support.pose(support.fzXneqCreified(v1, i2, v3));
    } else {
      support.pose(support.fzXneqCimplied(v1, i2, v3));
    }
    return null;
  }

  private PrimitiveConstraint intComparisonVarConstLt(
      IntVar v1, int i2, IntVar v3, boolean isReified) {
    if (v1.max() < i2) {
      if (isReified) {
        v3.domain.inValue(store.level, v3, 1);
      }
      return null;
    }
    if (v1.min() >= i2) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    if (!isReified && v3.max() == 0) {
      return null;
    }
    if (v3.min() == 1) {
      v1.domain.inMax(store.level, v1, i2 - 1);
      return null;
    }
    return new XltC(v1, i2);
  }

  private PrimitiveConstraint intComparisonVarConstGt(
      IntVar v1, int i2, IntVar v3, boolean isReified) {
    if (v1.min() > i2) {
      if (isReified) {
        v3.domain.inValue(store.level, v3, 1);
      }
      return null;
    }
    if (v1.max() <= i2) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    if (!isReified && v3.max() == 0) {
      return null;
    }
    if (v3.min() == 1) {
      v1.domain.inMin(store.level, v1, i2 + 1);
      return null;
    }
    return new XgtC(v1, i2);
  }

  private PrimitiveConstraint intComparisonVarConstLe(
      IntVar v1, int i2, IntVar v3, boolean isReified) {
    if (v1.max() <= i2) {
      if (isReified) {
        v3.domain.inValue(store.level, v3, 1);
      }
      return null;
    }
    if (v1.min() > i2) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    if (!isReified && v3.max() == 0) {
      return null;
    }
    if (v3.min() == 1) {
      v1.domain.inMax(store.level, v1, i2);
      return null;
    }
    return new XlteqC(v1, i2);
  }

  private PrimitiveConstraint intComparisonVarConstGe(
      IntVar v1, int i2, IntVar v3, boolean isReified) {
    if (v1.min() >= i2) {
      if (isReified) {
        v3.domain.inValue(store.level, v3, 1);
      }
      return null;
    }
    if (v1.max() < i2) {
      v3.domain.inValue(store.level, v3, 0);
      return null;
    }
    if (!isReified && v3.max() == 0) {
      return null;
    }
    if (v3.min() == 1) {
      v1.domain.inMin(store.level, v1, i2);
      return null;
    }
    return new XgteqC(v1, i2);
  }

  private void intComparisonVarVar(int operation, IntVar v1, IntVar v2) {
    switch (operation) {
      case Support.EQ:
        support.pose(new XeqY(v1, v2));
        break;
      case Support.NE:
        support.pose(new XneqY(v1, v2));
        break;
      case Support.LT:
        support.pose(new XltY(v1, v2));
        break;
      case Support.GT:
        support.pose(new XgtY(v1, v2));
        break;
      case Support.LE:
        support.pose(new XlteqY(v1, v2));
        break;
      case Support.GE:
        support.pose(new XgteqY(v1, v2));
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
  }

  /** Returns null if already handled, or the constraint to pose. */
  private PrimitiveConstraint intComparisonVarVar(
      int operation, ASTScalarFlatExpr p1, ASTScalarFlatExpr p2, IntVar v3, boolean isReified) {
    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);

    return switch (operation) {
      case Support.EQ -> intComparisonVarVarEq(v1, v2, v3, isReified);
      case Support.NE -> intComparisonVarVarNe(v1, v2, v3, isReified);
      case Support.LT -> new XltY(v1, v2);
      case Support.GT -> new XgtY(v1, v2);
      case Support.LE -> new XlteqY(v1, v2);
      case Support.GE -> new XgteqY(v1, v2);
      default -> throw new RuntimeException("Internal error in " + getClass().getName());
    };
  }

  private PrimitiveConstraint intComparisonVarVarEq(
      IntVar v1, IntVar v2, IntVar v3, boolean isReified) {
    if (isReified) {
      if (generateForEq(v1, v2, v3)) {
        return null;
      }
      if (generateForEq(v2, v1, v3)) {
        return null;
      }
      if (binaryVar(v1) && binaryVar(v2)) {
        if (support.options.useSat()) {
          support.sat.generateEqReif(v1, v2, v3);
        } else {
          support.pose(new Not(new XorBool(new IntVar[] {v1, v2}, v3)));
        }
        return null;
      }
    }
    if (v2.singleton()) {
      poseEqVarConst(v1, v2.value(), v3, isReified);
      return null;
    }
    if (v1.singleton()) {
      poseEqVarConst(v2, v1.value(), v3, isReified);
      return null;
    }
    if (isReified) {
      support.pose(support.fzXeqYreified(v1, v2, v3));
    } else {
      support.pose(support.fzXeqYimplied(v1, v2, v3));
    }
    return null;
  }

  private void poseEqVarConst(IntVar v, int c, IntVar b, boolean isReified) {
    if (isReified) {
      support.pose(support.fzXeqCreified(v, c, b));
    } else {
      support.pose(support.fzXeqCimplied(v, c, b));
    }
  }

  private PrimitiveConstraint intComparisonVarVarNe(
      IntVar v1, IntVar v2, IntVar v3, boolean isReified) {
    if (isReified) {
      if (generateForNeq(v1, v2, v3)) {
        return null;
      }
      if (generateForNeq(v2, v1, v3)) {
        return null;
      }
      if (binaryVar(v1) && binaryVar(v2)) {
        if (support.options.useSat()) {
          support.sat.generateNeqReif(v1, v2, v3);
        } else {
          support.pose(new XorBool(new IntVar[] {v1, v2}, v3));
        }
        return null;
      }
    }
    if (v2.singleton()) {
      poseNeqVarConst(v1, v2.value(), v3, isReified);
      return null;
    }
    if (v1.singleton()) {
      poseNeqVarConst(v2, v1.value(), v3, isReified);
      return null;
    }
    return new XneqY(v1, v2);
  }

  private void poseNeqVarConst(IntVar v, int c, IntVar b, boolean isReified) {
    if (isReified) {
      support.pose(support.fzXneqCreified(v, c, b));
    } else {
      support.pose(support.fzXneqCimplied(v, c, b));
    }
  }

  void int_comparison_reif(int operation, SimpleNode node) {
    int_comparison_reif_imp(operation, node, true);
  }

  void int_comparison_imp(int operation, SimpleNode node) {
    int_comparison_reif_imp(operation, node, false);
  }

  private void int_comparison_reif_imp(int operation, SimpleNode node, boolean isReified) {

    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);
    IntVar v3 = support.getVariable(p3);

    PrimitiveConstraint c;
    if (p2.getType() == 0 || p2.getType() == 1) {
      c = intComparisonVarConst(operation, p1, p2, v3, isReified);
    } else if (p1.getType() == 0 || p1.getType() == 1) {
      c = intComparisonConstVar(operation, p1, p2, v3, isReified);
    } else {
      c = intComparisonVarVar(operation, p1, p2, v3, isReified);
    }

    if (c != null) {
      Constraint cr = isReified ? new Reified(c, v3) : new Implies(v3, c);
      support.pose(cr);
    }
  }

  boolean generateForEqC(IntVar v1, int i2, IntVar b) {
    if (v1.min() >= 0 && v1.max() <= 1) { // binary variables
      if (i2 == 0) {
        support.pose(new XneqY(v1, b));
        return true;
      } else if (i2 == 1) {
        support.pose(new XeqY(v1, b));
        return true;
      }
    }
    return false;
  }

  boolean generateForNeqC(IntVar v1, int i2, IntVar b) {
    if (v1.min() >= 0 && v1.max() <= 1) { // binary variables
      if (i2 == 0) {
        support.pose(new XeqY(v1, b));
        return true;
      } else if (i2 == 1) {
        support.pose(new XneqY(v1, b));
        return true;
      }
    }
    return false;
  }

  boolean generateForEq(IntVar v1, IntVar v2, IntVar b) {
    if (v1.min() >= 0 && v1.max() <= 1) {
      if (v2.singleton()) {
        if (v2.value() == 1) {
          support.pose(new XeqY(v1, b));
          return true;
        } else if (v2.value() == 0) {
          support.pose(new XneqY(v1, b));
          return true;
        }
      }
    }
    return false;
  }

  boolean generateForNeq(IntVar v1, IntVar v2, IntVar b) {
    if (v1.min() >= 0 && v1.max() <= 1) {
      if (v2.singleton()) {
        if (v2.value() == 1) {
          support.pose(new XneqY(v1, b));
          return true;
        } else if (v2.value() == 0) {
          support.pose(new XeqY(v1, b));
          return true;
        }
      }
    }
    return false;
  }

  boolean binaryVar(IntVar v) {
    return v.min() >= 0 && v.max() <= 1;
  }
}
