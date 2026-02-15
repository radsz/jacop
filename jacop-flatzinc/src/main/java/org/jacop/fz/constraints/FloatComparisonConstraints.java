/*
 * FloatComparisonConstraints.java This file is part of JaCoP.
 *
 * <p>JaCoP is a Java Constraint Programming solver.
 *
 * <p>Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 * <p>This program is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Affero General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * <p>This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * <p>Notwithstanding any other provision of this License, the copyright owners of this work
 * supplement the terms of this License with terms prohibiting misrepresentation of the origin of
 * this work and requiring that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license terms is in accordance with
 * Section 7 of GNU Affero General Public License version 3.
 *
 * <p>You should have received a copy of the GNU Affero General Public License along with this
 * program. If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.fz.constraints;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PeqQ;
import org.jacop.floats.constraints.PgtC;
import org.jacop.floats.constraints.PgteqC;
import org.jacop.floats.constraints.PltC;
import org.jacop.floats.constraints.PltQ;
import org.jacop.floats.constraints.PlteqC;
import org.jacop.floats.constraints.PlteqQ;
import org.jacop.floats.constraints.PneqC;
import org.jacop.floats.constraints.PneqQ;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.fz.VariablesParameters;

/**
 * Generation of set constraints in flatzinc.
 *
 * @author Krzysztof Kuchcinski
 */
class FloatComparisonConstraints implements ParserTreeConstants {

  final Support support;
  final Store store;
  boolean reified;

  public FloatComparisonConstraints(Support support) {
    this.support = support;
    this.store = support.store;
  }

  void gen_float_eq(SimpleNode node) {
    reified = false;
    float_comparison(Support.EQ, node);
  }

  void gen_float_eq_reif(SimpleNode node) {
    reified = true;
    float_comparison(Support.EQ, node);
  }

  void gen_float_ne(SimpleNode node) {
    reified = false;
    float_comparison(Support.NE, node);
  }

  void gen_float_ne_reif(SimpleNode node) {
    reified = true;
    float_comparison(Support.NE, node);
  }

  void gen_float_le(SimpleNode node) {
    reified = false;
    float_comparison(Support.LE, node);
  }

  void gen_float_le_reif(SimpleNode node) {
    reified = true;
    float_comparison(Support.LE, node);
  }

  void gen_float_lt(SimpleNode node) {
    reified = false;
    float_comparison(Support.LT, node);
  }

  void gen_float_lt_reif(SimpleNode node) {
    reified = true;
    float_comparison(Support.LT, node);
  }

  void float_comparison(int operation, SimpleNode node) {

    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    if (reified) {
      ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);
      IntVar v3 = support.getVariable(p3);
      PrimitiveConstraint c = floatComparisonReifiedConstraint(operation, node, p1, p2, v3);
      if (c != null) {
        support.pose(new Reified(c, v3));
      }
      return;
    }

    floatComparisonNonReified(operation, node, p1, p2);
  }

  /**
   * Returns the constraint to reify, or null if the case was already fully handled (domain updates
   * and return).
   */
  private PrimitiveConstraint floatComparisonReifiedConstraint(
      int operation, SimpleNode node, ASTScalarFlatExpr p1, ASTScalarFlatExpr p2, IntVar v3) {
    if (p2.getType() == 5) {
      FloatVar v1 = support.getFloatVariable(p1);
      double i2 = support.getFloat(p2);
      return floatComparisonReifiedVarFloat(operation, v1, i2, v3);
    }
    if (p1.getType() == 5) {
      FloatVar v2 = support.getFloatVariable(p2);
      double i1 = support.getFloat(p1);
      return floatComparisonReifiedFloatVar(operation, v2, i1, v3);
    }
    FloatVar v1 = support.getFloatVariable(p1);
    FloatVar v2 = support.getFloatVariable(p2);
    return switch (operation) {
      case Support.EQ -> new PeqQ(v1, v2);
      case Support.NE -> new PneqQ(v1, v2);
      case Support.LT -> new PltQ(v1, v2);
      case Support.LE -> new PlteqQ(v1, v2);
      default -> throw new RuntimeException("Internal error in " + getClass().getName());
    };
  }

  /** Returns the constraint to reify, or null if already fully handled. */
  private PrimitiveConstraint floatComparisonReifiedVarFloat(
      int operation, FloatVar v1, double i2, IntVar v3) {
    return switch (operation) {
      case Support.EQ -> floatComparisonReifiedVarFloatEq(v1, i2, v3);
      case Support.NE -> floatComparisonReifiedVarFloatNe(v1, i2, v3);
      case Support.LT -> floatComparisonReifiedVarFloatLt(v1, i2, v3);
      case Support.LE -> floatComparisonReifiedVarFloatLe(v1, i2, v3);
      default -> throw new RuntimeException("Internal error in " + getClass().getName());
    };
  }

  private PrimitiveConstraint floatComparisonReifiedVarFloatEq(FloatVar v1, double i2, IntVar v3) {
    if (v1.min() > i2 || v1.max() < i2) {
      v3.domain.in(store.level, v3, 0, 0);
      return null;
    }
    if (v1.min() == i2 && v1.singleton()) {
      v3.domain.in(store.level, v3, 1, 1);
      return null;
    }
    if (v3.max() == 0) {
      v1.domain.inComplement(store.level, v1, i2);
      return null;
    }
    if (v3.min() == 1) {
      v1.domain.in(store.level, v1, i2, i2);
      return null;
    }
    return new PeqC(v1, i2);
  }

  private PrimitiveConstraint floatComparisonReifiedVarFloatNe(FloatVar v1, double i2, IntVar v3) {
    if (v1.min() > i2 || v1.max() < i2) {
      v3.domain.in(store.level, v3, 1, 1);
      return null;
    }
    if (v1.min() == i2 && v1.singleton()) {
      v3.domain.in(store.level, v3, 0, 0);
      return null;
    }
    if (v3.max() == 0) {
      v1.domain.in(store.level, v1, i2, i2);
      return null;
    }
    if (v3.min() == 1) {
      v1.domain.inComplement(store.level, v1, i2);
      return null;
    }
    return new PneqC(v1, i2);
  }

  private PrimitiveConstraint floatComparisonReifiedVarFloatLt(FloatVar v1, double i2, IntVar v3) {
    if (v1.max() < i2) {
      v3.domain.in(store.level, v3, 1, 1);
      return null;
    }
    if (v1.min() >= i2) {
      v3.domain.in(store.level, v3, 0, 0);
      return null;
    }
    return new PltC(v1, i2);
  }

  private PrimitiveConstraint floatComparisonReifiedVarFloatLe(FloatVar v1, double i2, IntVar v3) {
    if (v1.max() <= i2) {
      v3.domain.in(store.level, v3, 1, 1);
      return null;
    }
    if (v1.min() > i2) {
      v3.domain.in(store.level, v3, 0, 0);
      return null;
    }
    return new PlteqC(v1, i2);
  }

  /** Returns the constraint to reify, or null if already fully handled. */
  private PrimitiveConstraint floatComparisonReifiedFloatVar(
      int operation, FloatVar v2, double i1, IntVar v3) {
    return switch (operation) {
      case Support.EQ -> floatComparisonReifiedFloatVarEq(v2, i1, v3);
      case Support.NE -> floatComparisonReifiedFloatVarNe(v2, i1, v3);
      case Support.LT -> floatComparisonReifiedFloatVarLt(v2, i1, v3);
      case Support.LE -> floatComparisonReifiedFloatVarLe(v2, i1, v3);
      default -> throw new RuntimeException("Internal error in " + getClass().getName());
    };
  }

  private PrimitiveConstraint floatComparisonReifiedFloatVarEq(FloatVar v2, double i1, IntVar v3) {
    if (v2.min() > i1 || v2.max() < i1) {
      v3.domain.in(store.level, v3, 0, 0);
      return null;
    }
    if (v2.min() == i1 && v2.singleton()) {
      v3.domain.in(store.level, v3, 1, 1);
      return null;
    }
    if (v3.max() == 0) {
      v2.domain.inComplement(store.level, v2, i1);
      return null;
    }
    if (v3.min() == 1) {
      v2.domain.in(store.level, v2, i1, i1);
      return null;
    }
    return new PeqC(v2, i1);
  }

  private PrimitiveConstraint floatComparisonReifiedFloatVarNe(FloatVar v2, double i1, IntVar v3) {
    if (v2.min() > i1 || v2.max() < i1) {
      v3.domain.in(store.level, v3, 1, 1);
      return null;
    }
    if (v2.min() == i1 && v2.singleton()) {
      v3.domain.in(store.level, v3, 0, 0);
      return null;
    }
    return new PneqC(v2, i1);
  }

  private PrimitiveConstraint floatComparisonReifiedFloatVarLt(FloatVar v2, double i1, IntVar v3) {
    if (i1 < v2.min()) {
      v3.domain.in(store.level, v3, 1, 1);
      return null;
    }
    if (i1 >= v2.max()) {
      v3.domain.in(store.level, v3, 0, 0);
      return null;
    }
    return new PgtC(v2, i1);
  }

  private PrimitiveConstraint floatComparisonReifiedFloatVarLe(FloatVar v2, double i1, IntVar v3) {
    if (i1 <= v2.min()) {
      v3.domain.in(store.level, v3, 1, 1);
      return null;
    }
    if (i1 > v2.max()) {
      v3.domain.in(store.level, v3, 0, 0);
      return null;
    }
    return new PgteqC(v2, i1);
  }

  private void floatComparisonNonReified(
      int operation, SimpleNode node, ASTScalarFlatExpr p1, ASTScalarFlatExpr p2) {
    boolean p1Float = p1.getType() == 5;
    boolean p2Float = p2.getType() == 5;
    if (p1Float && (p2.getType() == 0 || p2.getType() == 1)) {
      floatComparisonNonReifiedTwoConstants(operation, support.getFloat(p1), support.getFloat(p2));
      return;
    }
    if (p1Float) {
      floatComparisonNonReifiedFloatVar(
          operation, support.getFloat(p1), support.getFloatVariable(p2));
      return;
    }
    if (p2.getType() == 5) {
      floatComparisonNonReifiedVarFloat(
          operation, support.getFloatVariable(p1), support.getFloat(p2));
      return;
    }
    FloatVar v1 = support.getFloatVariable(p1);
    FloatVar v2 = support.getFloatVariable(p2);
    floatComparisonNonReifiedVarVar(operation, v1, v2);
  }

  private void floatComparisonNonReifiedTwoConstants(int operation, double i1, double i2) {
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
      case Support.LE:
        if (i1 > i2) {
          throw Store.failException;
        }
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
  }

  private void floatComparisonNonReifiedFloatVar(int operation, double i1, FloatVar v2) {
    switch (operation) {
      case Support.EQ:
        v2.domain.in(store.level, v2, i1, i1);
        break;
      case Support.NE:
        v2.domain.inComplement(store.level, v2, i1);
        break;
      case Support.LT:
        v2.domain.in(store.level, v2, FloatDomain.next(i1), VariablesParameters.MAX_FLOAT);
        break;
      case Support.LE:
        v2.domain.in(store.level, v2, i1, VariablesParameters.MAX_FLOAT);
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
  }

  private void floatComparisonNonReifiedVarFloat(int operation, FloatVar v1, double i2) {
    switch (operation) {
      case Support.EQ:
        v1.domain.in(store.level, v1, i2, i2);
        break;
      case Support.NE:
        v1.domain.inComplement(store.level, v1, i2);
        break;
      case Support.LT:
        v1.domain.in(store.level, v1, VariablesParameters.MIN_FLOAT, FloatDomain.previous(i2));
        break;
      case Support.LE:
        v1.domain.in(store.level, v1, VariablesParameters.MIN_FLOAT, i2);
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
  }

  private void floatComparisonNonReifiedVarVar(int operation, FloatVar v1, FloatVar v2) {
    switch (operation) {
      case Support.EQ:
        support.pose(new PeqQ(v1, v2));
        break;
      case Support.NE:
        support.pose(new PneqQ(v1, v2));
        break;
      case Support.LT:
        support.pose(new PltQ(v1, v2));
        break;
      case Support.LE:
        support.pose(new PlteqQ(v1, v2));
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
  }
}
