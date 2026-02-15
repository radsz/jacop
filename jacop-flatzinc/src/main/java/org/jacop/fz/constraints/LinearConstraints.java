/*
 * LinearConstraints.java
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

import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Not;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Sum;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.satwrapper.SatTranslation;

/**
 * Generation of linear constraints in flatzinc.
 *
 * @author Krzysztof Kuchcinski
 */
class LinearConstraints implements ParserTreeConstants {

  final Store store;
  final Support support;
  final SatTranslation sat;

  public LinearConstraints(Support support) {
    this.store = support.store;
    this.support = support;
    this.sat = support.sat;
  }

  void gen_bool_lin_eq(SimpleNode node) {

    int[] p1 = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] p2 = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar par3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    // If a linear term contains only constants and can be evaluated
    // check if satisfied and do not generate constraint
    if (par3.min() == par3.max()) {
      Integer sum = evaluateConstantLinearTerm(p1, p2);
      if (sum != null) {
        if (sum == par3.min()) {
          return;
        } else {
          throw Store.failException;
        }
      }
    }

    if (allWeightsOne(p1)) {
      support.pose(new SumBool(p2, "==", par3));
    } else {
      if (p2.length < 100) {
        support.pose(new LinearInt(p2, p1, "==", par3));
      } else {
        support.pose(new SumWeight(p2, p1, par3));
      }
    }
  }

  void gen_int_lin_eq(SimpleNode node) {
    int_lin_relation(Support.EQ, node);
  }

  void gen_int_lin_eq_reif(SimpleNode node) {
    int_lin_relation_reif(Support.EQ, node);
  }

  void gen_int_lin_eq_imp(SimpleNode node) {
    int_lin_relation_imp(Support.EQ, node);
  }

  void gen_int_lin_ne(SimpleNode node) {
    int_lin_relation(Support.NE, node);
  }

  void gen_int_lin_ne_reif(SimpleNode node) {
    int_lin_relation_reif(Support.NE, node);
  }

  void gen_int_lin_ne_imp(SimpleNode node) {
    int_lin_relation_imp(Support.NE, node);
  }

  void gen_int_lin_lt(SimpleNode node) {
    int_lin_relation(Support.LT, node);
  }

  void gen_int_lin_lt_reif(SimpleNode node) {
    int_lin_relation_reif(Support.LT, node);
  }

  void gen_int_lin_lt_imp(SimpleNode node) {
    int_lin_relation_imp(Support.LT, node);
  }

  void gen_int_lin_le(SimpleNode node) {
    int_lin_relation(Support.LE, node);
  }

  void gen_int_lin_le_reif(SimpleNode node) {
    int_lin_relation_reif(Support.LE, node);
  }

  void gen_int_lin_le_imp(SimpleNode node) {
    int_lin_relation_imp(Support.LE, node);
  }

  void gen_int_lin_gt_imp(SimpleNode node) {
    int_lin_relation_imp(Support.GT, node);
  }

  void gen_int_lin_ge_imp(SimpleNode node) {
    int_lin_relation_imp(Support.GE, node);
  }

  void int_lin_relation_reif(int operation, SimpleNode node) throws FailException {
    int_lin_relation_reif_imp(operation, node, true);
  }

  void int_lin_relation_imp(int operation, SimpleNode node) throws FailException {
    int_lin_relation_reif_imp(operation, node, false);
  }

  private void int_lin_relation_reif_imp(int operation, SimpleNode node, boolean isReified)
      throws FailException {

    int[] p1 = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] p2 = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int p3 = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    boolean p2Fixed = allConstants(p2);
    int s = 0;
    if (p2Fixed) {
      for (int el = 0; el < p2.length; el++) {
        s += p2[el].min() * p1[el];
      }
    }
    IntVar p4 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

    switch (operation) {
      case Support.EQ:
        intLinReifEq(p1, p2, p3, p4, p2Fixed, s, isReified);
        return;
      case Support.NE:
        intLinReifNe(p1, p2, p3, p4, isReified);
        return;
      case Support.LT:
        poseReifiedOrImplied(new LinearInt(p2, p1, "<", p3), p4, isReified);
        return;
      case Support.GT:
        if (isReified) {
          throw new IllegalArgumentException(
              "%% ERROR: Relation GT not supported for reified constraint.");
        }
        support.pose(new Implies(p4, new LinearInt(p2, p1, ">", p3)));
        return;
      case Support.GE:
        if (isReified) {
          throw new IllegalArgumentException(
              "%% ERROR: Relation GE not supported for reified constraint.");
        }
        support.pose(new Implies(p4, new LinearInt(p2, p1, ">=", p3)));
        return;
      case Support.LE:
        intLinReifLe(p1, p2, p3, p4, isReified);
        return;
      default:
        throw new IllegalArgumentException(
            "%% ERROR: Relation in linear constraint not supported.");
    }
  }

  private void intLinReifEq(
      int[] p1, IntVar[] p2, int p3, IntVar p4, boolean p2Fixed, int s, boolean isReified) {
    if (p2Fixed) {
      handleIntLinReifEqFixed(p4, p3, s, isReified);
      return;
    }

    if (p1.length == 1) {
      handleIntLinReifEqSingleVar(p1[0], p2[0], p3, p4, isReified);
      return;
    }
    if (p1.length == 2) {
      if (handleIntLinReifEqTwoVars(p1, p2, p3, p4, isReified)) {
        return;
      }
    }

    int pos = sumPossible(p1, p3);
    if (pos > -1) {
      IntVar[] vect = createVectorExcluding(p2, pos);
      poseSumBoolOrIntReified(vect, "==", p2[pos], p4, isReified);
    } else if (allWeightsOne(p1)) {
      poseSumBoolOrIntReified(p2, "==", p3, p4, isReified);
    } else if (allWeightsMinusOne(p1)) {
      poseSumBoolOrIntReified(p2, "==", -p3, p4, isReified);
    } else {
      poseReifiedOrImplied(new LinearInt(p2, p1, "==", p3), p4, isReified);
    }
  }

  private void handleIntLinReifEqFixed(IntVar p4, int p3, int s, boolean isReified) {
    if (isReified) {
      p4.domain.inValue(store.level, p4, s == p3 ? 1 : 0);
    } else if (s != p3) {
      p4.domain.inValue(store.level, p4, 0);
    }
  }

  private void handleIntLinReifEqSingleVar(int w, IntVar x, int p3, IntVar p4, boolean isReified) {
    if (w == 1) {
      if (isReified) {
        if (x.min() == 0 && x.max() == 1 && p3 >= 0 && p3 <= 1) {
          if (p3 == 0) {
            support.pose(new XneqY(x, p4));
          } else {
            support.pose(new XeqY(x, p4));
          }
        } else {
          support.pose(support.fzXeqCreified(x, p3, p4));
        }
      } else {
        support.pose(support.fzXeqCimplied(x, p3, p4));
      }
    } else {
      poseReifiedOrImplied(new XmulCeqZ(x, w, support.dictionary.getConstant(p3)), p4, isReified);
    }
  }

  private void handleIntLinReifLeTwoVarsOneMinusOne(
      IntVar x, IntVar y, int p3, IntVar p4, boolean isReified, boolean swapped) {
    if (p3 == 0) {
      if (!swapped) {
        if (isReified) {
          support.pose(new Reified(new XlteqY(x, y), p4));
        } else {
          support.pose(new Implies(p4, new XlteqY(x, y)));
        }
      } else {
        poseReifiedOrImplied(new XlteqY(x, y), p4, isReified);
      }
      return;
    }
    PrimitiveConstraint leqConstraint = new XplusClteqZ(x, -p3, y);
    if (isReified) {
      if (p4.min() == 1) {
        support.pose(leqConstraint);
      } else if (p4.max() == 0) {
        support.pose(new Not(leqConstraint));
      } else if (x.singleton()) {
        support.pose(new Reified(new XgteqC(y, x.value() - p3), p4));
      } else {
        support.pose(new Reified(leqConstraint, p4));
      }
    } else {
      if (x.singleton()) {
        support.pose(new Implies(p4, new XgteqC(y, x.value() - p3)));
      } else {
        support.pose(new Implies(p4, leqConstraint));
      }
    }
  }

  private boolean handleIntLinReifEqTwoVars(
      int[] p1, IntVar[] p2, int p3, IntVar p4, boolean isReified) {
    if (p1[0] == 1 && p1[1] == -1) {
      poseReifiedOrImplied(new XplusCeqZ(p2[1], p3, p2[0]), p4, isReified);
      return true;
    }
    if (p1[0] == -1 && p1[1] == 1) {
      poseReifiedOrImplied(new XplusCeqZ(p2[0], p3, p2[1]), p4, isReified);
      return true;
    }
    if (p1[0] == 1 && p1[1] == 1) {
      if (isReified && binaryVar(p2[0]) && binaryVar(p2[1]) && p3 >= 0 && p3 <= 2) {
        if (p3 == 0) {
          support.pose(new Not(new OrBoolSimple(p2[0], p2[1], p4)));
        } else if (p3 == 1) {
          support.pose(new XorBool(new IntVar[] {p2[0], p2[1]}, p4));
        } else {
          support.pose(new AndBoolSimple(p2[0], p2[1], p4));
        }
      } else {
        poseReifiedOrImplied(new XplusYeqC(p2[0], p2[1], p3), p4, isReified);
      }
      return true;
    }
    if (p1[0] == -1 && p1[1] == -1) {
      poseReifiedOrImplied(new XplusYeqC(p2[0], p2[1], -p3), p4, isReified);
      return true;
    }
    return false;
  }

  private void intLinReifNe(int[] p1, IntVar[] p2, int p3, IntVar p4, boolean isReified) {
    if (p1.length == 1 && p1[0] == 1) {
      handleSingleVarNe(p2[0], p3, p4, isReified);
    } else if (p1.length == 1 && p1[0] == -1) {
      handleSingleVarNe(p2[0], -p3, p4, isReified);
    } else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
      handleTwoVarNe(p2[0], p2[1], p3, p4, isReified, false);
    } else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
      handleTwoVarNe(p2[1], p2[0], p3, p4, isReified, true);
    } else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
      poseReifiedOrImplied(new Not(new XplusYeqC(p2[0], p2[1], p3)), p4, isReified);
    } else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
      poseReifiedOrImplied(new Not(new XplusYeqC(p2[0], p2[1], -p3)), p4, isReified);
    } else if (allWeightsOne(p1)) {
      poseSumBoolOrIntReified(p2, "!=", p3, p4, isReified);
    } else if (allWeightsMinusOne(p1)) {
      poseSumBoolOrIntReified(p2, "!=", -p3, p4, isReified);
    } else {
      poseReifiedOrImplied(new LinearInt(p2, p1, "!=", p3), p4, isReified);
    }
  }

  private void intLinReifLe(int[] p1, IntVar[] p2, int p3, IntVar p4, boolean isReified) {
    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
      handleIntLinReifLeTwoVarsOneMinusOne(p2[0], p2[1], p3, p4, isReified, false);
      return;
    }
    if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
      handleIntLinReifLeTwoVarsOneMinusOne(p2[1], p2[0], p3, p4, isReified, true);
      return;
    }
    if (p1.length == 1 && p1[0] == 1) {
      poseReifiedOrImplied(new XlteqC(p2[0], p3), p4, isReified);
      return;
    }
    if (p1.length == 1 && p1[0] == -1) {
      poseReifiedOrImplied(new XgteqC(p2[0], -p3), p4, isReified);
      return;
    }
    if (boolSum(p2) && p3 == 0 && allPositive(p1)) {
      // very special case: positive weighted sum of 0/1 variables <= 0 =>  (all p2's zero <=>
      // p4)
      if (isReified) {
        if (support.options.useSat()) {
          sat.generateAllZeroReif(support.unique(p2), p4);
        } else {
          support.pose(new Not(new OrBoolVector(support.unique(p2), p4)));
        }
      } else {
        // This case doesn't exist in _imp version
        support.pose(new Implies(p4, new LinearInt(p2, p1, "<=", p3)));
      }
    } else if (boolSum(p2) && p3 == 0 && allNonPositive(p1)) {
      // very special case: negative weighted sum of 0/1 variables <= 0 =>  (p4 = 1)
      if (isReified) {
        p4.domain.inValue(store.level, p4, 1);
      } else {
        // This case doesn't exist in _imp version
        support.pose(new Implies(p4, new LinearInt(p2, p1, "<=", p3)));
      }
    } else if (allWeightsOne(p1)) {
      IntVar t = support.dictionary.getConstant(p3);
      if (boolSum(p2)) {
        if (isReified && p3 == 0) {
          // all p2's zero <=> p4
          if (support.options.useSat()) {
            sat.generateAllZeroReif(support.unique(p2), p4);
          } else {
            support.pose(new Not(new OrBoolVector(support.unique(p2), p4)));
          }
        } else {
          poseReifiedOrImplied(new SumBool(p2, "<=", t), p4, isReified);
        }
      } else {
        if (isReified) {
          poseReifiedOrImplied(new SumInt(p2, "<=", t), p4, isReified);
        } else {
          if (p2.length == 2) {
            support.pose(new Implies(p4, new XplusYlteqZ(p2[0], p2[1], t)));
          } else {
            poseReifiedOrImplied(new SumInt(p2, "<=", t), p4, isReified);
          }
        }
      }
    } else if (allWeightsMinusOne(p1)) {
      poseSumBoolOrIntReified(p2, ">=", -p3, p4, isReified);
    } else {
      int posLe = sumLePossible(p1, p3);
      int posGe = sumGePossible(p1, p3);
      if (posLe > -1) {
        IntVar[] vect = createVectorExcluding(p2, posLe);
        if (boolSum(vect)) {
          poseReifiedOrImplied(new SumBool(vect, "<=", p2[posLe]), p4, isReified);
        } else if (vect.length == 2) {
          poseReifiedOrImplied(new XplusYlteqZ(vect[0], vect[1], p2[posLe]), p4, isReified);
        } else {
          poseReifiedOrImplied(new SumInt(vect, "<=", p2[posLe]), p4, isReified);
        }
      } else if (posGe > -1) {
        IntVar[] vect = createVectorExcluding(p2, posGe);
        poseSumBoolOrIntReified(vect, ">=", p2[posGe], p4, isReified);
      } else {
        poseReifiedOrImplied(new LinearInt(p2, p1, "<=", p3), p4, isReified);
      }
    }
  }

  void int_lin_relation(int operation, SimpleNode node) throws FailException {

    int[] p1 = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] p2 = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int p3 = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

    Integer s = evaluateConstantLinearTerm(p1, p2);
    boolean p2Fixed = s != null;

    switch (operation) {
      case Support.EQ:
        int_lin_relationEq(p1, p2, p3, s, p2Fixed);
        break;
      case Support.NE:
        int_lin_relationNe(p1, p2, p3, s, p2Fixed);
        break;
      case Support.LT:
        int_lin_relationLt(p1, p2, p3, s, p2Fixed);
        break;
      case Support.LE:
        int_lin_relationLe(p1, p2, p3, s, p2Fixed);
        break;
      default:
        throw new IllegalArgumentException(
            "%% ERROR: Relation in linear constraint not supported.");
    }
  }

  private void int_lin_relationEq(int[] p1, IntVar[] p2, int p3, Integer s, boolean p2Fixed)
      throws FailException {
    if (p2Fixed) {
      if (s == p3) {
        return;
      }
      throw Store.failException;
    }
    if (p1.length == 1) {
      support.pose(new XmulCeqZ(p2[0], p1[0], support.dictionary.getConstant(p3)));
      return;
    }
    if (p1.length == 2 && poseIntLinRelationEqTwoVars(p1, p2, p3)) {
      return;
    }
    if (support.domainConsistency && !support.options.getBoundConsistency()) {
      int_lin_relationEqDomainConsistency(p1, p2, p3);
      return;
    }
    if (int_lin_relationEqSpecial3(p1, p2, p3)) {
      return;
    }
    if (int_lin_relationEqSpecial2(p1, p2, p3)) {
      return;
    }
    if (int_lin_relationEqXplusYeqZ(p1, p2, p3)) {
      return;
    }
    int_lin_relationEqDefault(p1, p2, p3);
  }

  private boolean poseIntLinRelationEqTwoVars(int[] p1, IntVar[] p2, int p3) {
    if (p1[0] == 1 && p1[1] == -1) {
      if (p3 != 0) {
        support.pose(new XplusCeqZ(p2[1], p3, p2[0]));
      } else {
        support.pose(new XeqY(p2[1], p2[0]));
      }
      return true;
    }
    if (p1[0] == -1 && p1[1] == 1) {
      if (p3 != 0) {
        support.pose(new XplusCeqZ(p2[0], p3, p2[1]));
      } else {
        support.pose(new XeqY(p2[0], p2[1]));
      }
      return true;
    }
    if (p1[0] == 1 && p1[1] == 1) {
      support.pose(new XplusYeqC(p2[0], p2[1], p3));
      return true;
    }
    if (p1[0] == -1 && p1[1] == -1) {
      support.pose(new XplusYeqC(p2[0], p2[1], p3 == 0 ? p3 : -p3));
      return true;
    }
    return false;
  }

  private void int_lin_relationEqDomainConsistency(int[] p1, IntVar[] p2, int p3) {
    int pos = sumPossible(p1);
    if (pos > -1) {
      IntVar[] vect = createVectorExcluding(p2, pos);
      if (boolSum(vect)) {
        if (p3 == 0) {
          support.pose(new SumBool(vect, "==", p2[pos]));
        } else {
          IntVar tmp = new IntVar(store, 0, IntDomain.MAX_INT);
          support.pose(new SumBool(vect, "==", tmp));
          support.pose(new XplusCeqZ(p2[pos], p3, tmp));
        }
        return;
      }
    }
    support.pose(new LinearIntDom(p2, p1, "==", p3));
  }

  private boolean int_lin_relationEqSpecial3(int[] p1, IntVar[] p2, int p3) {
    if (p3 != 0 || p1.length != 3) {
      return false;
    }
    if ((p1[0] == -1 && p1[1] == -1 && p1[2] == 1) || (p1[0] == 1 && p1[1] == 1 && p1[2] == -1)) {
      support.pose(new XplusYeqZ(p2[0], p2[1], p2[2]));
      return true;
    }
    return false;
  }

  private boolean int_lin_relationEqSpecial2(int[] p1, IntVar[] p2, int p3) {
    if (p3 != 0 || p1.length != 2) {
      return false;
    }
    if (p1[0] == 1) {
      support.pose(new XmulCeqZ(p2[1], -p1[1], p2[0]));
      return true;
    }
    if (p1[1] == 1) {
      support.pose(new XmulCeqZ(p2[0], -p1[0], p2[1]));
      return true;
    }
    if (p1[0] == -1) {
      support.pose(new XmulCeqZ(p2[1], p1[1], p2[0]));
      return true;
    }
    if (p1[1] == -1) {
      support.pose(new XmulCeqZ(p2[0], p1[0], p2[1]));
      return true;
    }
    return false;
  }

  private boolean int_lin_relationEqXplusYeqZ(int[] p1, IntVar[] p2, int p3) {
    if (p3 != 0 || p1.length != 3) {
      return false;
    }
    if (!((p1[0] == 1 && p1[1] == -1 && p1[2] == -1)
        || (p1[0] == -1 && p1[1] == 1 && p1[2] == 1))) {
      return false;
    }
    if (paramZero(p2[1])) {
      support.pose(new XeqY(p2[2], p2[0]));
    } else if (paramZero(p2[2])) {
      support.pose(new XeqY(p2[1], p2[0]));
    } else {
      support.pose(new XplusYeqZ(p2[1], p2[2], p2[0]));
    }
    return true;
  }

  private void int_lin_relationEqDefault(int[] p1, IntVar[] p2, int p3) {
    int pos = sumPossible(p1);
    if (pos > -1) {
      if (p3 == 0) {
        IntVar[] vect = createVectorExcluding(p2, pos);
        poseSumEq(vect, p2[pos]);
      } else {
        IntVar[] vect = new IntVar[p1.length];
        IntVar v = p2[pos];
        int constant = p1[pos] == 1 ? p3 : -p3;
        int n = 0;
        for (int i = 0; i < p2.length; i++) {
          vect[n++] = (i != pos) ? p2[i] : support.dictionary.getConstant(constant);
        }
        poseSumEq(vect, v);
      }
      return;
    }
    if (allWeightsOne(p1)) {
      poseSumBoolOrInt(p2, "==", support.dictionary.getConstant(p3));
    } else if (allWeightsMinusOne(p1)) {
      poseSumBoolOrInt(p2, "==", support.dictionary.getConstant(-p3));
    } else if (p2.length < 100) {
      support.pose(new LinearInt(p2, p1, "==", p3));
    } else {
      support.pose(new SumWeight(p2, p1, p3));
    }
  }

  private void int_lin_relationNe(int[] p1, IntVar[] p2, int p3, Integer s, boolean p2Fixed)
      throws FailException {
    if (p2Fixed) {
      if (s != p3) {
        return;
      }
      throw Store.failException;
    }
    if (p1.length == 1 && p1[0] == 1) {
      p2[0].domain.inComplement(store.level, p2[0], p3);
      return;
    }
    if (p1.length == 1 && p1[0] == -1) {
      p2[0].domain.inComplement(store.level, p2[0], -p3);
      return;
    }
    if (p1.length == 2 && p3 == 0 && ((p1[0] == 1 && p1[1] == -1) || (p1[0] == -1 && p1[1] == 1))) {
      if (p2[0].max() >= p2[1].min() && p2[0].min() <= p2[1].max()) {
        support.pose(new XneqY(p2[0], p2[1]));
      }
      return;
    }
    int pos = sumPossible(p1, p3);
    if (pos > -1) {
      IntVar[] vect = createVectorExcluding(p2, pos);
      poseSumBoolOrInt(vect, "!=", p2[pos]);
    } else if (boolSum(p2) && allWeightsOne(p1)) {
      support.pose(new SumBool(p2, "!=", support.dictionary.getConstant(p3)));
    } else {
      support.pose(new LinearInt(p2, p1, "!=", p3));
    }
  }

  private void int_lin_relationLt(int[] p1, IntVar[] p2, int p3, Integer s, boolean p2Fixed)
      throws FailException {
    if (p2Fixed) {
      if (s < p3) {
        return;
      }
      throw Store.failException;
    }
    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0) {
      support.pose(new XltY(p2[0], p2[1]));
      return;
    }
    if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0) {
      support.pose(new XltY(p2[1], p2[0]));
      return;
    }
    int posLe = sumLePossible(p1, p3);
    int posGe = sumGePossible(p1, p3);
    if (posLe > -1) {
      IntVar[] vect = createVectorExcluding(p2, posLe);
      poseSumBoolOrInt(vect, "<", p2[posLe]);
    } else if (posGe > -1) {
      IntVar[] vect = createVectorExcluding(p2, posGe);
      poseSumBoolOrInt(vect, ">", p2[posGe]);
    } else {
      support.pose(new LinearInt(p2, p1, "<", p3));
    }
  }

  private void int_lin_relationLe(int[] p1, IntVar[] p2, int p3, Integer s, boolean p2Fixed)
      throws FailException {
    if (p2Fixed) {
      if (s <= p3) {
        return;
      }
      throw Store.failException;
    }
    if (p1.length == 1) {
      int_lin_relationLeSingleWeight(p1[0], p2[0], p3);
      return;
    }
    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0) {
      support.pose(new XlteqY(p2[0], p2[1]));
      return;
    }
    if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0) {
      support.pose(new XlteqY(p2[1], p2[0]));
      return;
    }
    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
      support.pose(new XplusClteqZ(p2[0], -p3, p2[1]));
      return;
    }
    if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
      support.pose(new XplusClteqZ(p2[1], -p3, p2[0]));
      return;
    }
    if (allWeightsOne(p1)) {
      IntVar t = support.dictionary.getConstant(p3);
      if (boolSum(p2)) {
        support.pose(p2.length == 2 ? new XplusYlteqZ(p2[0], p2[1], t) : new SumBool(p2, "<=", t));
      } else {
        support.pose(p2.length == 2 ? new XplusYlteqZ(p2[0], p2[1], t) : new SumInt(p2, "<=", t));
      }
      return;
    }
    if (allWeightsMinusOne(p1)) {
      poseSumBoolOrInt(p2, ">=", support.dictionary.getConstant(-p3));
      return;
    }
    int posLe = sumLePossible(p1, p3);
    int posGe = sumGePossible(p1, p3);
    if (posLe > -1) {
      IntVar[] vect = createVectorExcluding(p2, posLe);
      if (boolSum(vect)) {
        support.pose(new SumBool(vect, "<=", p2[posLe]));
      } else if (vect.length == 2) {
        support.pose(new XplusYlteqZ(vect[0], vect[1], p2[posLe]));
      } else {
        support.pose(new SumInt(vect, "<=", p2[posLe]));
      }
    } else if (posGe > -1) {
      IntVar[] vect = createVectorExcluding(p2, posGe);
      poseSumBoolOrInt(vect, ">=", p2[posGe]);
    } else {
      support.pose(new LinearInt(p2, p1, "<=", p3));
    }
  }

  private void int_lin_relationLeSingleWeight(int w, IntVar x, int p3) {
    if (w < 0) {
      int rhsValue = (int) Math.round(Math.ceil((float) p3 / (float) w));
      x.domain.inMin(store.level, x, rhsValue);
      if (support.options.debug()) {
        IO.println("Pruned variable " + x + " to be >= " + rhsValue);
      }
    } else {
      int rhsValue = (int) Math.round(Math.floor((float) p3 / (float) w));
      x.domain.inMax(store.level, x, rhsValue);
      if (support.options.debug()) {
        IO.println("% Pruned variable " + x + " to be <= " + rhsValue);
      }
    }
  }

  boolean allPositive(int[] ws) {
    for (int w : ws) {
      if (w < 0) {
        return false;
      }
    }
    return true;
  }

  boolean allNonPositive(int[] ws) {
    for (int w : ws) {
      if (w > 0) {
        return false;
      }
    }
    return true;
  }

  boolean allConstants(IntVar[] p) {
    boolean sat = true;
    int k = 0;
    while (sat && k < p.length) {
      sat = p[k].min() == p[k].max();
      k++;
    }
    return sat;
  }

  boolean allWeightsOne(int[] w) {
    for (int j : w) {
      if (j != 1) {
        return false;
      }
    }
    return true;
  }

  boolean allWeightsMinusOne(int[] w) {
    for (int j : w) {
      if (j != -1) {
        return false;
      }
    }
    return true;
  }

  boolean boolSum(IntVar[] vs) {
    for (IntVar v : vs) {
      if (v.min() < 0 || v.max() > 1) {
        return false;
      }
    }
    return true;
  }

  int sumPossible(int[] ws, int result) {
    if (result != 0) {
      return -1;
    }
    return sumPossible(ws);
  }

  int sumPossible(int[] ws) {

    int one = 0;
    int minusOne = 0;
    int lastOnePosition = -1;
    int lastMinusOnePosition = -1;

    for (int i = 0; i < ws.length; i++) {
      if (ws[i] == 1) {
        one++;
        lastOnePosition = i;
      } else if (ws[i] == -1) {
        minusOne++;
        lastMinusOnePosition = i;
      }
    }

    if (one == 1 && minusOne == ws.length - 1) {
      return lastOnePosition;
    } else if (minusOne == 1 && one == ws.length - 1) {
      return lastMinusOnePosition;
    } else {
      return -1;
    }
  }

  /**
   * Checks if the weight array with a zero result allows a sum-le decomposition. Returns the
   * position of the single -1 weight when all others are 1, or -1 if not possible.
   */
  int sumLePossible(int[] ws, int result) {
    if (result != 0) {
      return -1;
    }
    return sumLeGePosition(ws, -1, 1);
  }

  /**
   * Checks if the weight array with a zero result allows a sum-ge decomposition. Returns the
   * position of the single 1 weight when all others are -1, or -1 if not possible.
   */
  int sumGePossible(int[] ws, int result) {
    if (result != 0) {
      return -1;
    }
    return sumLeGePosition(ws, 1, -1);
  }

  /**
   * Returns the position of the single occurrence of {@code singleWeight} in the array, provided
   * all other elements equal {@code otherWeight}. Returns -1 if the pattern does not match.
   */
  private int sumLeGePosition(int[] ws, int singleWeight, int otherWeight) {
    int singleCount = 0;
    int otherCount = 0;
    int lastSinglePosition = -1;

    for (int i = 0; i < ws.length; i++) {
      if (ws[i] == singleWeight) {
        singleCount++;
        lastSinglePosition = i;
      } else if (ws[i] == otherWeight) {
        otherCount++;
      }
    }

    if (singleCount == 1 && otherCount == ws.length - 1) {
      return lastSinglePosition;
    }
    return -1;
  }

  boolean paramZero(IntVar v) {
    return v.singleton() && v.value() == 0;
  }

  boolean binaryVar(IntVar v) {
    return v.min() >= 0 && v.max() <= 1;
  }

  /**
   * Poses a constraint as either reified or implied based on the isReified flag.
   *
   * @param c the primitive constraint to pose
   * @param boolVar the boolean variable for reification/implication
   * @param isReified true to use Reified constraint, false to use Implies constraint
   */
  private void poseReifiedOrImplied(PrimitiveConstraint c, IntVar boolVar, boolean isReified) {
    if (isReified) {
      support.pose(new Reified(c, boolVar));
    } else {
      support.pose(new Implies(boolVar, c));
    }
  }

  /**
   * Poses a SumBool or SumInt constraint as either reified or implied.
   *
   * @param vars the variables to sum
   * @param op the comparison operator
   * @param result the result variable
   * @param boolVar the boolean variable for reification/implication
   * @param isReified true to use Reified constraint, false to use Implies constraint
   */
  private void poseSumBoolOrIntReified(
      IntVar[] vars, String op, IntVar result, IntVar boolVar, boolean isReified) {
    if (boolSum(vars)) {
      poseReifiedOrImplied(new SumBool(vars, op, result), boolVar, isReified);
    } else {
      poseReifiedOrImplied(new SumInt(vars, op, result), boolVar, isReified);
    }
  }

  /**
   * Poses a SumBool or SumInt constraint as either reified or implied with a constant result.
   *
   * @param vars the variables to sum
   * @param op the comparison operator
   * @param constant the constant result value
   * @param boolVar the boolean variable for reification/implication
   * @param isReified true to use Reified constraint, false to use Implies constraint
   */
  private void poseSumBoolOrIntReified(
      IntVar[] vars, String op, int constant, IntVar boolVar, boolean isReified) {
    IntVar result = support.dictionary.getConstant(constant);
    poseSumBoolOrIntReified(vars, op, result, boolVar, isReified);
  }

  /**
   * Evaluates a linear term if all variables are constants.
   *
   * @param weights the weights array
   * @param vars the variables array
   * @return the computed sum if all variables are constants, or null if not all are constants
   */
  private Integer evaluateConstantLinearTerm(int[] weights, IntVar[] vars) {
    if (!allConstants(vars)) {
      return null;
    }
    int sum = 0;
    for (int i = 0; i < vars.length; i++) {
      sum += vars[i].min() * weights[i];
    }
    return sum;
  }

  /**
   * Handles the two-variable NE case: x - y != c or y - x != c.
   *
   * @param x first variable
   * @param y second variable
   * @param c constant value
   * @param boolVar boolean variable for reification/implication
   * @param isReified true for reified, false for implied
   * @param swapped true if coefficients are swapped (y - x), false if (x - y)
   */
  private void handleTwoVarNe(
      IntVar x, IntVar y, int c, IntVar boolVar, boolean isReified, boolean swapped) {
    if (c == 0) {
      if (isReified && binaryVar(x) && binaryVar(y)) {
        // (x != y) <=> b == x xor y = b
        support.pose(new XorBool(new IntVar[] {x, y}, boolVar));
      } else if (x.singleton()) {
        poseXneqCReifiedOrImplied(y, x.value(), boolVar, isReified);
      } else if (y.singleton()) {
        poseXneqCReifiedOrImplied(x, y.value(), boolVar, isReified);
      } else {
        poseReifiedOrImplied(new XneqY(x, y), boolVar, isReified);
      }
    } else {
      IntVar first = swapped ? y : x;
      IntVar second = swapped ? x : y;
      poseReifiedOrImplied(new Not(new XplusCeqZ(second, c, first)), boolVar, isReified);
    }
  }

  /**
   * Handles the single-variable NE case: x != c.
   *
   * @param var the variable
   * @param value the constant value
   * @param boolVar the boolean variable for reification/implication
   * @param isReified true for reified, false for implied
   */
  private void handleSingleVarNe(IntVar var, int value, IntVar boolVar, boolean isReified) {
    if (isReified) {
      if (var.domain.isIntersecting(value, value)) {
        support.pose(support.fzXneqCreified(var, value, boolVar));
      } else {
        boolVar.domain.inValue(store.level, boolVar, 1);
      }
    } else {
      support.pose(support.fzXneqCimplied(var, value, boolVar));
    }
  }

  /**
   * Poses XneqC constraint as either reified or implied.
   *
   * @param var the variable
   * @param value the constant value
   * @param boolVar the boolean variable for reification/implication
   * @param isReified true to use reified, false to use implied
   */
  private void poseXneqCReifiedOrImplied(IntVar var, int value, IntVar boolVar, boolean isReified) {
    if (isReified) {
      support.pose(support.fzXneqCreified(var, value, boolVar));
    } else {
      support.pose(support.fzXneqCimplied(var, value, boolVar));
    }
  }

  /**
   * Poses a sum-equality constraint, choosing the best variant for the given variables.
   *
   * @param vars the variables to sum
   * @param result the result variable
   */
  private void poseSumEq(IntVar[] vars, IntVar result) {
    if (boolSum(vars)) {
      support.pose(new SumBool(vars, "==", result));
    } else if (vars.length == 2) {
      support.pose(new XplusYeqZ(vars[0], vars[1], result));
    } else if (vars.length < 100) {
      support.pose(new SumInt(vars, "==", result));
    } else {
      support.pose(new Sum(vars, result));
    }
  }

  /**
   * Creates a new array by excluding the element at the given index.
   *
   * @param vars the source array
   * @param excludeIndex the index to exclude
   * @return a new array without the element at excludeIndex
   */
  private IntVar[] createVectorExcluding(IntVar[] vars, int excludeIndex) {
    IntVar[] vect = new IntVar[vars.length - 1];
    int n = 0;
    for (int i = 0; i < vars.length; i++) {
      if (i != excludeIndex) {
        vect[n++] = vars[i];
      }
    }
    return vect;
  }

  /**
   * Poses a SumBool or SumInt constraint directly (non-reified).
   *
   * @param vars the variables to sum
   * @param op the comparison operator
   * @param result the result variable
   */
  private void poseSumBoolOrInt(IntVar[] vars, String op, IntVar result) {
    if (boolSum(vars)) {
      support.pose(new SumBool(vars, op, result));
    } else {
      support.pose(new SumInt(vars, op, result));
    }
  }
}
