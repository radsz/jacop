/*
 * BoolConstraints.java This file is part of JaCoP.
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

import java.util.ArrayList;
import java.util.List;
import org.jacop.constraints.AndBool;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Implies;
import org.jacop.constraints.OrBool;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.XplusYgtC;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.satwrapper.SatTranslation;

/**
 * Generation of boolean constraints in flatzinc.
 *
 * @author Krzysztof Kuchcinski
 */
class BoolConstraints implements ParserTreeConstants {

  final Store store;
  final SatTranslation sat;
  final Support support;
  boolean reified;
  boolean implied;

  public BoolConstraints(Support support) {
    this.support = support;
    this.store = support.store;
    this.sat = support.sat;
  }

  void gen_array_bool_and(SimpleNode node) {

    IntVar[] a1 = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

    if (support.options.useSat()) {
      sat.generateAnd(a1, v);
    } else if (allVarOne(a1)) {
      v.domain.inValue(store.level, v, 1);
    } else if (atLeastOneVarZero(a1)) {
      v.domain.inValue(store.level, v, 0);
    } else {
      support.poseDc(new AndBool(a1, v));
    }
  }

  void gen_array_bool_and_imp(SimpleNode node) {

    IntVar[] a1 = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

    if (atLeastOneVarZero(a1)) {
      v.domain.inValue(store.level, v, 0);
    } else if (!allVarOne(a1)) {
      support.pose(new Implies(v, new AndBoolVector(a1, support.dictionary.getConstant(1))));
    }
  }

  void gen_bool_and(SimpleNode node) {

    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    IntVar v3 = support.getVariable(p3);

    if (support.options.useSat()) {
      sat.generateAnd(new IntVar[] {v1, v2}, v3);
    } else {
      support.pose(new AndBoolSimple(v1, v2, v3));
    }
  }

  void gen_bool_and_imp(SimpleNode node) {

    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    IntVar v3 = support.getVariable(p3);

    support.pose(new Implies(v3, new AndBoolSimple(v1, v2, support.dictionary.getConstant(1))));
  }

  void gen_array_bool_or(SimpleNode node) {
    IntVar[] a1 = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

    if (support.options.useSat()) {
      sat.generateOr(a1, v);
    } else {
      if (v.singleton(1)) {
        if (a1.length == 2) {
          support.pose(new XplusYgtC(a1[0], a1[1], 0));
        } else {
          support.pose(new SumBool(a1, ">=", v));
        }
      } else if (allVarZero(a1)) {
        v.domain.inValue(store.level, v, 0);
      } else if (atLeastOneVarOne(a1)) {
        v.domain.inValue(store.level, v, 1);
      } else {
        support.poseDc(new OrBool(a1, v));
      }
    }
  }

  void gen_array_bool_or_imp(SimpleNode node) {

    IntVar[] a1 = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

    if (v.singleton(1)) {
      if (a1.length == 2) {
        support.pose(new XplusYgtC(a1[0], a1[1], 0));
      } else {
        support.pose(new SumBool(a1, ">=", v));
      }
    } else if (allVarZero(a1)) {
      v.domain.inValue(store.level, v, 0);
    } else if (!atLeastOneVarOne(a1)) {
      support.pose(new Implies(v, new OrBoolVector(a1, support.dictionary.getConstant(1))));
    }
  }

  void gen_array_bool_xor(SimpleNode node) {

    SimpleNode p1 = (SimpleNode) node.jjtGetChild(0);
    IntVar[] a1 = support.getVarArray(p1);

    if (support.options.useSat()) {
      sat.generateXor(a1, support.dictionary.getConstant(1));
    } else {
      support.pose(new XorBool(a1, support.dictionary.getConstant(1)));
    }
  }

  void gen_array_bool_xor_imp(SimpleNode node) {

    SimpleNode p1 = (SimpleNode) node.jjtGetChild(0);
    IntVar[] a1 = support.getVarArray(p1);
    IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

    support.pose(new Implies(v, new XorBool(a1, support.dictionary.getConstant(1))));
  }

  void gen_bool_not(SimpleNode node) {

    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);

    if (support.options.useSat()) {
      sat.generateNot(v1, v2);
    } else {
      support.pose(new XneqY(v1, v2));
    }
  }

  void gen_bool_or(SimpleNode node) {

    IntVar v1 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar v2 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    if (support.options.useSat()) {
      sat.generateOr(new IntVar[] {v1, v2}, v3);
    } else {
      support.poseDc(new OrBool(new IntVar[] {v1, v2}, v3));
    }
  }

  void gen_bool_or_imp(SimpleNode node) {

    IntVar v1 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar v2 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    // r -> (a \/ b) is the clause a \/ b \/ not r, i.e. a + b >= r
    support.pose(new SumBool(new IntVar[] {v1, v2}, ">=", v3));
  }

  void gen_bool_xor(SimpleNode node) {

    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    IntVar v3 = support.getVariable(p3);

    if (support.options.useSat()) {
      sat.generateNeqReif(v1, v2, v3);
    } else if (v1.max() == 0) {
      support.pose(new XeqY(v2, v3));
    } else if (v2.max() == 0) {
      support.pose(new XeqY(v1, v3));
    } else if (v1.min() == 1) {
      support.pose(new XneqY(v2, v3));
    } else if (v2.min() == 1) {
      support.pose(new XneqY(v1, v3));
    } else if (v3.max() == 0) {
      support.pose(new XeqY(v1, v2));
    } else if (v3.min() == 1) {
      support.pose(new XneqY(v1, v2));
    } else {
      support.pose(new XorBool(new IntVar[] {v1, v2}, v3));
    }
  }

  void gen_bool_xor_imp(SimpleNode node) {

    IntVar v1 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar v2 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    support.pose(new Implies(v3, new XneqY(v1, v2)));
  }

  void gen_bool_clause(SimpleNode node) {
    reified = false;
    implied = false;
    clause_generation(node);
  }

  void gen_bool_clause_reif(SimpleNode node) {
    reified = true;
    implied = false;
    clause_generation(node);
  }

  void gen_bool_clause_imp(SimpleNode node) {
    reified = false;
    implied = true;
    clause_generation(node);
  }

  void gen_bool2int(SimpleNode node) {
    // the integer variable is an alias of the Boolean one, so there is usually nothing to post;
    // a second bool2int of the same integer variable joins two Booleans, which the alias table
    // cannot hold, so their equality is posted
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    if (b != x) {
      support.pose(new XeqY(b, x));
    }
  }

  void clause_generation(SimpleNode node) {

    IntVar[] a1 = support.unique(support.getVarArray((SimpleNode) node.jjtGetChild(0)));
    IntVar[] a2 = support.unique(support.getVarArray((SimpleNode) node.jjtGetChild(1)));

    if (clauseHasSameVarInBothSides(a1, a2)) {
      clauseSatisfied(node);
      return;
    }
    if (a1.length == 0 && a2.length == 0) {
      clauseFalse(node);
      return;
    }

    if (!reified && !implied && a2.length == 0) {
      restrictToClauseValues(a1);
    }

    if (support.options.useSat() && !implied) {
      poseSatClause(node, a1, a2);
      return;
    }

    clauseGenerationCp(node, a1, a2);
  }

  /**
   * A clause b1 \/ ... \/ bn whose literals all imply x = v1, ..., x = vn for one variable x
   * (int_eq_reif or int_eq_imp) restricts x to {v1, ..., vn}, for example leaf \/ unused written as
   * (x = 10) \/ (x = 11). The clause on its own only fails once x takes another value.
   */
  private void restrictToClauseValues(IntVar[] a1) {
    if (a1.length < 2) {
      return;
    }
    for (IntVar x : candidateVariables(a1[0])) {
      IntDomain values = new IntervalDomain();
      boolean all = true;
      for (IntVar b : a1) {
        if (b.max() == 0) {
          continue;
        }
        Integer v = impliedValue(b, x);
        if (v == null) {
          all = false;
          break;
        }
        values.unionAdapt(v, v);
      }
      if (all) {
        x.domain.in(store.level, x, values);
        return;
      }
    }
  }

  private List<IntVar> candidateVariables(IntVar b) {
    List<IntVar> result = new ArrayList<>(support.reif.variablesOf(b));
    result.addAll(support.imply.variablesOf(b));
    return result;
  }

  private Integer impliedValue(IntVar b, IntVar x) {
    Integer v = support.reif.valueImpliedBy(b, x);
    return v != null ? v : support.imply.valueImpliedBy(b, x);
  }

  private boolean clauseHasSameVarInBothSides(IntVar[] a1, IntVar[] a2) {
    for (IntVar v1 : a1) {
      for (IntVar v2 : a2) {
        if (v1.equals(v2)) {
          return true;
        }
      }
    }
    return false;
  }

  /** A clause that always holds: its reification variable is true, an implication is free. */
  private void clauseSatisfied(SimpleNode node) {
    if (reified) {
      setReifiedImpliedResult(node, 1);
    }
  }

  /** A clause that never holds: its reification or implication variable is false. */
  private void clauseFalse(SimpleNode node) {
    if (reified || implied) {
      setReifiedImpliedResult(node, 0);
    } else {
      throw Store.failException;
    }
  }

  private void setReifiedImpliedResult(SimpleNode node, int value) {
    IntVar r = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    r.domain.inValue(store.level, r, value);
  }

  private void poseSatClause(SimpleNode node, IntVar[] a1, IntVar[] a2) {
    if (reified) {
      IntVar r = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
      sat.generateClauseReif(a1, a2, r);
    } else {
      sat.generateClause(a1, a2);
    }
  }

  private void clauseGenerationCp(SimpleNode node, IntVar[] a1, IntVar[] a2) {
    ArrayList<IntVar> a1reduced = reduceClausePositives(a1, node);
    if (a1reduced == null) {
      return;
    }

    ArrayList<IntVar> a2reduced = reduceClauseNegatives(a2, node);
    if (a2reduced == null) {
      return;
    }

    if (a1reduced.isEmpty() && a2reduced.isEmpty()) {
      clauseFalse(node);
      return;
    }

    PrimitiveConstraint c = buildClauseConstraint(a1reduced, a2reduced, node);
    if (c == null) {
      return;
    }

    if (reified) {
      IntVar r = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
      support.pose(new Reified(c, r));
    } else if (implied) {
      IntVar r = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
      support.pose(new Implies(r, c));
    } else {
      support.pose(c);
    }
  }

  /**
   * Returns reduced list, or null if the clause is satisfied (see clauseSatisfied; caller should
   * return).
   */
  private ArrayList<IntVar> reduceClausePositives(IntVar[] a1, SimpleNode node) {
    ArrayList<IntVar> a1reduced = new ArrayList<>();
    for (IntVar v : a1) {
      if (v.min() == 1) {
        clauseSatisfied(node);
        return null;
      }
      if (v.max() != 0) {
        a1reduced.add(v);
      }
    }
    return a1reduced;
  }

  /**
   * Returns reduced list, or null if the clause is satisfied (see clauseSatisfied; caller should
   * return).
   */
  private ArrayList<IntVar> reduceClauseNegatives(IntVar[] a2, SimpleNode node) {
    ArrayList<IntVar> a2reduced = new ArrayList<>();
    for (IntVar intVar : a2) {
      if (intVar.max() == 0) {
        clauseSatisfied(node);
        return null;
      }
      if (intVar.min() != 1) {
        a2reduced.add(intVar);
      }
    }
    return a2reduced;
  }

  /**
   * Builds the clause constraint from reduced arrays. Returns null if constraint was posed directly
   * (e.g. reified OrBool) and caller should return.
   */
  private PrimitiveConstraint buildClauseConstraint(
      ArrayList<IntVar> a1reduced, ArrayList<IntVar> a2reduced, SimpleNode node) {
    if (a1reduced.isEmpty()) {
      return new AndBool(a2reduced, support.dictionary.getConstant(0)).decompose(store).getFirst();
    }
    if (a2reduced.isEmpty()) {
      if (reified) {
        IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        support.poseDc(new OrBool(a1reduced, b));
        return null;
      }
      IntVar r = support.dictionary.getConstant(1);
      return new OrBool(a1reduced, r).decompose(store).getFirst();
    }
    if (a1reduced.size() == 1 && a2reduced.size() == 1) {
      return new XlteqY(a2reduced.getFirst(), a1reduced.getFirst());
    }
    return new BoolClause(a1reduced, a2reduced);
  }

  boolean allVarOne(IntVar[] w) {
    for (IntVar intVar : w) {
      if (intVar.min() != 1) {
        return false;
      }
    }
    return true;
  }

  boolean allVarZero(IntVar[] w) {
    for (IntVar intVar : w) {
      if (intVar.max() != 0) {
        return false;
      }
    }
    return true;
  }

  boolean atLeastOneVarZero(IntVar[] w) {
    for (IntVar intVar : w) {
      if (intVar.max() == 0) {
        return true;
      }
    }
    return false;
  }

  boolean atLeastOneVarOne(IntVar[] w) {
    for (IntVar intVar : w) {
      if (intVar.min() == 1) {
        return true;
      }
    }
    return false;
  }
}
