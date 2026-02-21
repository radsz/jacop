/*
 * GlobalConstraints.java
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
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.AllEqual;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Among;
import org.jacop.constraints.AmongVar;
import org.jacop.constraints.And;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Conditional;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.CountValuesBounds;
import org.jacop.constraints.CountVar;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Decreasing;
import org.jacop.constraints.GCC;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.IfThenElseBool;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Increasing;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.Max;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SeqPrecedeChain;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.SoftAlldifferent;
import org.jacop.constraints.SoftGCC;
import org.jacop.constraints.Stretch;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.ValuePrecede;
import org.jacop.constraints.Values;
import org.jacop.constraints.ViolationMeasure;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.CumulativeUnaryOptional;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.geost.Dbox;
import org.jacop.constraints.geost.ExternalConstraint;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.InArea;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.Shape;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.NetworkFlow;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.SimpleTable;
import org.jacop.constraints.table.Table;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PeqQ;
import org.jacop.floats.core.FloatVar;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.set.constraints.AdisjointB;
import org.jacop.set.constraints.AeqB;
import org.jacop.set.constraints.AeqS;
import org.jacop.set.core.SetVar;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;

/**
 * Generation of global constraints in flatzinc.
 *
 * @author Krzysztof Kuchcinski
 */
class GlobalConstraints implements ParserTreeConstants {

  final Store store;
  final Support support;
  final Comparator<ArrayList<Integer>> rowComparator =
      (o1, o2) -> {
        for (int i = 0; i < o1.size(); i++) {
          if (o1.get(i) > o2.get(i)) {
            return 1;
          } else if (o1.get(i) < o2.get(i)) {
            return -1;
          }
        }
        return 0; // all equal
      };
  boolean useDisjunctions;
  boolean useCumulativeUnary;
  ArrayList<Pair> duplicates;

  public GlobalConstraints(Support support) {
    this.store = support.store;
    this.support = support;
  }

  /**
   * Filters out entries where the boolean variable is false (max == 0) from parallel arrays.
   *
   * @param b the boolean variable array
   * @param x the corresponding value array
   * @return a pair of filtered arrays: [filteredB, filteredX]
   */
  private static IntVar[][] filterFalseEntries(IntVar[] b, IntVar[] x) {
    ArrayList<IntVar> bn = new ArrayList<>();
    ArrayList<IntVar> xn = new ArrayList<>();
    for (int i = 0; i < b.length; i++) {
      if (b[i].max() != 0) {
        bn.add(b[i]);
        xn.add(x[i]);
      }
    }
    return new IntVar[][] {bn.toArray(new IntVar[0]), xn.toArray(new IntVar[0])};
  }

  /**
   * Checks for duplicate variables in the given array and throws a FailException if any are found.
   *
   * @param vars the array of variables to check
   */
  private static void checkForDuplicateVariables(IntVar[] vars) {
    HashSet<IntVar> varSet = new HashSet<>();
    for (IntVar value : vars) {
      if (varSet.contains(value)) {
        // problem unsatisfied since the same variables are on the list;
        // cannot get different values.
        throw Store.failException;
      } else {
        varSet.add(value);
      }
    }
  }

  void gen_jacop_cumulative(SimpleNode node) {

    IntVar[] str = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] dur = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] res = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

    IntVar[][] sdr = filterCumulativeTasks(str, dur, res);
    IntVar[] s = sdr[0];
    IntVar[] d = sdr[1];
    IntVar[] r = sdr[2];

    if (cumulativeResourceSumWithinCapacity(r, b)) {
      return;
    }

    if (s.length == 1) {
      support.pose(new XlteqY(r[0], b));
      return;
    }
    if (s.length == 0) {
      return;
    }
    if (b.max() == 1) {
      poseCumulativeUnaryBranch(s, d, r, b);
      return;
    }

    int[] minNext = computeResourceMinAndNextMin(r);
    int min = minNext[0];
    int nextMin = minNext[1];
    boolean unaryPossible =
        (min > b.max() / 2) || (nextMin > b.max() / 2 && min + nextMin > b.max());

    if (unaryPossible) {
      poseCumulativeUnaryPossible(s, d, r, b);
    } else if (allVarGround(d) && allVarGround(r)) {
      poseCumulativeGround(s, d, r, b);
    } else {
      poseCumulativeBasicWithImplied(s, d, r, b);
    }
  }

  private IntVar[][] filterCumulativeTasks(IntVar[] str, IntVar[] dur, IntVar[] res) {
    ArrayList<IntVar> start = new ArrayList<>();
    ArrayList<IntVar> duration = new ArrayList<>();
    ArrayList<IntVar> resource = new ArrayList<>();
    for (int i = 0; i < str.length; i++) {
      if (!res[i].singleton(0) && !dur[i].singleton(0)) {
        start.add(str[i]);
        duration.add(dur[i]);
        resource.add(res[i]);
      }
    }
    return new IntVar[][] {
      start.toArray(new IntVar[0]), duration.toArray(new IntVar[0]), resource.toArray(new IntVar[0])
    };
  }

  private boolean cumulativeResourceSumWithinCapacity(IntVar[] r, IntVar b) {
    int resSum = 0;
    for (IntVar v : r) {
      resSum += v.max();
    }
    return resSum <= b.min();
  }

  private void poseCumulativeUnaryBranch(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {
    if (allVarOne(d) && allVarOne(r)) {
      support.pose(new Alldiff(s));
    } else {
      support.delayedConstraints.add(new CumulativeUnary(s, d, r, b, true));
    }
  }

  private int[] computeResourceMinAndNextMin(IntVar[] r) {
    int min = Math.min(r[0].min(), r[1].min());
    int nextMin = Math.max(r[0].min(), r[1].min());
    for (int i = 2; i < r.length; i++) {
      if (r[i].min() < min) {
        nextMin = min;
        min = r[i].min();
      } else if (r[i].min() < nextMin) {
        nextMin = r[i].min();
      }
    }
    return new int[] {min, nextMin};
  }

  private void poseCumulativeUnaryPossible(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {
    if (allVarOne(d)) {
      support.pose(new Alldiff(s));
      if (!b.singleton()) {
        for (IntVar intVar : r) {
          support.pose(new XlteqY(intVar, b));
        }
      }
    } else {
      support.delayedConstraints.add(new CumulativeUnary(s, d, r, b, true));
    }
  }

  private void poseCumulativeGround(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {
    HashSet<Integer> diff = new HashSet<>();
    for (IntVar e : r) {
      diff.add(e.min());
    }
    double n = r.length;
    double k = diff.size();
    Cumulative cumul = new Cumulative(s, d, r, b);
    if (2 * n * n < n * k * Math.log10(n) / Math.log10(2.0)) {
      cumul.doQuadraticEdgeFind(true);
    }
    support.delayedConstraints.add(cumul);
    applyCumulativeImpliedOptions(s, d, r, b);
  }

  private void poseCumulativeBasicWithImplied(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {
    support.delayedConstraints.add(new CumulativeBasic(s, d, r, b));
    applyCumulativeImpliedOptions(s, d, r, b);
  }

  private void applyCumulativeImpliedOptions(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {
    String p = System.getProperty("fz_cumulative_use_disjunctions");
    if (p != null) {
      useDisjunctions = Boolean.parseBoolean(p);
    }
    p = System.getProperty("fz_cumulative_use_unary");
    if (p != null) {
      useCumulativeUnary = Boolean.parseBoolean(p);
    }
    if (useCumulativeUnary) {
      impliedCumulativeUnaryConstraints(s, d, r, b);
    }
    if (useDisjunctions) {
      impliedDisjunctionConstraints(s, d, r, b);
    }
  }

  void impliedCumulativeUnaryConstraints(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {

    int limit = b.max() / 2 + 1;

    ArrayList<IntVar> start = new ArrayList<>();
    ArrayList<IntVar> dur = new ArrayList<>();
    ArrayList<IntVar> res = new ArrayList<>();

    for (int i = 0; i < r.length; i++) {
      if (r[i].min() >= limit) {
        start.add(s[i]);
        dur.add(d[i]);
        res.add(r[i]);
      }
    }
    // use CumulativeUnary for tasks that have resource capacity greater than half of the cumulative
    // capacity bound.
    if (start.size() > 1) {
      support.delayedConstraints.add(new CumulativeUnary(start, dur, res, b, false));
    }
  }

  void impliedDisjunctionConstraints(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {

    // use pairwaise task disjunction constraints for all pairs of tasks that have sum of resource
    // capacities
    // greater than the cumulative capacity bound.
    for (int i = 0; i < s.length; i++) {
      for (int j = i + 1; j < s.length; j++) {
        if (r[i].min() + r[j].min() > b.max()) {
          if (d[i].singleton() && d[j].singleton()) {
            support.pose(
                new Or(
                    new XplusClteqZ(s[i], d[i].value(), s[j]),
                    new XplusClteqZ(s[j], d[j].value(), s[i])));
          } else {
            support.pose(
                new Or(new XplusYlteqZ(s[i], d[i], s[j]), new XplusYlteqZ(s[j], d[j], s[i])));
          }
        }
      }
    }
  }

  void gen_jacop_circuit(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));

    support.pose(new Circuit(v));

    if (support.domainConsistency
        && !support.options
            .getBoundConsistency()) { // we add additional implied constraint if domain consistency
      // is
      // required
      support.parameterListForAlldistincts.add(v);
    }
  }

  void gen_jacop_subcircuit(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    support.pose(new Subcircuit(v));

    if (support.domainConsistency
        && !support.options
            .getBoundConsistency()) { // we add additional implied constraint if domain consistency
      // is
      // required
      support.parameterListForAlldistincts.add(v);
    }
  }

  /** Returns true if variable domains are considered sparse (density <= 0.5). */
  private static boolean isSparseDomains(IntVar[] v) {
    float q = 0;
    int n = 0;
    for (IntVar intVar : v) {
      if (!intVar.singleton()) {
        q += (float) intVar.getSize() / (float) (intVar.max() - intVar.min() + 1);
        n++;
      }
    }
    return n > 0 && (q / (float) n) <= 0.5;
  }

  void gen_jacop_alldiff(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));

    if (v.length == 0 || v.length == 1) {
      return;
    }
    if (v.length == 2) {
      support.pose(new XneqY(v[0], v[1]));
      return;
    }

    checkForDuplicateVariables(v);

    IntervalDomain dom = new IntervalDomain();
    for (IntVar vv : v) {
      dom = (IntervalDomain) dom.union(vv.dom());
    }
    if (v.length > 100) {
      support.pose(new Alldiff(v));
      return;
    }
    boolean useAlldiff =
        (support.boundsConsistency || support.options.getBoundConsistency()) && !isSparseDomains(v);
    if (useAlldiff) {
      support.pose(new Alldiff(v));
    } else {
      support.parameterListForAlldistincts.add(v);
    }
  }

  void gen_jacop_softalldiff(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar s = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    int useDecomp = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    // 0 if false, 1 if true
    ViolationMeasure usedMeasure =
        useDecomp == 0 ? ViolationMeasure.VARIABLE_BASED : ViolationMeasure.DECOMPOSITION_BASED;
    SoftAlldifferent sa = new SoftAlldifferent(x, s, usedMeasure);
    support.poseDc(sa);
  }

  void gen_jacop_softgcc(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] values = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] hardCounters = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    IntVar[] soft_counters = support.getVarArray((SimpleNode) node.jjtGetChild(3));
    IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(4));

    SoftGCC sgcc =
        new SoftGCC(x, hardCounters, values, soft_counters, cost, ViolationMeasure.VALUE_BASED);
    support.poseDc(sgcc);
  }

  void gen_jacop_alldistinct(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    // we do not not pose Alldistinct directly because of possible inconsistency with its
    // initialization; we collect all vectors and pose it at the end when all constraints are posed

    checkForDuplicateVariables(v);

    support.parameterListForAlldistincts.add(v);
  }

  void gen_jacop_alldifferent_except_0(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));

    // no duplicated variables allowed in this constraint and,
    // if present, they get value 0 (the only allowed to be duplicated)
    IntVar[] xs = new IntVar[x.length];
    HashSet<IntVar> varSet = new HashSet<>();
    for (int i = 0; i < x.length; i++) {
      if (varSet.contains(x[i])) {
        IntVar tmp = new IntVar(store, 0, 0);
        x[i].domain.in(store.level, x[i], 0, 0);
        support.pose(new XeqY(x[i], tmp));
        xs[i] = tmp;
      } else {
        xs[i] = x[i];
        varSet.add(x[i]);
      }
    }

    support.pose(new AlldifferentExceptZero(xs));
  }

  void gen_jacop_alldifferent_except(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntDomain s = support.getSetLiteral(node, 1);

    // no duplicated variables allowed in this constraint and,
    // if present, they get value 0 (the only allowed to be duplicated)
    IntVar[] xs = new IntVar[x.length];
    HashSet<IntVar> varSet = new HashSet<>();
    for (int i = 0; i < x.length; i++) {
      if (varSet.contains(x[i])) {
        IntVar tmp = new IntVar(store, IntDomain.MIN_INT, IntDomain.MAX_INT);
        tmp.domain.in(store.level, tmp, s);
        support.pose(new XeqY(x[i], tmp));
        xs[i] = tmp;
      } else {
        xs[i] = x[i];
        varSet.add(x[i]);
      }
    }

    support.pose(new AlldifferentExcept(xs, s));
  }

  void gen_jacop_among_var(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] s = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    // we do not not pose AmongVar directly because of possible inconsistency with its
    // initialization; we collect all constraints and pose them at the end when all other
    // constraints are posed

    // ---- KK, 2015-10-17
    // among must not have duplicated variables there
    // could be constants that have the same value and
    // are duplicated.
    IntVar[] xx = removeDuplicates(x);
    IntVar[] ss = new IntVar[s.length];
    HashSet<IntVar> varSet = new HashSet<>();
    for (int i = 0; i < s.length; i++) {
      if (varSet.contains(s[i]) && s[i].singleton()) {
        ss[i] = new IntVar(store, s[i].min(), s[i].max());
      } else {
        ss[i] = s[i];
        varSet.add(s[i]);
      }
    }
    IntVar vv;
    if (varSet.contains(v) && v.singleton()) {
      vv = new IntVar(store, v.min(), v.max());
    } else {
      vv = v;
    }

    support.delayedConstraints.add(new AmongVar(xx, ss, vv));
  }

  void gen_jacop_among(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntDomain s = support.getSetLiteral(node, 1);
    IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    // ---- KK, 2015-10-17
    // among must not have duplicated variables. In x vecor
    // could be constants that have the same value and
    // are duplicated.
    IntVar[] xx = new IntVar[x.length];
    HashSet<IntVar> varSet = new HashSet<>();
    for (int i = 0; i < x.length; i++) {
      if (varSet.contains(x[i]) && x[i].singleton()) {
        xx[i] = new IntVar(store, x[i].min(), x[i].max());
      } else {
        xx[i] = x[i];
        varSet.add(x[i]);
      }
    }
    IntVar vv;
    if (varSet.contains(v) && v.singleton()) {
      vv = new IntVar(store, v.min(), v.max());
    } else {
      vv = v;
    }

    IntervalDomain setImpl = new IntervalDomain();
    for (ValueEnumeration e = s.valueEnumeration(); e.hasMoreElements(); ) {
      int val = e.nextElement();

      setImpl.unionAdapt(new IntervalDomain(val, val));
    }

    support.pose(new Among(xx, setImpl, vv));
  }

  void gen_jacop_gcc(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] c = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int indexMin = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int indexMax = indexMin + c.length - 1;

    for (IntVar intVar : x) {
      if (indexMin > intVar.max() || indexMax < intVar.min()) {
        throw new IllegalArgumentException("%% ERROR: gcc domain error in variable " + intVar);
      }
      if (indexMin > intVar.min() && indexMin < intVar.max()) {
        intVar.domain.inMin(store.level, intVar, indexMin);
      }
      if (indexMax < intVar.max() && indexMax > intVar.min()) {
        intVar.domain.inMax(store.level, intVar, indexMax);
      }
    }

    // =========> remove all non-existing-values counters
    IntDomain gccDom = new IntervalDomain();
    for (IntVar v : x) {
      gccDom = gccDom.union(v.dom());
    }
    ArrayList<Var> cList = new ArrayList<>();
    for (int i = 0; i < c.length; i++) {
      if (gccDom.contains(i + indexMin)) {
        cList.add(c[i]);
      } else {
        support.pose(new XeqC(c[i], 0));
      }
    }
    IntVar[] cArray = new IntVar[cList.size()];
    cArray = cList.toArray(cArray);
    // =========>

    support.pose(new GCC(x, cArray));
  }

  void gen_jacop_global_cardinality_closed(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] cover = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] counter = support.getVarArray((SimpleNode) node.jjtGetChild(2));

    IntDomain gccDom = new IntervalDomain();
    for (int e : cover) {
      gccDom = gccDom.union(e);
    }
    for (IntVar v : x) {
      v.domain.in(store.level, v, gccDom);
    }

    support.pose(new GCC(x, counter));
  }

  void gen_jacop_global_cardinality_low_up_closed(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] cover = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] low = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] up = support.getIntArray((SimpleNode) node.jjtGetChild(3));

    IntDomain gccDom = new IntervalDomain();
    int[] newCover = new int[cover.length];
    int n = 0;
    for (int i = 0; i < cover.length; i++) {
      int e = cover[i];
      if (varsContain(x, e)) {
        newCover[n++] = i;
      } else if (low[i] != 0) {
        throw Store.failException;
      }

      gccDom = gccDom.union(e);
    }

    for (IntVar v : x) {
      v.domain.in(store.level, v, gccDom);
    }

    IntVar[] counter = new IntVar[n];
    for (int i = 0; i < n; i++) {
      counter[i] = new IntVar(store, "counter" + i, low[newCover[i]], up[newCover[i]]);
    }

    support.pose(new GCC(x, counter));

    if (support.domainConsistency && !support.options.getBoundConsistency()) {
      // we add additional CountBounds constraint if domain consistency is required
      for (int i = 0; i < low.length; i++) {
        support.pose(new CountBounds(x, cover[i], low[i], up[i]));
      }
    }
  }

  boolean varsContain(IntVar[] x, int e) {
    for (IntVar v : x) {
      if (v.domain.contains(e)) {
        return true;
      }
    }

    return false;
  }

  void gen_jacop_diff2(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));

    IntVar[][] r = new IntVar[v.length / 4][4];
    for (int i = 0; i < r.length; i++) {
      System.arraycopy(v, 4 * i, r[i], 0, 4);
    }

    support.pose(new Diffn(r, false));
  }

  void gen_jacop_diff2_strict(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] lx = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    IntVar[] ly = support.getVarArray((SimpleNode) node.jjtGetChild(3));

    support.pose(
        Diffn.builder().origin1(x).origin2(y).length1(lx).length2(ly).strict(true).build());
  }

  void gen_jacop_list_diff2(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] lx = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    IntVar[] ly = support.getVarArray((SimpleNode) node.jjtGetChild(3));

    support.pose(
        Diffn.builder().origin1(x).origin2(y).length1(lx).length2(ly).strict(false).build());
  }

  void gen_jacop_count(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int y = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    if (c.singleton(0)) {
      for (IntVar v : x) {
        v.domain.inComplement(store.level, v, y);
      }
      return;
    } else if (c.singleton(x.length)) {
      for (IntVar v : x) {
        v.domain.inValue(store.level, v, y);
      }
      return;
    }

    ArrayList<IntVar> xs = new ArrayList<>();
    for (IntVar v : x) {
      if (v.domain.contains(y)) { // y >= v.min() && y <= v.max())
        xs.add(v);
      }
    }
    if (xs.isEmpty()) {
      c.domain.inValue(store.level, c, 0);
    } else if (c.singleton()) {
      support.pose(new CountBounds(xs, y, c.value(), c.value()));
    } else {
      support.pose(new Count(xs, c, y));
    }
  }

  void gen_jacop_count_reif(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int y = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

    support.pose(new Reified(new Count(x, c, y), b));
  }

  void gen_count_eq_imp(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

    if (y.singleton()) {
      support.pose(new Implies(b, new Count(x, c, y.value())));
    } else {
      support.pose(new Implies(b, new CountVar(x, c, y)));
    }
  }

  void gen_jacop_count_bounds(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int value = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int lb = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int ub = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));

    support.pose(new CountBounds(x, value, lb, ub));
  }

  void gen_jacop_count_values(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] values = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] counters = support.getVarArray((SimpleNode) node.jjtGetChild(2));

    if (allVarGround(counters)) {
      int[] lb = new int[counters.length];
      int[] ub = new int[counters.length];
      for (int i = 0; i < counters.length; i++) {
        lb[i] = counters[i].min();
        ub[i] = counters[i].max();
      }
      support.pose(new CountValuesBounds(x, lb, ub, values));
    } else {
      support.pose(new CountValues(x, counters, values));
    }
  }

  void gen_jacop_count_values_bounds(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] values = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] lb = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] ub = support.getIntArray((SimpleNode) node.jjtGetChild(3));

    int n = x.length;
    long z = Arrays.stream(lb).filter(v -> v == 0).count();
    long m = Arrays.stream(ub).filter(v -> v == n).count();
    // " + n);

    // skip constraint since lb is 0 and ub is the length of the
    // list => does not constraint anything
    if (m == ub.length && z == lb.length) {
      if (support.options.debug()) {
        String s = "% SKIPPED " + new CountValuesBounds(x, lb, ub, values);
        IO.println(s.replace("\n", "\n% "));
      }
      return;
    }

    support.pose(new CountValuesBounds(x, lb, ub, values));
  }

  void gen_jacop_count_var(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    if (c.singleton(0)) {
      for (IntVar v : x) {
        support.pose(new XneqY(v, y));
      }
      return;
    } else if (c.singleton(x.length)) {
      for (IntVar v : x) {
        support.pose(new XeqY(v, y));
      }
      return;
    }

    ArrayList<IntVar> xs = new ArrayList<>();
    for (IntVar v : x) {
      if (v.domain.isIntersecting(y.domain)) {
        xs.add(v);
      }
    }
    if (xs.isEmpty()) {
      c.domain.inValue(store.level, c, 0);
    } else if (y.singleton()) {
      support.pose(new Count(xs, c, y.value()));
    } else {
      support.pose(new CountVar(xs, c, y));
    }
  }

  void gen_jacop_count_var_reif(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

    support.pose(new Reified(new CountVar(x, c, y), b));
  }

  void gen_jacop_atleast(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int y = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

    support.pose(new AtLeast(x, c, y));
  }

  void gen_jacop_atleast_reif(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int y = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

    support.pose(new Reified(new AtLeast(x, c, y), b));
  }

  void gen_jacop_atmost(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int y = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

    support.pose(new AtMost(x, c, y));
  }

  void gen_jacop_atmost_reif(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int y = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

    support.pose(new Reified(new AtMost(x, c, y), b));
  }

  void gen_jacop_nvalue(SimpleNode node) {
    IntVar n = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));

    support.pose(new Values(x, n));
  }

  void gen_jacop_minimum_arg_int(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    int offset = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

    support.pose(new ArgMin(x, index, offset - 1));
  }

  void gen_jacop_minimum(SimpleNode node) {
    IntVar n = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));

    support.pose(new Min(x, n));
  }

  void gen_jacop_maximum_arg_int(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    int offset = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

    support.pose(new ArgMax(x, index, offset - 1));
  }

  void gen_jacop_maximum(SimpleNode node) {
    IntVar n = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));

    support.pose(new Max(x, n));
  }

  void gen_jacop_member(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

    int ground = 0;
    IntDomain d = new IntervalDomain();
    for (IntVar intVar : x) {
      if (intVar.singleton()) {
        ground++;
        d.unionAdapt(intVar.domain);
      }
    }
    if (ground == x.length) {
      y.domain.in(store.level, y, d);
      return;
    }

    if (x.length == 1) {
      support.pose(new XeqY(x[0], y));
      return;
    }

    support.pose(new Member(x, y));
  }

  void gen_jacop_member_reif(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    support.pose(new Reified(new Member(x, y), b));
  }

  @SuppressWarnings("unchecked")
  void gen_jacop_table_int(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int size = v.length;
    int[] tbl = support.getIntArray((SimpleNode) node.jjtGetChild(1));

    int[][] t = filterFeasibleTuples(tbl, v, size);

    TableVarsTuples reduced = removeGroundVariablesFromTable(v, t, size);
    v = reduced.vars;
    t = reduced.tuples;

    if (v.length == 0) {
      return;
    }

    t = deduplicateTableRows(t);

    int[] vu = uniqueIndex(v);
    if (vu.length != v.length) {
      poseTableWithUniqueVars(v, t, vu);
    } else {
      poseTableBySize(v, t);
    }
  }

  private int[][] filterFeasibleTuples(int[] tbl, IntVar[] v, int size) {
    int[][] t = new int[tbl.length / size][size];
    boolean[] tuplesToRemove = new boolean[t.length];
    int n = 0;
    for (int i = 0; i < t.length; i++) {
      for (int j = 0; j < size; j++) {
        if (!v[j].domain.contains(tbl[size * i + j])) {
          tuplesToRemove[i] = true;
        }
        t[i][j] = tbl[size * i + j];
      }
      if (tuplesToRemove[i]) {
        n++;
      }
    }
    int k = t.length - n;
    int[][] newT = new int[k][size];
    int m = 0;
    for (int i = 0; i < t.length; i++) {
      if (!tuplesToRemove[i]) {
        newT[m++] = t[i];
      }
    }
    return newT;
  }

  private record TableVarsTuples(IntVar[] vars, int[][] tuples) {}

  private TableVarsTuples removeGroundVariablesFromTable(IntVar[] v, int[][] t, int size) {
    boolean[] toRemove = new boolean[v.length];
    int numberToRemove = 0;
    for (int i = 0; i < v.length; i++) {
      if (v[i].singleton()) {
        toRemove[i] = true;
        numberToRemove++;
      }
    }
    int[][] newT = new int[t.length][size - numberToRemove];
    for (int i = 0; i < t.length; i++) {
      int l = 0;
      for (int j = 0; j < size; j++) {
        if (!toRemove[j]) {
          newT[i][l++] = t[i][j];
        } else if (t[i][j] != v[j].value()) {
          throw Store.failException;
        }
      }
    }
    IntVar[] newV = new IntVar[size - numberToRemove];
    int l = 0;
    for (int i = 0; i < v.length; i++) {
      if (!toRemove[i]) {
        newV[l++] = v[i];
      }
    }
    return new TableVarsTuples(newV, newT);
  }

  private int[][] deduplicateTableRows(int[][] t) {
    ArrayList<Integer>[] tl = new ArrayList[t.length];
    for (int i = 0; i < t.length; i++) {
      ArrayList<Integer> tmp = new ArrayList<>(t.length);
      for (int j = 0; j < t[i].length; j++) {
        tmp.add(t[i][j]);
      }
      tl[i] = tmp;
    }
    Arrays.sort(tl, 0, tl.length, rowComparator);
    t = toIntArray(tl);

    int[][] dt = new int[t.length][t[0].length];
    int[] rc = t[0];
    int kk = 0;
    dt[kk++] = rc;
    for (int i = 1; i < t.length; i++) {
      if (!equalRows(rc, t[i])) {
        dt[kk++] = t[i];
        rc = t[i];
      }
    }
    return Arrays.copyOf(dt, kk);
  }

  private void poseTableWithUniqueVars(IntVar[] v, int[][] t, int[] vu) {
    int[][] nt = removeInfeasibleTuples(t);
    IntVar[] nv = new IntVar[vu.length];
    for (int i = 0; i < vu.length; i++) {
      nv[i] = v[vu[i]];
    }
    int[][] tt = new int[nt.length][vu.length];
    for (int i = 0; i < tt.length; i++) {
      for (int j = 0; j < vu.length; j++) {
        tt[i][j] = nt[i][vu[j]];
      }
    }
    if (nv.length == 1) {
      poseTableSingleVar(nv[0], tt);
    } else {
      poseTableBySize(nv, tt);
    }
  }

  private void poseTableSingleVar(IntVar var, int[][] tt) {
    IntervalDomain d = new IntervalDomain();
    for (int[] ints : tt) {
      d.addDom(new IntervalDomain(ints[0], ints[0]));
    }
    var.domain.in(store.level, var, d);
    if (support.options.debug()) {
      IO.println("% " + var + " in " + d);
    }
  }

  private void poseTableBySize(IntVar[] v, int[][] t) {
    if (t.length <= 64) {
      generateTableConstraints(v, t);
    } else {
      support.pose(new Table(v, t, true));
    }
  }

  int[][] toIntArray(ArrayList<Integer>[] l) {
    int[][] a = new int[l.length][l[0].size()];
    for (int i = 0; i < l.length; i++) {
      for (int j = 0; j < l[i].size(); j++) {
        a[i][j] = l[i].get(j);
      }
    }
    return a;
  }

  boolean equalRows(int[] r1, int[] r2) {
    for (int i = 0; i < r1.length; i++) {
      if (r1[i] != r2[i]) {
        return false;
      }
    }
    return true;
  }

  void generateTableConstraints(IntVar[] v, int[][] t) {

    int size = Arrays.stream(v).mapToInt(x -> x.dom().getSize()).reduce(1, (a, b) -> a * b);

    if (v.length > 3 || size > 70) {
      support.pose(new SimpleTable(v, t, true));
      return;
    }
    int[][] c = conflictTuples(v, t);
    if (c == null || c.length > 3) {
      support.pose(new SimpleTable(v, t, true));
      return;
    }
    poseConflictTuplesAsConstraints(v, c);
  }

  private void poseConflictTuplesAsConstraints(IntVar[] v, int[][] c) {
    if (v.length == 1) {
      for (int[] ints : c) {
        v[0].domain.inComplement(store.level, v[0], ints[0]);
        if (support.options.debug()) {
          IO.println("% " + v[0] + " \\ " + ints[0]);
        }
      }
    } else {
      for (int[] ints : c) {
        XneqC[] x = new XneqC[ints.length];
        for (int j = 0; j < ints.length; j++) {
          x[j] = new XneqC(v[j], ints[j]);
        }
        support.pose(new Or(x));
      }
    }
  }

  int[][] conflictTuples(IntVar[] v, int[][] t) {

    int[][] r = product(v, t);

    ArrayList<int[]> c = new ArrayList<>();
    for (int[] value : r) {
      boolean exists = false;
      for (int[] ints : t) {
        if (eqTuples(value, ints)) {
          exists = true;
          break;
        }
      }
      if (!exists) {
        c.add(value);
      }
    }

    return c.toArray(new int[c.size()][2]);
  }

  int[][] product(IntVar[] v, int[][] t) {

    if (v.length == 1) {
      int[][] r = new int[v[0].domain.getSize()][1];
      int j = 0;
      ValueEnumeration e1 = v[0].domain.valueEnumeration();
      while (e1.hasMoreElements()) {
        r[j++][0] = e1.nextElement();
      }

      return r;
    } else {
      IntVar[] vs = new IntVar[v.length - 1];
      System.arraycopy(v, 1, vs, 0, v.length - 1);
      int[][] rs = product(vs, t);
      int n = v[0].domain.getSize() * rs.length;
      int m = rs[0].length + 1;
      int[][] r = new int[n][m];

      int k = 0;
      ValueEnumeration e1 = v[0].domain.valueEnumeration();
      while (e1.hasMoreElements()) {
        int val = e1.nextElement();

        for (int i = 0; i < rs.length; i++) {
          r[i + k][0] = val;
          System.arraycopy(rs[i], 0, r[i + k], 1, rs[i].length);
        }
        k += rs.length;
      }

      return r;
    }
  }

  boolean eqTuples(int[] a, int[] b) {

    for (int i = 0; i < a.length; i++) {
      if (a[i] != b[i]) {
        return false;
      }
    }
    return true;
  }

  void gen_jacop_assignment(SimpleNode node) {
    IntVar[] f = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] invf = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int indexF = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int indexInvf = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));

    // we do not not pose Assignment directly because of possible inconsistency with its
    // initialization; we collect all constraints and pose them at the end when all other
    // constraints are posed

    if (support.domainConsistency
        && !support.options
            .getBoundConsistency()) { // we add additional implied constraint if domain consistency
      // is
      // required
      support.parameterListForAlldistincts.add(f);
    }

    support.delayedConstraints.add(new Assignment(f, invf, indexF, indexInvf));
  }

  /**
   * Builds a DFA with the given number of states, initial state, and final states.
   *
   * @param Q the number of states
   * @param q0 the initial state (1-based)
   * @param F the set of final states (1-based)
   * @return a pair of [Fsm dfa, FsmState[] states]
   */
  private static Object[] buildDfaStructure(int Q, int q0, IntDomain F) {
    Fsm dfa = new Fsm();
    FsmState[] s = new FsmState[Q];
    for (int i = 0; i < s.length; i++) {
      s[i] = new FsmState();
      dfa.allStates.add(s[i]);
    }
    dfa.initState = s[q0 - 1];
    ValueEnumeration finalStates = F.valueEnumeration();
    while (finalStates.hasMoreElements()) {
      dfa.finalStates.add(s[finalStates.nextElement() - 1]);
    }
    return new Object[] {dfa, s};
  }

  /**
   * Adds transitions from a condition map to a state.
   *
   * @param state the source state
   * @param condition the map of next-state index to transition domain
   * @param states the array of all states
   */
  private static void addTransitionsFromCondition(
      FsmState state, Map<Integer, IntDomain> condition, FsmState[] states) {
    for (Map.Entry<Integer, IntDomain> e : condition.entrySet()) {
      state.transitions.add(new FsmTransition(e.getValue(), states[e.getKey()]));
    }
  }

  /**
   * Adds a transition value to the condition map, merging into existing domains.
   *
   * @param condition the condition map
   * @param nextState the next state index
   * @param transitionValue the transition value
   */
  private static void addTransitionValue(
      Map<Integer, IntDomain> condition, int nextState, int transitionValue) {
    if (condition.containsKey(nextState)) {
      IntervalDomain c = (IntervalDomain) condition.get(nextState);
      c.addLastElement(transitionValue);
      condition.put(nextState, c);
    } else {
      condition.put(nextState, new IntervalDomain(transitionValue, transitionValue));
    }
  }

  void gen_jacop_regular(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int numStates = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int alphabetSize = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int[] d = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    int q0 = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(4));
    IntDomain F = support.getSetLiteral(node, 5);
    int minIndex = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(6));

    // ---- KK, 2018-07-27
    // regular must not have duplicated variables; we create all
    // different variables and equality constraints here
    IntVar[] xx = removeDuplicates(x);

    Object[] dfaParts = buildDfaStructure(numStates, q0, F);
    Fsm dfa = (Fsm) dfaParts[0];
    FsmState[] s = (FsmState[]) dfaParts[1];

    for (int i = 0; i < numStates; i++) {
      // mapping current -> next & transition condition
      Map<Integer, IntDomain> condition = new HashMap<>();
      for (int j = 0; j < alphabetSize; j++) {
        if (d[i * alphabetSize + j] != 0) {
          addTransitionValue(condition, d[i * alphabetSize + j] - minIndex, j + minIndex);
        }
      }
      addTransitionsFromCondition(s[i], condition, s);
    }

    support.delayedConstraints.add(new Regular(dfa, xx));
  }

  void gen_jacop_regular_set(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int numStates = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntDomain S = support.getSetLiteral(node, 2);
    int[] d = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    int q0 = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(4));
    IntDomain F = support.getSetLiteral(node, 5);
    int minIndex = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(6));

    // ---- KK, 2018-07-27
    // regular must not have duplicated variables; we create all
    // different variables and equality constraints here
    IntVar[] xx = removeDuplicates(x);

    Object[] dfaParts = buildDfaStructure(numStates, q0, F);
    Fsm dfa = (Fsm) dfaParts[0];
    FsmState[] s = (FsmState[]) dfaParts[1];

    for (int i = 0; i < numStates; i++) {
      // mapping current -> next & transition condition
      ValueEnumeration valueTransition = S.valueEnumeration();
      Map<Integer, IntDomain> condition = new HashMap<>();
      for (int j = 0; j < S.getSize(); j++) {
        int valTran = valueTransition.nextElement();
        if (d[i * S.getSize() + j] != 0) {
          addTransitionValue(condition, d[i * S.getSize() + j] - minIndex, valTran);
        }
      }
      addTransitionsFromCondition(s[i], condition, s);
    }

    support.delayedConstraints.add(new Regular(dfa, xx));
  }

  void gen_jacop_knapsack(SimpleNode node) {
    int[] weights = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    int[] profits = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    IntVar W = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    IntVar P = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(4));

    support.pose(
        Knapsack.builder()
            .profits(profits)
            .weights(weights)
            .quantity(x)
            .knapsackCapacity(W)
            .knapsackProfit(P)
            .build());
  }

  void gen_jacop_sequence(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntDomain u = support.getSetLiteral(node, 1);
    int q = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));
    int max = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(4));

    IntervalDomain setImpl = new IntervalDomain();
    for (int i = 0; true; i++) {
      Interval val = u.getInterval(i);
      if (val != null) {
        setImpl.unionAdapt(val);
      } else {
        break;
      }
    }

    DecomposedConstraint<Constraint> c =
        Sequence.builder().list(x).set(setImpl).q(q).min(min).max(max).build();
    support.poseDc(c);
  }

  void gen_jacop_stretch(SimpleNode node) {
    int[] values = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    int[] min = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] max = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(3));

    DecomposedConstraint<Constraint> c = new Stretch(values, min, max, x);
    support.poseDc(c);
  }

  void gen_jacop_disjoint(SimpleNode node) {
    SetVar v1 = support.getSetVariable(node, 0);
    SetVar v2 = support.getSetVariable(node, 1);

    support.pose(new AdisjointB(v1, v2));
  }

  void gen_jacop_networkflow(SimpleNode node) {
    int[] arc = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] flow = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] weight = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    int[] balance = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(4));

    int minNode = Arrays.stream(arc).min().getAsInt();

    NetworkBuilder net = new NetworkBuilder();

    Node[] netNode = new Node[balance.length];
    for (int i = 0; i < balance.length; i++) {
      netNode[i] = net.addNode("n_" + i, balance[i]);
    }

    for (int i = 0; i < flow.length; i++) {
      net.addArc(
          netNode[arc[2 * i] - minNode], netNode[arc[2 * i + 1] - minNode], weight[i], flow[i]);
    }

    net.setCostVariable(cost);

    support.pose(new NetworkFlow(net));
  }

  void gen_jacop_lex_less_int(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));

    support.pose(new LexOrder(x, y, true));
  }

  void gen_jacop_lex_lesseq_int(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));

    support.pose(new LexOrder(x, y, false));
  }

  void gen_jacop_increasing(SimpleNode node, boolean strict) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));

    if (x.length == 2) {
      if (strict) {
        support.pose(new XltY(x[0], x[1]));
      } else {
        support.pose(new XlteqY(x[0], x[1]));
      }
    } else {
      support.pose(new Increasing(x, strict));
    }
    // decompoistion possible
  }

  void gen_jacop_decreasing(SimpleNode node, boolean strict) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));

    if (x.length == 2) {
      if (strict) {
        support.pose(new XltY(x[1], x[0]));
      } else {
        support.pose(new XlteqY(x[1], x[0]));
      }
    } else {
      support.pose(new Decreasing(x, strict));
    }
    // decompoistion possible
  }

  void gen_jacop_value_precede_int(SimpleNode node) {
    int s = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(0));
    int t = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(2));

    // no duplicated variables allowed in ValuePrecede and
    // we create a new vector with different variables
    IntVar[] xs = removeDuplicates(x);

    support.pose(new ValuePrecede(s, t, xs));
  }

  void gen_jacop_value_precede_chain_int(SimpleNode node) {
    int[] c = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));

    // no duplicated variables allowed in ValuePrecede and
    // we create a new vector with different variables
    IntVar[] xs = removeDuplicates(x);

    if (c.length > 1) {
      HashSet<Integer> values = new HashSet<>();
      values.add(c[0]);
      for (int i = 1; i < c.length; i++) {
        if (values.contains(c[i])) {
          throw new IllegalArgumentException(
              "%% Values in int_value_precede_chain must be distinct");
        }
        values.add(c[i]);
        support.pose(new ValuePrecede(c[i - 1], c[i], xs));
      }
    }
  }

  void gen_jacop_seq_precede_chain_int(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));

    // keep only **unique** variables in the original order
    ArrayList<IntVar> xx = new ArrayList<>();
    HashSet<IntVar> varSet = new HashSet<>();
    for (IntVar intVar : x) {
      if (!varSet.contains(intVar)) {
        xx.add(intVar);
        varSet.add(intVar);
      }
    }
    IntVar[] xs = xx.toArray(new IntVar[0]);

    support.pose(new SeqPrecedeChain(xs));
  }

  void gen_jacop_bin_packing(SimpleNode node) {
    IntVar[] bin = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] capacity = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int[] w = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int minBin = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));

    // ---- KK, 2023-06-21
    // binpacking must not have duplicated variables there
    // could be constants that have the same value and
    // are duplicated.
    IntVar[] cc = removeDuplicates(capacity);

    Constraint binPack =
        Binpacking.builder().bin(bin).load(cc).w(w).minBin(minBin).lbPruning(true).build();
    support.delayedConstraints.add(binPack);
  }

  void gen_jacop_bin_packing_capacity(SimpleNode node) {
    IntVar[] bin = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] capacity = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] w = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int minBin = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));

    IntVar[] load = new IntVar[capacity.length];
    for (int i = 0; i < load.length; i++) {
      load[i] = new IntVar(store, 0, capacity[i]);
    }

    Constraint binPack =
        Binpacking.builder().bin(bin).load(load).w(w).minBin(minBin).lbPruning(true).build();
    support.delayedConstraints.add(binPack);
  }

  void gen_jacop_float_maximum(SimpleNode node) {
    FloatVar p2 = support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    FloatVar[] p1 = support.getFloatVarArray((SimpleNode) node.jjtGetChild(0));

    support.pose(new org.jacop.floats.constraints.Max(p1, p2));
  }

  void gen_jacop_float_minimum(SimpleNode node) {
    FloatVar p2 = support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    FloatVar[] p1 = support.getFloatVarArray((SimpleNode) node.jjtGetChild(0));

    support.pose(new org.jacop.floats.constraints.Min(p1, p2));
  }

  void gen_jacop_geost(SimpleNode node) {
    buildGeost(node, false);
  }

  void gen_jacop_geost_bb(SimpleNode node) {
    buildGeost(node, true);
  }

  private void buildGeost(SimpleNode node, boolean withBoundingBox) {
    int dim = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(0));
    int[] rectSize = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] rectOffset = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    IntDomain[] shape = support.getSetArray((SimpleNode) node.jjtGetChild(3));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(4));
    IntVar[] kind = support.getVarArray((SimpleNode) node.jjtGetChild(5));

    // ---- KK, 2023-06-29
    // geost must not have duplicated variables
    IntVar[] xx = removeDuplicates(x);

    ArrayList<Shape> shapes = new ArrayList<>();

    // dummy shape to have right indexes for kind (starting from 1)
    ArrayList<Dbox> dummy = new ArrayList<>();
    int[] offsetDummy = new int[dim];
    int[] sizeDummy = new int[dim];
    for (int k = 0; k < dim; k++) {
      offsetDummy[k] = 0;
      sizeDummy[k] = 1;
    }
    dummy.add(new Dbox(offsetDummy, sizeDummy));
    shapes.add(new Shape(0, dummy));

    // create all shapes (starting with id=1)
    for (int i = 0; i < shape.length; i++) {
      ArrayList<Dbox> shapeI = new ArrayList<>();

      for (ValueEnumeration e = shape[i].valueEnumeration(); e.hasMoreElements(); ) {
        int j = e.nextElement();

        int[] offset = new int[dim];
        int[] size = new int[dim];

        for (int k = 0; k < dim; k++) {
          offset[k] = rectOffset[(j - 1) * dim + k];
          size[k] = rectSize[(j - 1) * dim + k];
        }
        shapeI.add(new Dbox(offset, size));
      }
      shapes.add(new Shape((i + 1), shapeI));
    }

    ArrayList<GeostObject> objects = new ArrayList<>();

    for (int i = 0; i < kind.length; i++) {

      IntVar[] coords = new IntVar[dim];

      System.arraycopy(xx, i * dim, coords, 0, dim);

      IntVar start = new IntVar(store, "start[" + i + "]", 0, 0);
      IntVar duration = new IntVar(store, "duration[" + i + "]", 1, 1);
      IntVar end = new IntVar(store, "end[" + i + "]", 1, 1);
      GeostObject obj = new GeostObject(i, coords, kind[i], start, duration, end);
      objects.add(obj);
    }

    ArrayList<ExternalConstraint> constraints = new ArrayList<>();
    int[] dimensions = new int[dim + 1];
    for (int i = 0; i < dim + 1; i++) {
      dimensions[i] = i;
    }

    NonOverlapping constraint1 = new NonOverlapping(objects, dimensions);
    constraints.add(constraint1);

    if (withBoundingBox) {
      int[] lb = support.getIntArray((SimpleNode) node.jjtGetChild(6));
      int[] ub = support.getIntArray((SimpleNode) node.jjtGetChild(7));

      InArea constraint2 = new InArea(new Dbox(lb, ub), null);
      constraints.add(constraint2);
    }

    support.pose(new Geost(objects, constraints, shapes));
  }

  void gen_jacop_if_then_else_bool(SimpleNode node) {
    IntVar[] b = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    IntVar[][] filtered = filterFalseEntries(b, x);
    b = filtered[0];
    x = filtered[1];

    if (x.length == 2) {
      if (tryPoseIfThenElseBoolTwoBranches(b, x, y)) {
        return;
      }
    }
    gen_jacop_if_then_else_int(node);
  }

  /**
   * Tries to pose the if_then_else for two boolean branches. Returns true if handled, false if
   * caller should fall back to gen_jacop_if_then_else_int.
   */
  private boolean tryPoseIfThenElseBoolTwoBranches(IntVar[] b, IntVar[] x, IntVar y) {
    if (support.options.useSat()
        && x[0].min() >= 0
        && x[0].max() <= 1
        && x[1].min() >= 0
        && x[1].max() <= 1
        && y.singleton(1)) {
      support.sat.generateIfThenElseBool(b[0], x[0], x[1]);
      return true;
    }
    if (b[0].singleton(1)) {
      support.pose(new XeqY(x[0], y));
      return true;
    }
    if (b[0].singleton(0) && b[1].singleton(1)) {
      support.pose(new XeqY(x[1], y));
      return true;
    }
    if (y.min() == 1) {
      if (x[1].min() == 1) {
        support.pose(support.fzIfThenBool(b[0], x[0]));
      } else {
        support.pose(new IfThenElseBool((BooleanVar) b[0], (BooleanVar) x[0], (BooleanVar) x[1]));
      }
      return true;
    }
    return false;
  }

  void gen_jacop_if_then_else_int(SimpleNode node) {
    IntVar[] b = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    IntVar[][] filtered = filterFalseEntries(b, x);
    b = filtered[0];
    x = filtered[1];

    int n = x.length;
    if (n == 2 && tryEarlyReturnForIfThenElseIntTwoBranches(b, x, y)) {
      return;
    }

    PrimitiveConstraint[] cs = createIntEqualityConstraintsForConditional(x, y);
    poseIntConditionalConstraint(b, cs, n);
  }

  private boolean tryEarlyReturnForIfThenElseIntTwoBranches(IntVar[] b, IntVar[] x, IntVar y) {
    if (support.options.useSat()
        && x[0].min() >= 0
        && x[0].max() <= 1
        && x[1].min() >= 0
        && x[1].max() <= 1
        && y.singleton(1)) {
      support.sat.generateIfThenElseBool(b[0], x[0], x[1]);
      return true;
    }
    if (b[0].singleton(1)) {
      support.pose(new XeqY(x[0], y));
      return true;
    }
    if (b[0].singleton(0) && b[1].singleton(1)) {
      support.pose(new XeqY(x[1], y));
      return true;
    }
    return false;
  }

  private PrimitiveConstraint[] createIntEqualityConstraintsForConditional(IntVar[] x, IntVar y) {
    PrimitiveConstraint[] cs = new PrimitiveConstraint[x.length];
    for (int i = 0; i < x.length; i++) {
      if (y.singleton()) {
        cs[i] = new XeqC(x[i], y.value());
      } else if (x[i].singleton()) {
        cs[i] = new XeqC(y, x[i].value());
      } else {
        cs[i] = new XeqY(y, x[i]);
      }
    }
    return cs;
  }

  private void poseIntConditionalConstraint(IntVar[] b, PrimitiveConstraint[] cs, int n) {
    if (n == 2) {
      if (cs[1].satisfied()) {
        if (!cs[0].satisfied()) {
          support.pose(new IfThen(new XeqC(b[0], 1), cs[0]));
        }
      } else {
        support.pose(new IfThenElse(new XeqC(b[0], 1), cs[0], cs[1]));
      }
    } else {
      support.pose(new Conditional(b, cs));
    }
  }

  void gen_jacop_if_then_else_float(SimpleNode node) {
    IntVar[] b = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    FloatVar[] x = support.getFloatVarArray((SimpleNode) node.jjtGetChild(1));
    FloatVar y = support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    PrimitiveConstraint[] cs = createFloatEqualityConstraints(x, y);
    poseConditionalConstraints(b, cs);
  }

  void gen_jacop_if_then_else_set(SimpleNode node) {
    IntVar[] b = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    SetVar[] x = support.getSetVarArray((SimpleNode) node.jjtGetChild(1));
    SetVar y = support.getSetVariable(node, 2);

    PrimitiveConstraint[] cs = createSetEqualityConstraints(x, y);
    poseConditionalConstraints(b, cs);
  }

  private PrimitiveConstraint[] createFloatEqualityConstraints(FloatVar[] x, FloatVar y) {
    PrimitiveConstraint[] cs = new PrimitiveConstraint[x.length];
    for (int i = 0; i < x.length; i++) {
      if (y.singleton()) {
        cs[i] = new PeqC(x[i], y.value());
      } else if (x[i].singleton()) {
        cs[i] = new PeqC(y, x[i].value());
      } else {
        cs[i] = new PeqQ(y, x[i]);
      }
    }
    return cs;
  }

  private PrimitiveConstraint[] createSetEqualityConstraints(SetVar[] x, SetVar y) {
    PrimitiveConstraint[] cs = new PrimitiveConstraint[x.length];
    for (int i = 0; i < x.length; i++) {
      if (y.singleton()) {
        cs[i] = new AeqS(x[i], y.domain.glb());
      } else if (x[i].singleton()) {
        cs[i] = new AeqS(y, x[i].domain.glb());
      } else {
        cs[i] = new AeqB(y, x[i]);
      }
    }
    return cs;
  }

  private void poseConditionalConstraints(IntVar[] b, PrimitiveConstraint[] cs) {
    if (cs.length == 2) {
      support.pose(new IfThenElse(new XeqC(b[0], 1), cs[0], cs[1]));
    } else {
      support.pose(new Conditional(b, cs));
    }
  }

  void gen_jacop_channel(SimpleNode node) {
    IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar[] bs = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntDomain vs = support.getSetLiteral(node, 2);

    support.pose(new ChannelReif(x, bs, vs));

    // Decomposition

  }

  void gen_jacop_all_equal_int_reif(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

    if (x.length == 2) {
      support.pose(new Reified(new XeqY(x[0], x[1]), b));
    } else if (x.length == 3) {
      support.pose(
          new Reified(new And(new XeqY[] {new XeqY(x[0], x[1]), new XeqY(x[1], x[2])}), b));
    } else {
      support.pose(new Reified(new AllEqual(x), b));
    }
  }

  // optional global constraints

  void gen_jacop_all_equal_int(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));

    if (x.length == 2) {
      support.pose(new XeqY(x[0], x[1]));
    } else {
      support.pose(new AllEqual(x));
    }
  }

  void gen_jacop_cumulative_optional(SimpleNode node) {
    IntVar[] str = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] dur = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] res = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));
    IntVar[] opt = support.getVarArray((SimpleNode) node.jjtGetChild(4));

    support.pose(new CumulativeOptional(str, dur, res, b, opt));
  }

  void gen_jacop_disjunctive_optional(SimpleNode node) {
    IntVar[] str = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] dur = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] opt = support.getVarArray((SimpleNode) node.jjtGetChild(2));

    IntVar one = support.dictionary.getConstant(1);
    IntVar[] ones = createFilledArray(one, str.length);

    support.pose(new CumulativeUnaryOptional(str, dur, ones, one, opt, true, true));
  }

  void gen_jacop_disjunctive_strict_optional(SimpleNode node) {
    IntVar[] str = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] dur = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] opt = support.getVarArray((SimpleNode) node.jjtGetChild(2));

    IntVar one = support.dictionary.getConstant(1);
    IntVar[] ones = createFilledArray(one, str.length);

    support.pose(
        Diffn.builder().origin1(str).origin2(ones).length1(dur).length2(opt).strict(true).build());
  }

  private static IntVar[] createFilledArray(IntVar value, int length) {
    IntVar[] array = new IntVar[length];
    Arrays.fill(array, value);
    return array;
  }

  IntVar[] removeDuplicates(IntVar[] x) {

    // no duplicated variables allowed in a constraint and
    // we create a new vector with all different variables
    IntVar[] xs = new IntVar[x.length];
    HashSet<IntVar> varSet = new HashSet<>();
    for (int i = 0; i < x.length; i++) {
      if (varSet.contains(x[i])) {
        if (x[i].singleton()) {
          xs[i] = new IntVar(store, x[i].min(), x[i].max());
        } else {
          IntVar tmp = new IntVar(store, x[i].min(), x[i].max());
          support.pose(new XeqY(x[i], tmp));
          xs[i] = tmp;
        }
      } else {
        xs[i] = x[i];
        varSet.add(x[i]);
      }
    }
    return xs;
  }

  boolean allVarOne(IntVar[] w) {
    for (IntVar intVar : w) {
      if (!intVar.singleton(1)) {
        return false;
      }
    }
    return true;
  }

  boolean allVarGround(IntVar[] w) {
    for (IntVar intVar : w) {
      if (!intVar.singleton()) {
        return false;
      }
    }
    return true;
  }

  int[] uniqueIndex(IntVar[] vs) {

    Map<IntVar, Integer> map = new LinkedHashMap<>();
    duplicates = new ArrayList<>();
    for (int i = 0; i < vs.length; i++) {
      if (map.get(vs[i]) == null) {
        map.put(vs[i], i);
      } else {
        duplicates.add(new Pair(map.get(vs[i]), i));
      }
    }

    int[] x = new int[map.size()];
    Set<Map.Entry<IntVar, Integer>> entries = map.entrySet();
    int i = 0;
    for (Map.Entry<IntVar, Integer> e : entries) {
      int v = e.getValue();
      x[i++] = v;
    }
    return x;
  }

  int[][] removeInfeasibleTuples(int[][] t) {
    int n = t.length;
    int[][] nt = new int[n][t[0].length];

    int k = 0;
    for (int[] ints : t) {
      int correct = 0;
      for (Pair d : duplicates) {
        if (ints[d.first()] == ints[d.second()]) {
          correct++;
        }
      }
      if (correct == duplicates.size()) {
        System.arraycopy(ints, 0, nt[k], 0, ints.length);
        k++;
      }
    }

    int[][] tt = new int[k][t[0].length];
    for (int i = 0; i < k; i++) {
      System.arraycopy(nt[i], 0, tt[i], 0, nt[i].length);
    }
    return tt;
  }

  private record Pair(int a, int b) {

    int first() {
      return a;
    }

    int second() {
      return b;
    }

    public String toString() {
      return "(" + a + ", " + b + ")";
    }
  }
}
