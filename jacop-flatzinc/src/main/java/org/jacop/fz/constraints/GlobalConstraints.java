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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.AllEqual;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Alternative;
import org.jacop.constraints.Among;
import org.jacop.constraints.AmongVar;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Conditional;
import org.jacop.constraints.ConditionalSelect;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.CountValuesBounds;
import org.jacop.constraints.CountVar;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Decreasing;
import org.jacop.constraints.Deviation;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.GCC;
import org.jacop.constraints.GlobalCardinality;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.IfThenElseBool;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Increasing;
import org.jacop.constraints.InterDistance;
import org.jacop.constraints.LexChain;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.MultiInterDistance;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SeqPrecedeChain;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.SoftAlldifferent;
import org.jacop.constraints.SoftGCC;
import org.jacop.constraints.Sort;
import org.jacop.constraints.Span;
import org.jacop.constraints.Spread;
import org.jacop.constraints.StockingCost;
import org.jacop.constraints.Stretch;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.SubcircuitCost;
import org.jacop.constraints.SymmetricAlldifferent;
import org.jacop.constraints.ValuePrecede;
import org.jacop.constraints.Values;
import org.jacop.constraints.ViolationMeasure;
import org.jacop.constraints.WeightedSubcircuits;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.CumulativeUnaryOptional;
import org.jacop.constraints.cumulative.Cumulatives;
import org.jacop.constraints.cumulative.UnaryTransition;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.diffn.DiffnK;
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
import org.jacop.constraints.regular.CostMdd;
import org.jacop.constraints.regular.CostRegular;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.HybridTable;
import org.jacop.constraints.table.NegativeTable;
import org.jacop.constraints.table.Restriction;
import org.jacop.constraints.table.TableCompressor;
import org.jacop.constraints.table.TableReified;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PeqQ;
import org.jacop.floats.core.FloatVar;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
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

  // default value of the boolean system properties that switch off a filtering rule
  private static final String FALSE = "false";

  // smallest circuit or subcircuit that gets the implied Alldistinct without ::domain
  static final int CIRCUIT_ALLDISTINCT_MIN_SIZE = 30;

  final Store store;
  final Support support;

  // the two-dimensional diffn constraints read so far: x, y, lx, ly
  private final List<IntVar[][]> diffnProjections = new ArrayList<>();

  // the tasks of the cumulative constraints read so far, see taskKey
  private final Set<List<IntVar>> cumulativeTasks = new HashSet<>();
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

    cumulativeTasks.add(taskKey(str, dur, res));
    poseCumulative(str, dur, res, b);
  }

  private void poseCumulative(IntVar[] str, IntVar[] dur, IntVar[] res, IntVar b) {

    IntVar[][] sdr = filterCumulativeTasks(str, dur, res);
    IntVar[] s = sdr[0];
    IntVar[] d = sdr[1];
    IntVar[] r = sdr[2];

    if (cumulativeResourceSumWithinCapacity(r, b)) {
      return;
    }

    if (s.length == 1) {
      if (d[0].min() > 0) {
        support.pose(new XlteqY(r[0], b));
      } else {
        // a task that may have zero duration does not need to fit within the limit
        support.delayedConstraints.add(new CumulativeBasic(s, d, r, b));
      }
      return;
    }
    if (s.length == 0) {
      return;
    }
    if (support.options.proof() != null) {
      // --proof: the time table, which unit propagation over the time-indexed encoding states;
      // the energy and edge-finding rules of the other cumulative constraints it does not
      support.delayedConstraints.add(new CumulativeBasic(s, d, r, b));
      return;
    }
    if (poseInterDistance(s, d, r, b)) {
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

  /**
   * The mode of the inter-distance detection, from the system property {@code
   * org.jacop.fz.interDistance}: {@code true} (the default) replaces a cumulative of tasks with one
   * length and one resource use by InterDistance or MultiInterDistance, {@code add} posts them next
   * to the cumulative, {@code false} turns the detection off.
   *
   * @return the mode: true, add or false.
   */
  static String interDistanceMode() {
    return System.getProperty("org.jacop.fz.interDistance", "true").toLowerCase();
  }

  /**
   * A cumulative whose tasks have one fixed length p &gt; 1 and one fixed resource use k, with a
   * fixed capacity b, is multi_inter_distance(s, b / k, p): at most b / k starts in any window of
   * p. With b / k = 1 it is inter_distance(s, p).
   *
   * @return true if the cumulative is replaced.
   */
  private boolean poseInterDistance(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {
    String mode = interDistanceMode();
    if ("false".equals(mode) || !b.singleton() || !d[0].singleton() || !r[0].singleton()) {
      return false;
    }
    int p = d[0].value();
    int k = r[0].value();
    if (p < 2 || k < 1) {
      return false;
    }
    for (int i = 1; i < s.length; i++) {
      if (!d[i].singleton(p) || !r[i].singleton(k)) {
        return false;
      }
    }
    int m = b.value() / k;
    if (m == 0) {
      // no task fits under the capacity
      throw Store.failException;
    }
    if (m >= s.length) {
      return false;
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% cumulative of " + s.length + " tasks of length " + p + " as inter-distance, m = " + m);
    }
    support.delayedConstraints.add(
        m == 1 ? new InterDistance(s, p) : new MultiInterDistance(s, m, p));
    return !"add".equals(mode);
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
      // the same start variable twice means two overlapping tasks
      checkForDuplicateVariables(s);
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
      // the same start variable twice means two overlapping tasks
      checkForDuplicateVariables(s);
      support.pose(new Alldiff(s));
      for (IntVar intVar : r) {
        support.pose(new XlteqY(intVar, b));
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
    support.delayedConstraints.add(configureCumulative(cumul));
    applyCumulativeImpliedOptions(s, d, r, b);
  }

  private void poseCumulativeBasicWithImplied(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {
    if (Boolean.parseBoolean(System.getProperty("fz_cumulative_variable_basic", FALSE))) {
      support.delayedConstraints.add(new CumulativeBasic(s, d, r, b));
    } else {
      // edge finding and the energy rules use minimal durations and resource use, so they are
      // sound for variable tasks too; if edge finding is switched on, use the quadratic one
      // since the number of distinct minimal resource uses, which the O(kn log n) one depends
      // on, changes during search
      Cumulative cumul = new Cumulative(s, d, r, b);
      cumul.doQuadraticEdgeFind(true);
      support.delayedConstraints.add(configureCumulative(cumul));
    }
    applyCumulativeImpliedOptions(s, d, r, b);
  }

  /**
   * Sets the filtering rules of a cumulative constraint from the system properties
   * fz_cumulative_ttef (time-table edge finding), fz_cumulative_ttdr (time-table disjunctive
   * reasoning), fz_cumulative_ef (edge finding, off by default), fz_cumulative_quad_ef (quadratic
   * edge finding), fz_cumulative_overload (overload check), fz_cumulative_heef (horizontally
   * elastic edge finding, off by default) and fz_cumulative_adaptive (skipping the time-table
   * energy rules while they prune nothing, on by default).
   */
  static <T extends Cumulative> T configureCumulative(T c) {
    String p = System.getProperty("fz_cumulative_ttef");
    if (p != null) {
      c.doTimeTableEdgeFind(Boolean.parseBoolean(p));
    }
    p = System.getProperty("fz_cumulative_ttdr");
    if (p != null) {
      c.doTimeTableDisjunctive(Boolean.parseBoolean(p));
    }
    // time-table edge finding with time-table disjunctive reasoning solved more cumulative
    // benchmarks than with edge finding added, which cost more time than its pruning gained
    c.doEdgeFind(Boolean.parseBoolean(System.getProperty("fz_cumulative_ef", FALSE)));
    p = System.getProperty("fz_cumulative_quad_ef");
    if (p != null) {
      c.doQuadraticEdgeFind(Boolean.parseBoolean(p));
    }
    // on the cumulative benchmarks, skipping the time-table energy rules while they prune nothing
    // solved more instances and found better objectives, mainly on RCPSP where they rarely prune
    c.doAdaptiveEnergyReasoning(
        Boolean.parseBoolean(System.getProperty("fz_cumulative_adaptive", "true")));
    p = System.getProperty("fz_cumulative_overload");
    if (p != null) {
      c.doOverload(Boolean.parseBoolean(p));
    }
    c.doHorizontallyElasticEdgeFind(
        Boolean.parseBoolean(System.getProperty("fz_cumulative_heef", FALSE)));
    return c;
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
    genCircuit(node, 1);
  }

  void gen_jacop_circuit_offset(SimpleNode node) {
    genCircuit(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1)));
  }

  private void genCircuit(SimpleNode node, int offset) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    // successors must all be different, so the same variable (or constant) twice is infeasible
    checkForDuplicateVariables(v);

    support.pose(new Circuit(v, offset));

    // Circuit propagates all-different on values only
    addImpliedAlldistinct(v);
  }

  void gen_jacop_subcircuit(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    // successors must all be different, so the same variable (or constant) twice is infeasible
    checkForDuplicateVariables(v);
    support.pose(new Subcircuit(v));

    // the successors of a subcircuit are all different too (x[i] = i is unique to i)
    addImpliedAlldistinct(v);
  }

  // jacop_subcircuit_cost(x, d, cost): a subcircuit of x numbered from 1 whose cost is
  // sum(i)(d[i, x[i]]), with d given row by row
  void gen_jacop_subcircuit_cost(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[][] costs = matrix(support.getIntArray((SimpleNode) node.jjtGetChild(1)), v.length);
    IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    checkForDuplicateVariables(v);
    support.pose(new Subcircuit(v));
    addImpliedAlldistinct(v);
    support.pose(new SubcircuitCost(v, costs, cost));
  }

  // jacop_weighted_subcircuits(next, tour, d, tourCost, cost, offset)
  void gen_jacop_weighted_subcircuits(SimpleNode node) {
    IntVar[] next = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] tour = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int[][] costs = matrix(support.getIntArray((SimpleNode) node.jjtGetChild(2)), next.length);
    IntVar[] tourCost = support.getVarArray((SimpleNode) node.jjtGetChild(3));
    IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(4));
    int offset = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
    checkForDuplicateVariables(next);
    support.pose(new Alldistinct(next));
    support.pose(new WeightedSubcircuits(next, tour, costs, tourCost, cost, offset));
  }

  private static int[][] matrix(int[] values, int n) {
    if (values == null || values.length != n * n) {
      throw new IllegalArgumentException("the cost matrix needs " + n + " x " + n + " values");
    }
    int[][] m = new int[n][n];
    for (int i = 0; i < n; i++) {
      System.arraycopy(values, i * n, m[i], 0, n);
    }
    return m;
  }

  /**
   * Adds the implied Alldistinct (GAC all-different) on the successors of a circuit or subcircuit
   * under ::domain, and by default when there are at least CIRCUIT_ALLDISTINCT_MIN_SIZE successors.
   * On the benchmarks it cut time by up to 2x from 30 nodes up, while below that it saved few
   * failures and cost up to 19% more time (vehicle routing, small TSP, circuit enumeration). Option
   * -b leaves it out.
   */
  private void addImpliedAlldistinct(IntVar[] v) {
    if (!support.options.getBoundConsistency()
        && (support.domainConsistency || v.length >= CIRCUIT_ALLDISTINCT_MIN_SIZE)) {
      support.parameterListForAlldistincts.add(v);
    }
  }

  /** Returns true if variable domains are considered sparse (density <= 0.5). */
  private static boolean isSparseDomains(IntVar[] v) {
    float q = 0;
    int n = 0;
    for (IntVar intVar : v) {
      if (!intVar.singleton()) {
        q += intVar.getSize() / (float) (intVar.max() - intVar.min() + 1);
        n++;
      }
    }
    return n > 0 && q / n <= 0.5;
  }

  /**
   * The largest number of values, from the system property {@code org.jacop.fz.alldiffDomainSize}
   * (64 by default), of an all_different over dense domains that gets domain consistency
   * (Alldistinct) instead of bounds consistency (Alldiff). Bounds consistency does not see the
   * holes that other constraints make, as in sudoku, where the domain-consistent one needs a tenth
   * of the failures; over small domains it costs little more.
   *
   * @return the number of values.
   */
  static int alldiffDomainSize() {
    return Integer.getInteger("org.jacop.fz.alldiffDomainSize", 64);
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
    support.alldifferentLists.add(v);

    IntervalDomain dom = new IntervalDomain();
    for (IntVar vv : v) {
      dom = (IntervalDomain) dom.union(vv.dom());
    }
    // a large all_different over sparse domains (successor arrays) keeps domain consistency:
    // bounds consistency prunes nothing inside them
    if (v.length > 100 && !isSparseDomains(v)) {
      support.pose(new Alldiff(v));
      return;
    }
    boolean useAlldiff =
        (support.boundsConsistency || support.options.getBoundConsistency())
            && !isSparseDomains(v)
            && dom.getSize() > alldiffDomainSize();
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
    genSoftGcc(node, ViolationMeasure.VALUE_BASED);
  }

  void gen_jacop_softgcc_var(SimpleNode node) {
    genSoftGcc(node, ViolationMeasure.VARIABLE_BASED);
  }

  private void genSoftGcc(SimpleNode node, ViolationMeasure measure) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] values = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] hardCounters = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    IntVar[] soft_counters = support.getVarArray((SimpleNode) node.jjtGetChild(3));
    IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(4));

    SoftGCC sgcc = new SoftGCC(x, hardCounters, values, soft_counters, cost, measure);
    support.poseDc(sgcc);
  }

  void gen_jacop_alldistinct(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    // we do not not pose Alldistinct directly because of possible inconsistency with its
    // initialization; we collect all vectors and pose it at the end when all constraints are posed

    checkForDuplicateVariables(v);

    support.parameterListForAlldistincts.add(v);
    support.alldifferentLists.add(v);
  }

  // the capacity and the cost sum are posted by the predicate; this only adds the cost reasoning
  void gen_jacop_stocking_cost(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] due = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] h = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));
    int capacity = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(4));
    if (x.length > 0) {
      support.pose(new StockingCost(x, due, h, cost, capacity));
    }
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

  /**
   * Posts all_different on optional variables: x holds the values and occurs whether each variable
   * is present. A present variable keeps its value and an absent one takes a value below every
   * domain, which AlldifferentExcept leaves out.
   */
  void gen_jacop_alldifferent_opt(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] occurs = support.getVarArray((SimpleNode) node.jjtGetChild(1));

    int dummy = IntDomain.MAX_INT;
    for (IntVar v : x) {
      dummy = Math.min(dummy, v.min());
    }
    dummy--;

    ArrayList<IntVar> values = new ArrayList<>();
    Set<IntVar> seen = new HashSet<>();
    for (int i = 0; i < x.length; i++) {
      if (occurs[i].singleton(0)) {
        continue;
      }
      IntVar xi = x[i];
      if (seen.contains(xi)) {
        IntVar copy = new IntVar(store, xi.dom().cloneLight());
        support.pose(new XeqY(xi, copy));
        xi = copy;
      }
      seen.add(x[i]);
      if (occurs[i].singleton(1)) {
        values.add(xi);
      } else {
        IntDomain dom = xi.dom().cloneLight();
        dom.unionAdapt(dummy, dummy);
        IntVar y = new IntVar(store, dom);
        support.pose(new IfThenElse(new XeqC(occurs[i], 1), new XeqY(xi, y), new XeqC(y, dummy)));
        values.add(y);
      }
    }
    if (values.size() > 1) {
      support.pose(new AlldifferentExcept(values, new IntervalDomain(dummy, dummy)));
    }
  }

  void gen_jacop_among_var(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] s = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    // we do not not pose AmongVar directly because of possible inconsistency with its
    // initialization; we collect all constraints and pose them at the end when all other
    // constraints are posed

    // AmongVar must not have the same variable twice; repeated variables or constants (that
    // share one variable) are replaced by copies
    Set<IntVar> seen = new HashSet<>();
    IntVar[] xx = distinctCopies(x, seen);
    IntVar[] ss = distinctCopies(s, seen);
    IntVar vv = distinctCopies(new IntVar[] {v}, seen)[0];

    support.delayedConstraints.add(new AmongVar(xx, ss, vv));
  }

  void gen_jacop_among(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntDomain s = support.getSetLiteral(node, 1);
    IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    // Among must not have the same variable twice; repeated variables or constants (that
    // share one variable) are replaced by copies
    Set<IntVar> seen = new HashSet<>();
    IntVar[] xx = distinctCopies(x, seen);
    IntVar vv = distinctCopies(new IntVar[] {v}, seen)[0];

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

    // c[i] counts value indexMin + i, and x takes only counted values
    int[] cover = new int[c.length];
    for (int i = 0; i < c.length; i++) {
      cover[i] = indexMin + i;
    }
    poseClosedGcc(x, cover, c);
    if (domainConsistent()) {
      poseCountValues(x, cover, c, true);
    }
  }

  void gen_jacop_global_cardinality_closed(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] cover = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] counter = support.getVarArray((SimpleNode) node.jjtGetChild(2));

    poseClosedGcc(x, cover, counter);
    if (domainConsistent()) {
      poseCountValues(x, cover, counter, true);
    }
  }

  void gen_jacop_global_cardinality_low_up_closed(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] cover = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] low = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] up = support.getIntArray((SimpleNode) node.jjtGetChild(3));

    IntVar[] counter = new IntVar[cover.length];
    for (int i = 0; i < cover.length; i++) {
      if (low[i] > up[i]) {
        throw Store.failException;
      }
      counter[i] = new IntVar(store, "counter" + i, low[i], up[i]);
    }

    poseClosedGcc(x, cover, counter);

    if (domainConsistent()) {
      poseGlobalCardinality(x, cover, low, up);
    }
  }

  /** Whether the constraint asks for domain consistency, with ::domain. */
  private boolean domainConsistent() {
    return support.domainConsistency && !support.options.getBoundConsistency();
  }

  /**
   * Poses the domain consistent GlobalCardinality with fixed bounds; a repeated value is counted
   * once within the intersection of its bounds.
   */
  private void poseGlobalCardinality(IntVar[] x, int[] values, int[] lb, int[] ub) {
    if (lb.length != values.length || ub.length != values.length) {
      throw new IllegalArgumentException(
          "global cardinality needs one lower and one upper bound for each value");
    }
    Map<Integer, int[]> bounds = new LinkedHashMap<>();
    for (int i = 0; i < values.length; i++) {
      int[] b = bounds.putIfAbsent(values[i], new int[] {lb[i], ub[i]});
      if (b != null) {
        b[0] = Math.max(b[0], lb[i]);
        b[1] = Math.min(b[1], ub[i]);
      }
    }
    support.pose(
        new GlobalCardinality(
            x,
            bounds.keySet().stream().mapToInt(Integer::intValue).toArray(),
            bounds.values().stream().mapToInt(b -> b[0]).toArray(),
            bounds.values().stream().mapToInt(b -> b[1]).toArray()));
  }

  /**
   * Posts GCC over x restricted to the cover values, where counter[i] counts the occurrences of
   * cover[i]. The cover may be unsorted, may repeat values and may contain values no variable can
   * take, and x may repeat variables. GCC itself needs distinct non-singleton variables and one
   * counter for each value of the union of the variable domains, in increasing order of values.
   */
  private void poseClosedGcc(IntVar[] x, int[] cover, IntVar[] counter) {
    IntervalDomain coverDomain = new IntervalDomain();
    for (int v : cover) {
      coverDomain.unionAdapt(v, v);
    }
    for (IntVar v : x) {
      v.domain.in(store.level, v, coverDomain);
    }

    IntVar[] xs = new IntVar[x.length];
    Set<IntVar> seen = new HashSet<>();
    for (int i = 0; i < x.length; i++) {
      if (!x[i].singleton() && !seen.add(x[i])) {
        xs[i] = new IntVar(store, x[i].dom().cloneLight());
        support.pose(new XeqY(x[i], xs[i]));
      } else {
        xs[i] = x[i];
      }
    }

    // a repeated cover value is counted once and its counters are made equal
    Map<Integer, IntVar> counterOf = new HashMap<>();
    for (int i = 0; i < cover.length; i++) {
      IntVar first = counterOf.putIfAbsent(cover[i], counter[i]);
      if (first != null && first != counter[i]) {
        support.pose(new XeqY(first, counter[i]));
      }
    }

    support.binPackingCardinality.addCounters(x, counterOf);

    // a counter of a value no variable can take is zero; it may also be one of the variables, so
    // the union is recomputed until no counter is fixed any more
    IntDomain union;
    boolean changed;
    do {
      union = new IntervalDomain();
      for (IntVar v : xs) {
        union.unionAdapt(v.dom());
      }
      changed = false;
      for (Map.Entry<Integer, IntVar> e : counterOf.entrySet()) {
        IntVar zero = e.getValue();
        if (!union.contains(e.getKey()) && !zero.singleton(0)) {
          zero.domain.inValue(store.level, zero, 0);
          changed = true;
        }
      }
    } while (changed);
    if (xs.length == 0) {
      return;
    }

    IntVar[] gccCounter = new IntVar[union.getSize()];
    int k = 0;
    for (ValueEnumeration e = union.valueEnumeration(); e.hasMoreElements(); ) {
      gccCounter[k++] = counterOf.get(e.nextElement());
    }
    support.pose(new GCC(xs, gccCounter));
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
    diffnProjections.add(new IntVar[][] {x, y, lx, ly});
  }

  void gen_jacop_list_diff2(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] lx = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    IntVar[] ly = support.getVarArray((SimpleNode) node.jjtGetChild(3));

    support.pose(
        Diffn.builder().origin1(x).origin2(y).length1(lx).length2(ly).strict(false).build());
    diffnProjections.add(new IntVar[][] {x, y, lx, ly});
  }

  /**
   * Whether diffn also gets a cumulative per axis, from the system property {@code
   * fz_diffn_cumulative} (true by default).
   *
   * @return true if the projections are posted.
   */
  static boolean diffnCumulativeEnabled() {
    return Boolean.parseBoolean(System.getProperty("fz_diffn_cumulative", "true"));
  }

  /**
   * Poses, for each two-dimensional diffn, a cumulative per axis: the rectangles crossing a line
   * across one axis are disjoint along the other, so their lengths along it fit in the span of all
   * rectangles along it. A projection is skipped when the model already has a cumulative over the
   * same tasks and heights, as rectangle packing models often do, or when the rectangles are fixed
   * along the other axis and do not all cross one line along it. Called after the whole model is
   * read, before the delayed constraints are imposed.
   */
  void poseDiffnProjections() {
    if (!diffnCumulativeEnabled()) {
      return;
    }
    for (IntVar[][] d : diffnProjections) {
      IntVar[] x = d[0];
      IntVar[] y = d[1];
      IntVar[] lx = d[2];
      IntVar[] ly = d[3];
      if (x.length < 2 || negativeMin(lx) || negativeMin(ly)) {
        continue;
      }
      // with the other axis fixed, rectangles apart along it never meet and diffn knows it; the
      // projection then only adds cost (accap), unless all of them cross one line (filters)
      if (!fixedApart(y, ly) && !cumulativeTasks.contains(taskKey(x, lx, ly))) {
        poseCumulative(x, lx, ly, span(y, ly));
      }
      if (!fixedApart(x, lx) && !cumulativeTasks.contains(taskKey(y, ly, lx))) {
        poseCumulative(y, ly, lx, span(x, lx));
      }
    }
    diffnProjections.clear();
  }

  // whether all intervals [o, o + l) are fixed and not all of them share a point
  private boolean fixedApart(IntVar[] o, IntVar[] l) {
    if (!allVarGround(o) || !allVarGround(l)) {
      return false;
    }
    long lastStart = Long.MIN_VALUE;
    long firstEnd = Long.MAX_VALUE;
    for (int i = 0; i < o.length; i++) {
      lastStart = Math.max(lastStart, o[i].value());
      firstEnd = Math.min(firstEnd, (long) o[i].value() + l[i].value());
    }
    return lastStart >= firstEnd;
  }

  private static boolean negativeMin(IntVar[] v) {
    for (IntVar e : v) {
      if (e.min() < 0) {
        return true;
      }
    }
    return false;
  }

  // the identity of the tasks of a cumulative: its starts, durations and resource uses
  private static List<IntVar> taskKey(IntVar[] s, IntVar[] d, IntVar[] r) {
    List<IntVar> key = new ArrayList<>(3 * s.length);
    key.addAll(Arrays.asList(s));
    key.addAll(Arrays.asList(d));
    key.addAll(Arrays.asList(r));
    return key;
  }

  /** A variable equal to max(o[i] + l[i]) - min(o[i]), the span of the intervals along one axis. */
  private IntVar span(IntVar[] o, IntVar[] l) {
    Store store = support.store;
    IntVar[] end = new IntVar[o.length];
    int low = IntDomain.MAX_INT;
    int high = IntDomain.MIN_INT;
    for (int i = 0; i < o.length; i++) {
      low = Math.min(low, o[i].min());
      high = Math.max(high, o[i].max() + l[i].max());
      if (l[i].singleton(0)) {
        end[i] = o[i];
      } else {
        end[i] = new IntVar(store, o[i].min() + l[i].min(), o[i].max() + l[i].max());
        support.pose(new XplusYeqZ(o[i], l[i], end[i]));
      }
    }
    IntVar first = new IntVar(store, low, high);
    IntVar last = new IntVar(store, low, high);
    IntVar span = new IntVar(store, 0, Math.max(0, high - low));
    support.pose(new Min(o, first));
    support.pose(new Max(end, last));
    support.pose(new XplusYeqZ(first, span, last));
    return span;
  }

  void gen_jacop_diffn_k(SimpleNode node) {
    IntVar[] posn = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] size = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int k = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    boolean strict = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)) != 0;

    int n = posn.length / k;
    IntVar[][] origin = new IntVar[n][k];
    IntVar[][] length = new IntVar[n][k];
    for (int i = 0; i < n; i++) {
      System.arraycopy(posn, k * i, origin[i], 0, k);
      System.arraycopy(size, k * i, length[i], 0, k);
    }

    DiffnK c = new DiffnK(origin, length, strict);
    c.doProjection(Boolean.parseBoolean(System.getProperty("fz_diffnk_projection", FALSE)));
    c.doSlices(Boolean.parseBoolean(System.getProperty("fz_diffnk_slices", FALSE)));
    support.pose(c);
    if (!strict) {
      support.nonStrictDiffnK.add(c);
    }
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
    } else {
      counts
          .computeIfAbsent(List.of(x), k -> new ArrayList<>())
          .add(new PendingCount(y, c, xs, support.constraintPriority));
    }
  }

  /** A jacop_count constraint waiting for {@link #poseCounts()}. */
  private record PendingCount(int value, IntVar counter, List<IntVar> list, int priority) {}

  /** The jacop_count constraints of the model, by the list they count over. */
  private final Map<List<IntVar>, List<PendingCount>> counts = new LinkedHashMap<>();

  /**
   * Poses the jacop_count constraints collected by gen_jacop_count. The counts of different values
   * over the same list become one CountValues, as in magicseq with its n counts over one list: one
   * propagator scans the list once for all values, where n Count constraints are each queued on
   * every change of a list variable and each scan the list.
   */
  void poseCounts() {
    int priority = support.constraintPriority;
    for (Map.Entry<List<IntVar>, List<PendingCount>> e : counts.entrySet()) {
      List<PendingCount> group = e.getValue();
      if (group.size() == 1) {
        PendingCount pc = group.get(0);
        support.constraintPriority = pc.priority();
        IntVar c = pc.counter();
        if (c.singleton()) {
          support.pose(new CountBounds(pc.list(), pc.value(), c.value(), c.value()));
        } else {
          support.pose(new Count(pc.list(), c, pc.value()));
        }
      } else {
        support.constraintPriority = -1;
        int[] values = new int[group.size()];
        IntVar[] counters = new IntVar[group.size()];
        for (int i = 0; i < values.length; i++) {
          values[i] = group.get(i).value();
          counters[i] = group.get(i).counter();
        }
        poseCountValues(e.getKey().toArray(new IntVar[0]), values, counters, false);
      }
    }
    support.constraintPriority = priority;
    counts.clear();
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

    poseCountValues(x, values, counters, domainConsistent());
  }

  /**
   * Poses CountValues, or CountValuesBounds when every counter is fixed, or the domain consistent
   * GlobalCardinality when domain is true. A repeated value is counted once and its counters are
   * made equal.
   */
  private void poseCountValues(IntVar[] x, int[] values, IntVar[] counters, boolean domain) {
    Map<Integer, Integer> firstPosition = new LinkedHashMap<>();
    for (int i = 0; i < values.length; i++) {
      Integer first = firstPosition.putIfAbsent(values[i], i);
      if (first != null && counters[first] != counters[i]) {
        support.pose(new XeqY(counters[first], counters[i]));
      }
    }
    if (firstPosition.size() < values.length) {
      int[] positions = firstPosition.values().stream().mapToInt(Integer::intValue).toArray();
      int[] uniqueValues = new int[positions.length];
      IntVar[] uniqueCounters = new IntVar[positions.length];
      for (int i = 0; i < positions.length; i++) {
        uniqueValues[i] = values[positions[i]];
        uniqueCounters[i] = counters[positions[i]];
      }
      values = uniqueValues;
      counters = uniqueCounters;
    }

    if (domain) {
      support.pose(new GlobalCardinality(x, values, counters));
    } else if (allVarGround(counters)) {
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

    // a repeated cover value is counted once within the intersection of its bounds
    Map<Integer, int[]> bounds = new LinkedHashMap<>();
    for (int i = 0; i < values.length; i++) {
      int[] b = bounds.putIfAbsent(values[i], new int[] {lb[i], ub[i]});
      if (b != null) {
        b[0] = Math.max(b[0], lb[i]);
        b[1] = Math.min(b[1], ub[i]);
      }
    }
    if (bounds.size() < values.length) {
      values = bounds.keySet().stream().mapToInt(Integer::intValue).toArray();
      lb = bounds.values().stream().mapToInt(b -> b[0]).toArray();
      ub = bounds.values().stream().mapToInt(b -> b[1]).toArray();
    }

    int n = x.length;
    long z = Arrays.stream(lb).filter(v -> v == 0).count();
    long m = Arrays.stream(ub).filter(v -> v == n).count();
    // " + n);

    // skip constraint since lb is 0 and ub is the length of the
    // list => does not constraint anything
    if (m == ub.length && z == lb.length) {
      if (support.options.debug()) {
        String s = "% SKIPPED " + new CountValuesBounds(x, lb, ub, values);
        FzConsole.println(s.replace("\n", "\n% "));
      }
      return;
    }

    support.binPackingCardinality.addBounds(x, bounds);
    if (domainConsistent()) {
      poseGlobalCardinality(x, values, lb, ub);
    } else {
      support.pose(new CountValuesBounds(x, lb, ub, values));
    }
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

  /** Poses count(x, y) + k {@literal <=} c (count_geq, count_gt with a variable value or count). */
  void gen_jacop_count_var_le(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    int k = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));

    support.pose(new XplusClteqZ(countOf(x, y), k, c));
  }

  /** Poses count(x, y) {@literal >=} c + k (count_leq, count_lt with a variable value or count). */
  void gen_jacop_count_var_ge(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    int k = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));

    support.pose(new XplusClteqZ(c, k, countOf(x, y)));
  }

  /** Returns a variable equal to the number of variables of x equal to y. */
  private IntVar countOf(IntVar[] x, IntVar y) {
    ArrayList<IntVar> xs = new ArrayList<>();
    for (IntVar v : x) {
      if (v.domain.isIntersecting(y.domain)) {
        xs.add(v);
      }
    }
    IntVar counter = new IntVar(store, 0, xs.size());
    if (xs.isEmpty()) {
      return counter;
    }
    if (y.singleton()) {
      support.pose(new Count(xs, counter, y.value()));
    } else {
      support.pose(new CountVar(xs, counter, y));
    }
    return counter;
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

    if (x.length == 0) {
      // nothing is a member of an empty array
      throw Store.failException;
    }

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

  void gen_jacop_table_int(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int size = v.length;
    int[] tbl = support.getIntArray((SimpleNode) node.jjtGetChild(1));

    int[][] t = filterFeasibleTuples(tbl, v, size);
    if (t.length == 0) {
      // no tuple is allowed by the domains
      throw Store.failException;
    }

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

  /**
   * It posts a reified (b = 1 if and only if x is a tuple) or half-reified (b = 1 implies that x is
   * a tuple) table constraint.
   *
   * @param node the constraint node.
   * @param implication true for the half-reification.
   */
  void gen_jacop_table_int_reif(SimpleNode node, boolean implication) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] tbl = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

    if (b.min() == 1) {
      gen_jacop_table_int(node);
      return;
    }
    if (b.max() == 0 && implication) {
      return;
    }

    // Keep the tuples that can match the domains and project them onto the distinct variables
    // that are not fixed; a tuple that gives two values to the same variable cannot match.
    int size = v.length;
    Map<IntVar, Integer> position = new LinkedHashMap<>();
    for (IntVar x : v) {
      if (!x.singleton()) {
        position.putIfAbsent(x, position.size());
      }
    }
    IntVar[] nv = position.keySet().toArray(new IntVar[0]);
    List<int[]> kept = new ArrayList<>();
    for (int i = 0; i < tbl.length / size; i++) {
      int[] tuple = new int[nv.length];
      boolean[] set = new boolean[nv.length];
      boolean possible = true;
      for (int j = 0; j < size && possible; j++) {
        int value = tbl[size * i + j];
        if (!v[j].domain.contains(value)) {
          possible = false;
        } else if (!v[j].singleton()) {
          int k = position.get(v[j]);
          if (set[k] && tuple[k] != value) {
            possible = false;
          }
          tuple[k] = value;
          set[k] = true;
        }
      }
      if (possible) {
        kept.add(tuple);
      }
    }
    int[][] t = kept.toArray(new int[0][]);

    if (nv.length == 0 || t.length == 0) {
      // The truth of the table is known: x is a tuple exactly when a tuple is left.
      boolean holds = t.length > 0;
      if (!holds) {
        b.domain.in(store.level, b, 0, 0);
      } else if (!implication) {
        b.domain.in(store.level, b, 1, 1);
      }
      return;
    }
    if (b.max() == 0) {
      support.pose(new NegativeTable(nv, t));
    } else {
      support.pose(new TableReified(nv, t, b, implication));
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
    int[][] newT = new int[k][];
    int m = 0;
    for (int i = 0; i < t.length; i++) {
      if (!tuplesToRemove[i]) {
        newT[m++] = t[i];
      }
    }
    return newT;
  }

  private record TableVarsTuples(IntVar[] vars, int[][] tuples) {
    @Override
    public boolean equals(Object o) {
      return o instanceof TableVarsTuples other
          && Arrays.equals(vars, other.vars)
          && Arrays.deepEquals(tuples, other.tuples);
    }

    @Override
    public int hashCode() {
      return 31 * Arrays.hashCode(vars) + Arrays.deepHashCode(tuples);
    }

    @Override
    public String toString() {
      return "TableVarsTuples[vars="
          + Arrays.toString(vars)
          + ", tuples="
          + Arrays.deepToString(tuples)
          + "]";
    }
  }

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
    // stable lexicographic sort of the rows, then drop the repeated ones
    Arrays.sort(t, Arrays::compare);

    int[][] dt = new int[t.length][];
    int[] rc = t[0];
    int kk = 0;
    dt[kk++] = rc;
    for (int i = 1; i < t.length; i++) {
      if (!Arrays.equals(rc, t[i])) {
        dt[kk++] = t[i];
        rc = t[i];
      }
    }
    return Arrays.copyOf(dt, kk);
  }

  private void poseTableWithUniqueVars(IntVar[] v, int[][] t, int[] vu) {
    int[][] nt = removeInfeasibleTuples(t);
    if (nt.length == 0) {
      throw Store.failException;
    }
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
      FzConsole.println("% " + var + " in " + d);
    }
  }

  private void poseTableBySize(IntVar[] v, int[][] t) {
    // Merging the tuples that differ in one column only (-Djacop.table=star into *, or =sets into
    // sets of values) shrinks the tables that MiniZinc expanded from short tables, but it measured
    // slower overall on the FlatZinc benchmarks, so it is off by default.
    String mode = System.getProperty("jacop.table", "plain");
    Restriction[][] compressed =
        "plain".equals(mode) ? null : TableCompressor.compress(v, t, "sets".equals(mode));
    if (compressed != null && compressed.length < t.length) {
      support.pose(new HybridTable(v, compressed));
    } else {
      support.pose(new HybridTable(v, t));
    }
  }

  /**
   * How inverse(x, x) over n variables is posted, set by the system property {@code
   * org.jacop.fz.symmetricAlldifferent}: {@code matching} (the default) for a {@link
   * SymmetricAlldifferent} that channels x[i] = j with x[j] = i and fails when no perfect matching
   * exists, {@code domain} for the domain consistent one, {@code false} for Assignment, which is
   * also used above 1000 variables. On the MiniZinc Challenge models with inverse(x, x) (p1f,
   * elitserien) the domain consistent one searched the same number of nodes and was a quarter
   * slower.
   *
   * @param n the number of variables
   * @return matching, domain or false
   */
  static String symmetricAlldifferent(int n) {
    return n > 1000
        ? "false"
        : System.getProperty("org.jacop.fz.symmetricAlldifferent", "matching");
  }

  private static boolean sameVariables(IntVar[] a, IntVar[] b) {
    for (int i = 0; i < a.length; i++) {
      if (a[i] != b[i] && !(a[i].singleton() && b[i].singleton() && a[i].value() == b[i].value())) {
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

    // inverse functions are bijections, so index sets of different sizes cannot be satisfied
    if (f.length != invf.length) {
      throw Store.failException;
    }

    // inverse(x, x) is symmetric all different, a perfect matching of the variables
    String symmetric = symmetricAlldifferent(f.length);
    if (indexF == indexInvf && sameVariables(f, invf) && !"false".equals(symmetric)) {
      support.pose(new SymmetricAlldifferent(f, indexF, "domain".equals(symmetric)));
      return;
    }

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
   * @param stateCount the number of states
   * @param q0 the initial state (1-based)
   * @param finalStates the set of final states (1-based)
   * @return a pair of [Fsm dfa, FsmState[] states]
   */
  private static Object[] buildDfaStructure(int stateCount, int q0, IntDomain finalStates) {
    Fsm dfa = new Fsm();
    FsmState[] s = new FsmState[stateCount];
    for (int i = 0; i < s.length; i++) {
      s[i] = new FsmState();
      dfa.allStates.add(s[i]);
    }
    dfa.initState = s[q0 - 1];
    ValueEnumeration finalStateEnum = finalStates.valueEnumeration();
    while (finalStateEnum.hasMoreElements()) {
      dfa.finalStates.add(s[finalStateEnum.nextElement() - 1]);
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

  void gen_jacop_cost_regular(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int numStates = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int alphabetSize = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int[] d = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    int q0 = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(4));
    IntDomain finalSet = support.getSetLiteral(node, 5);
    int[] c = support.getIntArray((SimpleNode) node.jjtGetChild(6));
    IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(7));

    // the constraint must not have duplicated variables, nor the cost among them
    IntVar[] xx = removeDuplicates(x);
    for (int i = 0; i < xx.length; i++) {
      if (xx[i] == cost && !cost.singleton()) {
        IntVar tmp = new IntVar(store, cost.min(), cost.max());
        support.pose(new XeqY(cost, tmp));
        xx[i] = tmp;
      }
    }

    // MiniZinc numbers states from 1 and values from 1; state 0 is the failing state
    int[][] transition = new int[numStates][alphabetSize];
    int[][] costs = new int[numStates][alphabetSize];
    for (int q = 0; q < numStates; q++) {
      for (int j = 0; j < alphabetSize; j++) {
        transition[q][j] = d[q * alphabetSize + j] - 1;
        costs[q][j] = c[q * alphabetSize + j];
      }
    }
    int[] finalStates = new int[finalSet.getSize()];
    int k = 0;
    for (ValueEnumeration e = finalSet.valueEnumeration(); e.hasMoreElements(); ) {
      finalStates[k++] = e.nextElement() - 1;
    }

    support.delayedConstraints.add(
        new CostRegular(xx, transition, 1, q0 - 1, finalStates, costs, cost));
  }

  /**
   * Posts regular_nfa: d is the flattened array of the sets of next states, with rows indexed by
   * states from minState and columns by symbols from minSymbol; only the symbols in S are allowed.
   * Regular accepts several transitions from a state with the same symbol.
   */
  void gen_jacop_regular_nfa(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int numStates = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntDomain symbols = support.getSetLiteral(node, 2);
    IntDomain[] d = support.getSetArray((SimpleNode) node.jjtGetChild(3));
    int q0 = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(4));
    IntDomain finalStates = support.getSetLiteral(node, 5);
    int minState = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(6));
    int minSymbol = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(7));
    int columns = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(8));

    IntVar[] xx = removeDuplicates(x);

    Object[] dfaParts = buildDfaStructure(numStates, q0, finalStates.intersect(1, numStates));
    Fsm nfa = (Fsm) dfaParts[0];
    FsmState[] s = (FsmState[]) dfaParts[1];

    for (int q = 1; q <= numStates; q++) {
      int row = q - minState;
      if (row < 0 || (row + 1) * columns > d.length) {
        continue;
      }
      Map<Integer, IntDomain> condition = new HashMap<>();
      for (int j = 0; j < columns; j++) {
        int symbol = minSymbol + j;
        if (!symbols.contains(symbol)) {
          continue;
        }
        ValueEnumeration next = d[row * columns + j].valueEnumeration();
        while (next.hasMoreElements()) {
          int nextState = next.nextElement();
          if (nextState >= 1 && nextState <= numStates) {
            addTransitionValue(condition, nextState - 1, symbol);
          }
        }
      }
      addTransitionsFromCondition(s[q - 1], condition, s);
    }

    support.delayedConstraints.add(new Regular(nfa, xx));
  }

  void gen_jacop_cost_mdd(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] level = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] from = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    IntDomain[] label = support.getSetArray((SimpleNode) node.jjtGetChild(3));
    int[] edgeCost = support.getIntArray((SimpleNode) node.jjtGetChild(4));
    int[] to = support.getIntArray((SimpleNode) node.jjtGetChild(5));
    IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(6));

    // the layered graph must not have duplicated variables, nor the cost among them
    IntVar[] xx = removeDuplicates(x);
    for (int i = 0; i < xx.length; i++) {
      if (xx[i] == cost && !cost.singleton()) {
        IntVar tmp = new IntVar(store, cost.min(), cost.max());
        support.pose(new XeqY(cost, tmp));
        xx[i] = tmp;
      }
    }

    support.delayedConstraints.add(new CostMdd(xx, level, from, label, edgeCost, to, cost));
  }

  void gen_jacop_mdd(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] level = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] from = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    IntDomain[] label = support.getSetArray((SimpleNode) node.jjtGetChild(3));
    int[] to = support.getIntArray((SimpleNode) node.jjtGetChild(4));

    // the layered graph must not have duplicated variables
    IntVar[] xx = removeDuplicates(x);

    support.delayedConstraints.add(new ExtensionalSupportMdd(xx, level, from, label, to));
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

    if (Arrays.stream(x).anyMatch(v -> !v.singleton() && (v == W || v == P))) {
      // Knapsack rejects a quantity that is also the capacity or the profit
      support.pose(new LinearInt(x, weights, "==", W));
      support.pose(new LinearInt(x, profits, "==", P));
      return;
    }

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
    setImpl.addDom(u);

    // Sequence accepts repeated variables and constants (that share one variable)
    DecomposedConstraint<Constraint> c =
        Sequence.builder().list(x).set(setImpl).q(q).min(min).max(max).build();
    support.poseDc(c);
  }

  void gen_jacop_balance(SimpleNode node, boolean squares) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int a = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int b = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int s = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));
    IntVar d = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(4));

    // repeated variables and constants are treated as independent, which stays correct
    support.pose(squares ? new Spread(x, a, b, s, d) : new Deviation(x, a, b, s, d));
  }

  void gen_jacop_stretch(SimpleNode node) {
    int[] values = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    int[] min = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] max = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(3));

    // Stretch replaces repeated variables and constants (that share one variable) by copies
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

    // JaCoP's library numbers the nodes from 1, as the positions in the balance array. FlatZinc
    // files compiled with older versions of the library number them from the lowest node in arc.
    int minNode = Math.min(1, Arrays.stream(arc).min().getAsInt());

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

  void gen_jacop_lex_chain(SimpleNode node, boolean strict) {
    IntVar[] a = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int vectors = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int n = a.length / vectors;

    // vector j is column j of the matrix that a lists row by row
    IntVar[][] x = new IntVar[vectors][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < vectors; j++) {
        x[j][i] = a[i * vectors + j];
      }
    }

    support.pose(new LexChain(x, strict));
  }

  void gen_jacop_increasing(SimpleNode node, boolean strict) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));

    // a repeated variable goes to Increasing/Decreasing, which handle it (XltY rejects it)
    if (x.length == 2 && x[0] != x[1]) {
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

    // a repeated variable goes to Increasing/Decreasing, which handle it (XltY rejects it)
    if (x.length == 2 && x[0] != x[1]) {
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

    if (c.length > 1) {
      HashSet<Integer> values = new HashSet<>();
      for (int v : c) {
        if (!values.add(v)) {
          throw new IllegalArgumentException(
              "%% Values in int_value_precede_chain must be distinct");
        }
      }
      // a later occurrence of a variable equals its first one and adds nothing to the
      // precedences, so only first occurrences are kept
      IntVar[] xs = Arrays.stream(x).distinct().toArray(IntVar[]::new);

      // c[i] takes the role of i and other values the role of 0 (Gange and Stuckey): one domain
      // consistent propagator for the whole chain instead of pairwise ValuePrecede
      support.pose(new SeqPrecedeChain(xs, c));
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

  void gen_jacop_inter_distance(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int p = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));

    if (p > 0 && x.length > 1) {
      support.pose(new InterDistance(x, p));
    }
  }

  void gen_jacop_multi_inter_distance(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int m = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
    int p = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

    if (p <= 0 || x.length <= m) {
      return;
    }
    if (m < 1) {
      // every start is in its own window
      throw Store.failException;
    }
    support.pose(m == 1 ? new InterDistance(x, p) : new MultiInterDistance(x, m, p));
  }

  void gen_jacop_sort(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));

    if (x.length != y.length) {
      throw Store.failException;
    }
    support.pose(new Sort(x, y));
  }

  void gen_jacop_sort_permutation(SimpleNode node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] z = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    int offset = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));

    if (x.length != y.length || x.length != z.length) {
      throw Store.failException;
    }
    support.pose(new Sort(x, y, z, offset));
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

    support.delayedConstraints.add(support.binPackingCardinality.binPacking(bin, cc, w, minBin));
    support.binPackingCliques.add(bin, cc, w, minBin);
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

    support.delayedConstraints.add(support.binPackingCardinality.binPacking(bin, load, w, minBin));
    support.binPackingCliques.add(bin, load, w, minBin);
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
    // geost must not have duplicated variables, neither within nor across x and kind
    IntVar[] all = new IntVar[x.length + kind.length];
    System.arraycopy(x, 0, all, 0, x.length);
    System.arraycopy(kind, 0, all, x.length, kind.length);
    all = removeDuplicates(all);
    IntVar[] xx = Arrays.copyOfRange(all, 0, x.length);
    IntVar[] kk = Arrays.copyOfRange(all, x.length, all.length);

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
      shapes.add(new Shape(i + 1, shapeI));
    }

    ArrayList<GeostObject> objects = new ArrayList<>();

    for (int i = 0; i < kind.length; i++) {

      IntVar[] coords = new IntVar[dim];

      System.arraycopy(xx, i * dim, coords, 0, dim);

      IntVar start = new IntVar(store, "start[" + i + "]", 0, 0);
      IntVar duration = new IntVar(store, "duration[" + i + "]", 1, 1);
      IntVar end = new IntVar(store, "end[" + i + "]", 1, 1);
      GeostObject obj = new GeostObject(i, coords, kk[i], start, duration, end);
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

      // geost_bb gives the box as bounds l..u, while Dbox takes an origin and a length
      int[] length = new int[dim];
      for (int j = 0; j < dim; j++) {
        length[j] = ub[j] - lb[j];
        if (length[j] < 0 && kind.length > 0) {
          throw Store.failException;
        }
      }

      InArea constraint2 = new InArea(new Dbox(lb, length), null);
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

    if (x.length == 2 && tryPoseIfThenElseBoolTwoBranches(b, x, y)) {
      return;
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

    if (CONDITIONAL_SELECT) {
      support.pose(new ConditionalSelect(b, x, y));
      return;
    }
    PrimitiveConstraint[] cs = createIntEqualityConstraintsForConditional(x, y);
    poseIntConditionalConstraint(b, cs, n);
  }

  /**
   * Whether if_then_else on integers is posed as {@link ConditionalSelect}, which bounds the result
   * by the branches still possible ({@code -Dorg.jacop.fz.conditionalSelect}, true by default),
   * instead of IfThenElse/Conditional over equalities, which wait until the selected branch is
   * known.
   */
  static final boolean CONDITIONAL_SELECT =
      Boolean.parseBoolean(System.getProperty("org.jacop.fz.conditionalSelect", "true"));

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

    CumulativeOptional c = configureCumulative(new CumulativeOptional(str, dur, res, b, opt));
    String p = System.getProperty("fz_cumulative_optional_overload");
    if (p != null) {
      c.doOptionalOverload(Boolean.parseBoolean(p));
    }
    support.pose(c);
  }

  void gen_jacop_cumulatives(SimpleNode node) {
    IntVar[] str = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] dur = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] res = support.getVarArray((SimpleNode) node.jjtGetChild(2));
    IntVar[] machine = support.getVarArray((SimpleNode) node.jjtGetChild(3));
    IntVar[] bound = support.getVarArray((SimpleNode) node.jjtGetChild(4));
    boolean upper = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5)) != 0;
    int first = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(6));
    IntVar[] opt =
        node.jjtGetNumChildren() > 7 ? support.getVarArray((SimpleNode) node.jjtGetChild(7)) : null;

    support.pose(new Cumulatives(str, dur, res, machine, bound, upper, first, opt));
  }

  void gen_jacop_disjunctive_optional(SimpleNode node) {
    IntVar[] str = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] dur = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar[] opt = support.getVarArray((SimpleNode) node.jjtGetChild(2));

    IntVar one = support.dictionary.getConstant(1);
    IntVar[] ones = createFilledArray(one, str.length);

    CumulativeUnaryOptional c = new CumulativeUnaryOptional(str, dur, ones, one, opt, true, true);
    // off by default: on the flexible job shop benchmarks it cost time without removing nodes
    c.doOptionalOverload(
        Boolean.parseBoolean(System.getProperty("fz_cumulative_optional_overload", FALSE)));
    support.pose(c);
  }

  void gen_jacop_disjunctive_setup(SimpleNode node) {
    IntVar[] str = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] dur = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int[] family = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] flat = support.getIntArray((SimpleNode) node.jjtGetChild(3));

    int f = (int) Math.round(Math.sqrt(flat.length));
    if (f * f != flat.length) {
      throw new IllegalArgumentException(
          "jacop_disjunctive_setup: the transition matrix has " + flat.length + " entries");
    }
    int[][] transitions = new int[f][f];
    for (int a = 0; a < f; a++) {
      System.arraycopy(flat, a * f, transitions[a], 0, f);
    }
    IntVar[] opt =
        node.jjtGetNumChildren() > 4 ? support.getVarArray((SimpleNode) node.jjtGetChild(4)) : null;
    support.pose(new UnaryTransition(str, dur, family, transitions, opt));
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

  void gen_jacop_alternative(SimpleNode node) {
    IntVar[][] a = intervalArgs(node);
    support.pose(new Alternative(a[0][0], a[0][1], a[0][2], a[1], a[2], a[3]));
  }

  void gen_jacop_span(SimpleNode node) {
    IntVar[][] a = intervalArgs(node);
    support.pose(new Span(a[0][0], a[0][1], a[0][2], a[1], a[2], a[3]));
  }

  // {p0, s0, d0}, p, s and d of jacop_alternative and jacop_span
  private IntVar[][] intervalArgs(SimpleNode node) {
    IntVar[] master = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      master[i] = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
    }
    return new IntVar[][] {
      master,
      support.getVarArray((SimpleNode) node.jjtGetChild(3)),
      support.getVarArray((SimpleNode) node.jjtGetChild(4)),
      support.getVarArray((SimpleNode) node.jjtGetChild(5))
    };
  }

  private static IntVar[] createFilledArray(IntVar value, int length) {
    IntVar[] array = new IntVar[length];
    Arrays.fill(array, value);
    return array;
  }

  /**
   * Returns the variables with every variable already in seen (or repeated in x) replaced by a copy
   * constrained to be equal to it, and adds the returned variables to seen.
   */
  private IntVar[] distinctCopies(IntVar[] x, Set<IntVar> seen) {
    IntVar[] xs = new IntVar[x.length];
    for (int i = 0; i < x.length; i++) {
      if (seen.contains(x[i])) {
        xs[i] = new IntVar(store, x[i].min(), x[i].max());
        if (!x[i].singleton()) {
          support.pose(new XeqY(x[i], xs[i]));
        }
      } else {
        xs[i] = x[i];
      }
      seen.add(xs[i]);
    }
    return xs;
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

    @Override
    public String toString() {
      return "(" + a + ", " + b + ")";
    }
  }
}
