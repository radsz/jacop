/*
 * GiantTourDetector.java
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
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.ArcTimes;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Routes;
import org.jacop.constraints.TspEdgeElimination;
import org.jacop.constraints.TspKOpt;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ASTSolveExpr;
import org.jacop.fz.ASTSolveKind;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds vehicle routes written as a giant tour and posts a redundant {@link Routes} over new arc
 * Booleans, with the rows that tie the arcs to the costs of the model, so that the linear
 * relaxation gets the two-index routing relaxation and its rounded capacity cuts ({@link
 * org.jacop.constraints.lp.CapacityCuts}).
 *
 * <p>A giant tour is one circuit {@code circuit(x)} over the customers and two depot nodes per
 * vehicle, where the successor of each vehicle's end node is fixed to the next vehicle's start node
 * (the cvrp and vrplc models of the MiniZinc Challenge, from Kilby and Shaw's CP model of vehicle
 * routing). The nodes whose successor is fixed and their successors are the depot; the stretch of
 * the tour from one depot node to the next is a route. The detector posts, for the customers 1..k:
 *
 * <ul>
 *   <li>a Boolean {@code b[i,j] <-> x[i] = j} for every customer j a customer i may precede ({@link
 *       ChannelReif}), a Boolean {@code b[i,0]} for "the successor of i is a depot node" and {@code
 *       b[0,j]} for "the predecessor of j is a depot node", with the degree rows {@code sum(j)
 *       b[i,j] + b[i,0] = 1} and {@code sum(i) b[i,j] + b[0,j] = 1};
 *   <li>{@link Routes} over these arcs (depot 0), with demands and a capacity when the model
 *       accumulates a quantity along the tour: an element {@code a[n] = T[x[n]]} for every node n
 *       whose successor is not fixed and a row {@code a[n] >= T[n] + q[n]} with {@code q[n] >= 0}
 *       for every customer; a route then carries at most {@code max T[end] - min T[customer]};
 *   <li>for every element {@code d = c[x[i]]} over a constant array (an arc cost): the row {@code d
 *       = sum(j) c[j] b[i,j] + c[end] b[i,0]} (at least, when the end nodes differ in cost), and
 *       for start nodes with the same costs to the customers the row {@code sum(s) d[s] >= sum(j)
 *       c[j] b[0,j] + c[end] (starts - sum(j) b[0,j])};
 *   <li>for every accumulated quantity T: {@code sum(n) T[x[n]] = sum(m) T[m]}, over the nodes n
 *       whose successor is not fixed and the nodes m that are not the successor of a fixed one, as
 *       x is a permutation. With {@code a[n] >= T[n] + d[n]}, this gives the relaxation {@code
 *       sum(end) T - sum(start) T >= sum(n) d[n]}, the bound on an objective written as the arrival
 *       times at the end nodes (cvrp).
 * </ul>
 *
 * <p>A travelling salesman tour, one circuit {@code circuit(x)} with no successor fixed, is a
 * single route from its first node, taken as the depot, back to it. The detector posts the same
 * arcs, cost rows and {@link Routes} for it, with the degree rows of the depot, so that the linear
 * relaxation becomes the subtour elimination relaxation of Dantzig, Fulkerson and Johnson, with
 * subtour cuts (the capacity cuts without demands) and blossom and comb cuts (Padberg and Rao,
 * Grötschel and Padberg). This is off by default: System property org.jacop.fz.tsp=true turns it
 * on, for tours of at most org.jacop.fz.tspArcs arcs (default 40,000). Use it for a pure TSP whose
 * objective is the sum of the arc costs of the tour. On 42 TSPLIB instances at 600 s it proves 30
 * optima instead of 24 with free search (23 instead of 20 with the model's search), and on the
 * instances of 70 to 152 cities its bound is within 0.8 % of the optimum (median 0 %, against 0.7 %
 * with free search and 3.4 % with the model's search without it). Each LP solve costs time, so at
 * short time limits the solutions found on tours of more than about 120 cities can be worse.
 *
 * <p>For a pure symmetric TSP the detector also removes, before search, the arcs that are in no
 * optimal tour ({@link org.jacop.constraints.TspEdgeElimination}: Jonker and Volgenant's 2-opt
 * compatibility and Hougardy and Schroeder's close point and main edge elimination), whether or not
 * org.jacop.fz.tsp is set. Pure means: the minimised objective occurs only in one row {@code obj =
 * sum(i) d[i] + c}, each successor x[i] occurs only in the circuit and in one element {@code d[i] =
 * cost[x[i]]} over a constant array, each d[i] only in its element and the row, and the arcs and
 * their costs are symmetric. The rules use strict improvements, so every optimal tour stays and the
 * removal is sound with all solutions requested for an optimisation; side constraints on the tour,
 * fixed successors or asymmetric costs turn it off. System property
 * org.jacop.fz.tspElimination=false turns it off; org.jacop.fz.tspEliminationMs (default 2000)
 * limits its time. For the same pure TSP it can post {@link org.jacop.constraints.TspKOpt}, which
 * removes during search the partial tours that a 2-opt or 3-opt move shortens (Isoart and Régin, A
 * k-Opt Based Constraint for the TSP, CP 2021) after a first tour, when system property
 * org.jacop.fz.tspKOpt=true is set. It is off by default: it proves optima faster, but it makes
 * better tours harder to find, so the tours of large instances that are not proved end worse.
 *
 * <p>All the constraints of the model stay. System property org.jacop.fz.giantTour=false turns the
 * detection off; org.jacop.fz.routes=false turns it off with the other routes.
 *
 * <p>References: P. Kilby and P. Shaw, Vehicle Routing, in Handbook of Constraint Programming,
 * Elsevier, 2006 (the giant-tour model); J. Lysgaard, A. N. Letchford and R. W. Eglese, A new
 * branch-and-cut algorithm for the capacitated vehicle routing problem, Mathematical Programming
 * 100(2), 2004 (the two-index relaxation and its rounded capacity cuts); R. Jonker and T.
 * Volgenant, Nonoptimal edges for the symmetric traveling salesman problem, Operations Research
 * 32(4), 1984, S. Hougardy and R. T. Schroeder, Edge elimination in TSP instances, WG 2014, and W.
 * Cook, K. Helsgaun, S. Hougardy and R. T. Schroeder, Local elimination in the traveling salesman
 * problem, Mathematical Programming Computation, 2024 (edge elimination); G. Dantzig, R. Fulkerson
 * and S. Johnson, Solution of a large-scale traveling-salesman problem, Operations Research 2(4),
 * 1954 (the subtour elimination relaxation); M. W. Padberg and M. R. Rao, Odd minimum cut-sets and
 * b-matchings, Mathematics of Operations Research 7(1), 1982, and M. Grötschel and M. W. Padberg,
 * On the symmetric travelling salesman problem I and II, Mathematical Programming 16, 1979 (blossom
 * and comb cuts).
 */
public class GiantTourDetector implements ParserTreeConstants {

  // the fewest customers worth a Routes
  private static final int MIN_CUSTOMERS = 3;

  // the most arcs of one tour: one Boolean each
  private static final int MAX_ARCS = 20_000;

  // the successors removed by the time window reduction
  private int windowArcs;

  // the most arcs of such a tour
  private static final int MAX_TSP_ARCS = Integer.getInteger("org.jacop.fz.tspArcs", 40_000);

  // the most variables of a row read for an increment: a[n] = T[n] + slack[n] + d[n] has four
  private static final int MAX_ROW = 5;

  // the most elements over a constant array read for one node
  private static final int MAX_COSTS = 4;

  // the most milliseconds of the edge elimination
  private static final long ELIMINATION_MS = Long.getLong("org.jacop.fz.tspEliminationMs", 2_000L);

  private final Support support;

  private final List<Tour> tours = new ArrayList<>();

  // the number of constraints each variable occurs in
  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  // the int_lin_eq constraints
  private final List<ASTConstElem> equations = new ArrayList<>();

  // the variable minimized, null when the model maximizes or is a satisfaction problem
  private IntVar minimized;

  private static final class Tour {
    final IntVar[] x;
    final int offset;
    // a subcircuit, a tour only when no node can be its own successor
    final boolean sub;

    Tour(IntVar[] x, int offset, boolean sub) {
      this.x = x;
      this.offset = offset;
      this.sub = sub;
    }
  }

  // p = q + c for the variables p of two-variable equations: aliasOf.get(p) = q, shiftOf.get(p) = c
  private final Map<IntVar, IntVar> aliasOf = new IdentityHashMap<>();
  private final Map<IntVar, Integer> shiftOf = new IdentityHashMap<>();

  // the other literal of each binary clause (r \/ e) over two Booleans
  private final Map<IntVar, List<IntVar>> clausePartners = new IdentityHashMap<>();

  // e -> y = k (int_eq_imp): the variable y and the value k of each literal e
  private final Map<IntVar, IntVar> impliedVar = new IdentityHashMap<>();
  private final Map<IntVar, Integer> impliedValue = new IdentityHashMap<>();

  // the elements value = array[index - first] of each index variable
  private final Map<IntVar, List<Element>> elements = new IdentityHashMap<>();

  // vars null for a constant array (values), values null for an array of variables
  private static final class Element {
    final IntVar[] vars;
    final int[] values;
    final int first;
    final IntVar value;

    Element(IntVar[] vars, int[] values, int first, IntVar value) {
      this.vars = vars;
      this.values = values;
      this.first = first;
      this.value = value;
    }
  }

  // the linear rows of two to MAX_ROW variables of each variable
  private final Map<IntVar, List<Row>> rows = new IdentityHashMap<>();

  // sum a * x == rhs (equation) or <= rhs
  private static final class Row {
    final long[] a;
    final IntVar[] x;
    final long rhs;
    final boolean equation;
    // the literal that enforces the row (int_lin_le_imp), or null for a row that always holds
    IntVar condition;

    Row(long[] a, IntVar[] x, long rhs, boolean equation) {
      this.a = a;
      this.x = x;
      this.rhs = rhs;
      this.equation = equation;
    }
  }

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public GiantTourDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on (the default).
   *
   * @return false if the system property org.jacop.fz.giantTour is false.
   */
  public static boolean enabled() {
    return !"false".equals(System.getProperty("org.jacop.fz.giantTour"));
  }

  /**
   * It scans the constraint items of the model and posts a Routes and its rows for each giant tour.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            for (int a = 0; a < item.jjtGetNumChildren(); a++) {
              PartialCopyDetector.countVariables(support, child(item, a), occurrences);
            }
            collect((ASTConstElem) item);
          }
        }
      } else if (node.getId() == JJTMODELEND && node.jjtGetNumChildren() > 0) {
        objective(child(node, 0));
      }
    }
    for (Tour t : tours) {
      tour(t.x, t.offset, t.sub);
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private ASTScalarFlatExpr scalar(SimpleNode node, int i) {
    return (ASTScalarFlatExpr) node.jjtGetChild(i);
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_circuit" -> tours.add(new Tour(support.getVarArray(child(node, 0)), 1, false));
      case "jacop_circuit_offset" ->
          tours.add(
              new Tour(
                  support.getVarArray(child(node, 0)), support.getInt(scalar(node, 1)), false));
      case "jacop_subcircuit" -> tours.add(new Tour(support.getVarArray(child(node, 0)), 1, true));
      case "int_lin_le_imp" -> row(node, false);
      case "bool_clause" -> clause(node);
      case "int_eq_imp" -> implied(node);
      case "array_int_element" -> element(node, null, support.getIntArray(child(node, 1)), 1);
      case "array_var_int_element" -> element(node, support.getVarArray(child(node, 1)), null, 1);
      case "jacop_array_var_int_element_nonshifted" ->
          element(node, support.getVarArray(child(node, 1)), null, support.getInt(scalar(node, 3)));
      case "int_lin_eq" -> {
        equations.add(node);
        row(node, true);
        alias(node);
      }
      case "int_lin_le" -> row(node, false);
      default -> {
        // not part of a giant tour
      }
    }
  }

  private void element(ASTConstElem node, IntVar[] vars, int[] values, int first) {
    if (vars == null && values == null) {
      return;
    }
    IntVar index = support.getVariable(scalar(node, 0));
    IntVar value = support.getVariable(scalar(node, 2));
    if (index.singleton()) {
      return;
    }
    if (vars != null && Arrays.stream(vars).allMatch(IntVar::singleton)) {
      values = Arrays.stream(vars).mapToInt(IntVar::value).toArray();
      vars = null;
    }
    elements
        .computeIfAbsent(index, k -> new ArrayList<>())
        .add(new Element(vars, values, first, value));
  }

  private void row(ASTConstElem node, boolean equation) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    if (a == null || x == null || a.length != x.length) {
      return;
    }
    ASTScalarFlatExpr r = scalar(node, 2);
    if (r.getType() == 2 && support.dictionary.getVariable(r) != null) {
      IntVar v = support.dictionary.getVariable(r);
      if (!v.singleton()) {
        return;
      }
    }
    long rhs = support.getVariable(r).value();
    List<IntVar> vs = new ArrayList<>();
    List<Long> cs = new ArrayList<>();
    for (int k = 0; k < x.length; k++) {
      if (x[k].singleton()) {
        rhs -= (long) a[k] * x[k].value();
      } else if (a[k] != 0) {
        vs.add(x[k]);
        cs.add((long) a[k]);
      }
    }
    if (vs.size() < 2 || vs.size() > MAX_ROW) {
      return;
    }
    Row row =
        new Row(
            cs.stream().mapToLong(Long::longValue).toArray(),
            vs.toArray(new IntVar[0]),
            rhs,
            equation);
    if ("int_lin_le_imp".equals(node.getName())) {
      IntVar enforced = support.getVariable(scalar(node, 3));
      if (enforced.singleton()) {
        if (enforced.value() == 0) {
          return;
        }
      } else {
        row.condition = enforced;
      }
    }
    for (IntVar v : vs) {
      rows.computeIfAbsent(v, k -> new ArrayList<>()).add(row);
    }
  }

  // p = q + c from int_lin_eq([1, -1], [p, q], c) or its negation
  private void alias(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    if (a == null || x == null || a.length != 2 || a[0] != -a[1] || Math.abs(a[0]) != 1) {
      return;
    }
    ASTScalarFlatExpr r = scalar(node, 2);
    if (r.getType() == 2 && support.dictionary.getVariable(r) != null) {
      return;
    }
    long rhs = support.getVariable(r).value();
    if (x[0] == x[1] || x[0].singleton() || x[1].singleton()) {
      return;
    }
    // a[0] (p - q) = rhs
    long c = a[0] > 0 ? rhs : -rhs;
    if (Math.abs(c) > 1_000_000) {
      return;
    }
    aliasOf.putIfAbsent(x[0], x[1]);
    shiftOf.putIfAbsent(x[0], (int) c);
    aliasOf.putIfAbsent(x[1], x[0]);
    shiftOf.putIfAbsent(x[1], (int) -c);
  }

  // bool_clause([r, e], []): r or e
  private void clause(ASTConstElem node) {
    IntVar[] pos = support.getVarArray(child(node, 0));
    IntVar[] neg = support.getVarArray(child(node, 1));
    if (pos == null || neg == null || pos.length != 2 || neg.length != 0 || pos[0] == pos[1]) {
      return;
    }
    clausePartners.computeIfAbsent(pos[0], k -> new ArrayList<>()).add(pos[1]);
    clausePartners.computeIfAbsent(pos[1], k -> new ArrayList<>()).add(pos[0]);
  }

  // int_eq_imp(y, k, e): e -> y = k
  private void implied(ASTConstElem node) {
    IntVar y = support.getVariable(scalar(node, 0));
    IntVar k = support.getVariable(scalar(node, 1));
    IntVar e = support.getVariable(scalar(node, 2));
    if (!k.singleton() || y.singleton() || e.singleton()) {
      return;
    }
    impliedVar.putIfAbsent(e, y);
    impliedValue.putIfAbsent(e, k.value());
  }

  // the successor value w + offset of x that the negation of the condition of a row implies (not
  // r -> e by a binary clause, e -> x = value, also through an alias of x), or null: the row holds
  // on every arc of x except the one to that value
  private Integer exemptValue(IntVar condition, IntVar xv) {
    for (IntVar e : clausePartners.getOrDefault(condition, List.of())) {
      IntVar y = impliedVar.get(e);
      if (y == null) {
        continue;
      }
      if (y == xv) {
        return impliedValue.get(e);
      }
      if (aliasOf.get(xv) == y) {
        return impliedValue.get(e) + shiftOf.get(xv);
      }
    }
    return null;
  }

  // ---------------------------------------------------------------------------------------------

  private void tour(IntVar[] x, int offset, boolean sub) {
    int n = x.length;
    for (int v = 0; v < n; v++) {
      if (sub && x[v].domain.contains(v + offset)) {
        // a node may stay out of the subcircuit
        IntVar q = aliasOf.get(x[v]);
        if (q == null || q.domain.contains(v + offset - shiftOf.get(x[v]))) {
          return;
        }
      }
      // the elements read through an alias q = x[v] - c of a successor that has none of its own
      IntVar q = aliasOf.get(x[v]);
      if (q != null && elements.containsKey(q) && !elements.containsKey(x[v])) {
        int c = shiftOf.get(x[v]);
        List<Element> own = new ArrayList<>();
        for (Element e : elements.get(q)) {
          own.add(new Element(e.vars, e.values, e.first + c, e.value));
        }
        elements.put(x[v], own);
      }
    }
    // the fixed links: their tails and heads are depot nodes
    boolean[] fixed = new boolean[n];
    boolean[] target = new boolean[n];
    int fixedCount = 0;
    for (int v = 0; v < n; v++) {
      if (x[v].singleton()) {
        int w = x[v].value() - offset;
        if (w < 0 || w >= n || w == v || target[w]) {
          return;
        }
        fixed[v] = true;
        target[w] = true;
        fixedCount++;
      }
    }
    // a travelling salesman tour: its first node is the depot, both start and end of one route
    boolean tsp = fixedCount == 0;
    if (tsp && !"false".equals(System.getProperty("org.jacop.fz.tspElimination"))) {
      eliminateEdges(x, offset);
    }
    // a travelling salesman tour gets the relaxation only with time windows of its own, or in the
    // opt-in TSP mode (org.jacop.fz.tsp)
    boolean tspMode = Boolean.getBoolean("org.jacop.fz.tsp");
    // customer number (1..k) of each node, or 0 for a depot node
    int[] customer = new int[n];
    List<Integer> customers = new ArrayList<>();
    customers.add(-1);
    for (int v = tsp ? 1 : 0; v < n; v++) {
      if (!fixed[v] && !target[v]) {
        customer[v] = customers.size();
        customers.add(v);
      }
    }
    int k = customers.size() - 1;
    if (k < MIN_CUSTOMERS) {
      return;
    }
    // the start nodes (successors of fixed links, not fixed themselves) and the end nodes (fixed,
    // not successors): a customer is followed by a customer or an end node, and preceded by a
    // customer or a start node, as the other depot nodes are already taken
    List<Integer> starts = new ArrayList<>();
    boolean[] end = new boolean[n];
    for (int v = 0; v < n; v++) {
      if (target[v] && !fixed[v]) {
        starts.add(v);
      }
      end[v] = fixed[v] && !target[v];
    }
    if (tsp) {
      starts.add(0);
      end[0] = true;
    }
    if (starts.isEmpty()) {
      return;
    }

    // a quantity accumulated along the tour, the capacity, and the sums over the permutation
    List<Constraint> posted = new ArrayList<>();
    int[] demands = null;
    long capacity = 0;
    double best = 0;
    int sums = 0;
    List<Chain> chainList = chains(x, offset, fixed, target, customers);
    // the time windows of the chains whose lags depend on the arcs, reduced together
    Chain timed = null;
    long[][] windows = null;
    if (!"false".equals(System.getProperty("org.jacop.fz.timeWindows"))) {
      // the path cuts and ArcTimes only for a chain whose customers have windows of their own; a
      // distance accumulated up to one horizon (cvrp) has none, and there they only cost time
      List<Chain> windowed = new ArrayList<>();
      for (Chain c : chainList) {
        if (c.lag != null
            && ("all".equals(System.getProperty("org.jacop.fz.timeWindows"))
                || ownWindows(x, offset, c, customers, starts, end))) {
          windowed.add(c);
        }
      }
      for (int pass = 0; pass < 2; pass++) {
        for (Chain c : chainList) {
          if (c.lag != null) {
            long[][] w = reduceWindows(x, offset, fixed, c);
            if (w == null) {
              timed = null;
              windows = null;
              pass = 2;
              break;
            }
            if (windowed.contains(c) && (timed == null || timed == c)) {
              timed = c;
              windows = w;
            }
          }
        }
      }
    }
    if (tsp && !tspMode && timed == null) {
      return;
    }
    for (Chain c : chainList) {
      posted.add(c.sum);
      sums++;
      if (c.demand == null) {
        continue;
      }
      long q = Long.MIN_VALUE;
      long low = Long.MAX_VALUE;
      for (int v = 0; v < n; v++) {
        if (end[v]) {
          q = Math.max(q, c.t[v].max());
        }
      }
      long total = 0;
      for (int i = 1; i <= k; i++) {
        low = Math.min(low, c.t[customers.get(i)].min());
        total += c.demand[i];
      }
      q -= low;
      if (q > 0 && q < Integer.MAX_VALUE && total > q && (double) total / q > best) {
        best = (double) total / q;
        capacity = q;
        demands = new int[k + 1];
        for (int i = 1; i <= k; i++) {
          demands[i] = (int) Math.min(c.demand[i], q);
        }
      }
    }

    boolean costly = false;
    for (int i = 1; i <= k && !costly; i++) {
      for (Element e : elements.getOrDefault(x[customers.get(i)], List.of())) {
        costly |= e.values != null;
      }
    }
    if (demands == null && !costly) {
      // nothing for the relaxation to bound: a second circuit over the predecessors, say
      return;
    }

    // the arcs and their Booleans
    List<int[]> arcs = new ArrayList<>();
    List<IntVar> literals = new ArrayList<>();
    IntVar[][] arc = new IntVar[k + 1][k + 1];
    int count = 0;
    for (int i = 1; i <= k; i++) {
      count += x[customers.get(i)].getSize();
    }
    if (count > (tsp ? MAX_TSP_ARCS : MAX_ARCS)) {
      return;
    }
    for (int i = 1; i <= k; i++) {
      boolean toEnd = false;
      for (ValueEnumeration e = x[customers.get(i)].domain.valueEnumeration();
          e.hasMoreElements(); ) {
        int w = e.nextElement() - offset;
        if (w < 0 || w >= n) {
          continue;
        }
        if (customer[w] > 0 && customer[w] != i) {
          arc[i][customer[w]] = new IntVar(support.store, 0, 1);
        } else if (end[w]) {
          toEnd = true;
        }
      }
      if (toEnd) {
        arc[i][0] = new IntVar(support.store, 0, 1);
      }
    }
    for (int j = 1; j <= k; j++) {
      int value = customers.get(j) + offset;
      for (int s : starts) {
        if (x[s].domain.contains(value)) {
          arc[0][j] = new IntVar(support.store, 0, 1);
          break;
        }
      }
    }
    for (int i = 0; i <= k; i++) {
      for (int j = 0; j <= k; j++) {
        if (arc[i][j] != null) {
          arcs.add(new int[] {i, j});
          literals.add(arc[i][j]);
        }
      }
    }

    // the costs of the arcs
    int costs = costRows(x, offset, customer, customers, starts, end, arc, posted);

    // the degrees
    for (int i = 1; i <= k; i++) {
      List<IntVar> out = new ArrayList<>();
      List<IntVar> in = new ArrayList<>();
      for (int j = 0; j <= k; j++) {
        if (arc[i][j] != null) {
          out.add(arc[i][j]);
        }
        if (arc[j][i] != null) {
          in.add(arc[j][i]);
        }
      }
      if (out.isEmpty() || in.isEmpty()) {
        return;
      }
      posted.add(ones(out));
      posted.add(ones(in));
      // b[i,j] <-> x[i] = j over the customers j
      List<IntVar> bs = new ArrayList<>();
      List<Integer> vs = new ArrayList<>();
      for (int j = 1; j <= k; j++) {
        if (arc[i][j] != null) {
          bs.add(arc[i][j]);
          vs.add(customers.get(j) + offset);
        }
      }
      if (!bs.isEmpty()) {
        posted.add(
            new ChannelReif(
                    x[customers.get(i)],
                    bs.toArray(new IntVar[0]),
                    vs.stream().mapToInt(Integer::intValue).toArray())
                .setDegreeWeight(0));
      }
    }

    if (tsp && !depotRows(x, offset, customers, arc, posted)) {
      return;
    }

    int[] tails = new int[arcs.size()];
    int[] heads = new int[arcs.size()];
    for (int a = 0; a < tails.length; a++) {
      tails[a] = arcs.get(a)[0];
      heads[a] = arcs.get(a)[1];
    }
    Routes routes =
        new Routes(tails, heads, literals.toArray(new IntVar[0]), demands, (int) capacity);
    // the degree rows keep the degrees
    routes.setDegrees(false);
    if (timed != null) {
      timeWindows(routes, x, offset, customers, starts, end, timed, windows);
      if (!"false".equals(System.getProperty("org.jacop.fz.arcTimes"))) {
        posted.add(new ArcTimes(x, offset, timed.t, timed.lag));
      }
    }
    routes.setDegreeWeight(0);
    posted.add(routes);
    if (support.options.debug()) {
      FzConsole.println(
          (tsp
                  ? "% redundant Routes of a travelling salesman tour: "
                  : "% redundant Routes of a giant tour: ")
              + k
              + " customers, "
              + tails.length
              + " arcs, "
              + (demands == null ? "no capacity" : "capacity " + capacity)
              + ", "
              + costs
              + " cost rows, "
              + sums
              + " tour sums"
              + (timed == null
                  ? ""
                  : ", time windows, "
                      + windowArcs
                      + " successors removed, narrow "
                      + narrow(windows, customers, end)));
    }
    support.delayedConstraints.addAll(posted);
    support.dictionary.addAuxiliaryVariables(literals);
  }

  // the variable of minimize in the solve item
  private void objective(SimpleNode item) {
    SimpleNode last = child(item, item.jjtGetNumChildren() - 1);
    if (last instanceof ASTSolveKind kind
        && "minimize".equals(kind.getKind())
        && last.jjtGetNumChildren() > 0
        && child(kind, 0) instanceof ASTSolveExpr expr) {
      if (expr.getType() == 0) {
        minimized = support.dictionary.getVariable(expr.getIdent());
      } else if (expr.getType() == 1) {
        IntVar[] array = support.dictionary.getVariableArray(expr.getIdent());
        minimized =
            array != null && expr.getIndex() >= 0 && expr.getIndex() < array.length
                ? array[expr.getIndex()]
                : null;
      }
    }
  }

  /*
   * Edge elimination (TspEdgeElimination) for a pure symmetric travelling salesman problem: the
   * model minimizes obj = sum(i) c[i][x[i]] + constant, where each x[i] occurs only in the circuit
   * and in its cost element, each cost only in its element and in that sum, and obj in no other
   * constraint, with no alias and with an interval domain. The arcs i -> j left by the domains of
   * x[i] and of its cost must be symmetric and have symmetric costs. Missing edges get a length larger than any tour, so that no improving
   * move uses one. The removed successors are in no optimal tour; every optimal tour stays, so the
   * optimum is kept, while the tours that are not optimal can go.
   */
  private void eliminateEdges(IntVar[] x, int offset) {
    int n = x.length;
    IntVar obj = minimized;
    // a hole in the domain of obj could forbid the optimal length and make a longer tour optimal
    if (n < 5
        || obj == null
        || occurrences.getOrDefault(obj, 0) != 1
        || obj.domain.noIntervals() != 1) {
      return;
    }
    Set<IntVar> aliased = Collections.newSetFromMap(new IdentityHashMap<>());
    aliased.addAll(support.dictionary.aliasTable.keySet());
    aliased.addAll(support.dictionary.aliasTable.values());
    support.dictionary.addDeclaredEqualities(aliased);
    if (aliased.contains(obj)) {
      return;
    }
    IntVar[] cost = new IntVar[n];
    Element[] element = new Element[n];
    Map<IntVar, Integer> node = new IdentityHashMap<>();
    for (int v = 0; v < n; v++) {
      List<Element> es = elements.get(x[v]);
      if (es == null
          || es.size() != 1
          || es.get(0).values == null
          || occurrences.getOrDefault(x[v], 0) != 2
          || aliased.contains(x[v])) {
        return;
      }
      element[v] = es.get(0);
      cost[v] = element[v].value;
      if (cost[v] == obj
          || cost[v].singleton()
          || occurrences.getOrDefault(cost[v], 0) != 2
          || aliased.contains(cost[v])
          || node.put(cost[v], v) != null) {
        return;
      }
    }
    // obj = sum(v) cost[v] + constant
    long constant = 0;
    boolean found = false;
    for (ASTConstElem eq : equations) {
      IntVar[] vs = support.getVarArray(child(eq, 1));
      if (vs == null || Arrays.stream(vs).noneMatch(v -> v == obj)) {
        continue;
      }
      int[] a = support.getIntArray(child(eq, 0));
      ASTScalarFlatExpr r = scalar(eq, 2);
      IntVar rv = support.getVariable(r);
      if (found || a == null || a.length != vs.length || !rv.singleton()) {
        return;
      }
      found = true;
      int sign = 0;
      for (int k = 0; k < vs.length; k++) {
        if (vs[k] == obj) {
          sign = -a[k];
        }
      }
      if (sign != 1 && sign != -1) {
        return;
      }
      boolean[] seen = new boolean[n];
      int costs = 0;
      long rhs = rv.value();
      for (int k = 0; k < vs.length; k++) {
        if (vs[k] == obj) {
          if (a[k] != -sign) {
            return;
          }
        } else if (vs[k].singleton()) {
          rhs -= (long) a[k] * vs[k].value();
        } else {
          Integer v = node.get(vs[k]);
          if (v == null || seen[v] || a[k] != sign) {
            return;
          }
          seen[v] = true;
          costs++;
        }
      }
      if (costs != n) {
        return;
      }
      // sign * (sum cost - obj) = rhs
      constant = -sign * rhs;
    }
    if (!found) {
      return;
    }
    // the arcs and their costs
    boolean[][] arcs = new boolean[n][n];
    long[][] d = new long[n][n];
    long maxAbs = 0;
    long least = constant;
    for (int v = 0; v < n; v++) {
      Element e = element[v];
      long low = Long.MAX_VALUE;
      for (int w = 0; w < n; w++) {
        int index = w + offset - e.first;
        if (w == v
            || !x[v].domain.contains(w + offset)
            || index < 0
            || index >= e.values.length
            || !cost[v].domain.contains(e.values[index])) {
          continue;
        }
        arcs[v][w] = true;
        d[v][w] = e.values[index];
        maxAbs = Math.max(maxAbs, Math.abs(d[v][w]));
        low = Math.min(low, d[v][w]);
      }
      if (low == Long.MAX_VALUE) {
        return;
      }
      least += low;
    }
    // a lower bound of obj above the least tour could make a longer tour optimal
    if (obj.min() > least) {
      return;
    }
    long big = 2L * n * maxAbs + 1;
    if (big > (1L << 40)) {
      return;
    }
    int edges = 0;
    for (int v = 0; v < n; v++) {
      for (int w = v + 1; w < n; w++) {
        if (arcs[v][w] != arcs[w][v] || (arcs[v][w] && d[v][w] != d[w][v])) {
          return;
        }
        if (!arcs[v][w]) {
          d[v][w] = big;
          d[w][v] = big;
        } else {
          edges++;
        }
      }
    }
    if (Boolean.getBoolean("org.jacop.fz.tspKOpt")) {
      long[][] lengths = new long[n][];
      for (int v = 0; v < n; v++) {
        lengths[v] = d[v].clone();
      }
      support.delayedConstraints.add(new TspKOpt(x, offset, lengths, obj));
      if (support.options.debug()) {
        FzConsole.println("% TSP k-opt dominance (TspKOpt) on " + n + " nodes");
      }
    }
    boolean[][] keep = new boolean[n][];
    for (int v = 0; v < n; v++) {
      keep[v] = arcs[v].clone();
    }
    long start = System.nanoTime();
    int removed = TspEdgeElimination.eliminate(d, keep, start + ELIMINATION_MS * 1_000_000L);
    for (int v = 0; v < n; v++) {
      for (int w = 0; w < n; w++) {
        if (arcs[v][w] && !keep[v][w]) {
          x[v].domain.inComplement(support.store.level, x[v], w + offset);
        }
      }
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% TSP edge elimination: "
              + removed
              + " of "
              + edges
              + " edges removed in "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
  }

  // the degree rows of the depot of a travelling salesman tour and b[0,j] <-> x[0] = j; false when
  // the depot has no arc out or in
  private static boolean depotRows(
      IntVar[] x, int offset, List<Integer> customers, IntVar[][] arc, List<Constraint> posted) {
    int k = customers.size() - 1;
    List<IntVar> out = new ArrayList<>();
    List<IntVar> in = new ArrayList<>();
    List<Integer> vs = new ArrayList<>();
    for (int j = 1; j <= k; j++) {
      if (arc[0][j] != null) {
        out.add(arc[0][j]);
        vs.add(customers.get(j) + offset);
      }
      if (arc[j][0] != null) {
        in.add(arc[j][0]);
      }
    }
    if (out.isEmpty() || in.isEmpty()) {
      return false;
    }
    posted.add(ones(out));
    posted.add(ones(in));
    posted.add(
        new ChannelReif(
                x[0], out.toArray(new IntVar[0]), vs.stream().mapToInt(Integer::intValue).toArray())
            .setDegreeWeight(0));
    return true;
  }

  private static Constraint ones(List<IntVar> vs) {
    int[] w = new int[vs.size()];
    Arrays.fill(w, 1);
    return new LinearInt(vs.toArray(new IntVar[0]), w, "==", 1).setDegreeWeight(0);
  }

  // a quantity T accumulated along the tour: its elements a[n] = T[x[n]], the least increment of
  // each customer (null when some row is missing or an increment is negative) and its sum row
  private static final class Chain {
    final IntVar[] t;
    final long[] demand;
    final Constraint sum;
    // the value T[x[v]] read through the successor of each node v not fixed
    IntVar[] a;
    // lag[v][w]: a row forces T[w] >= T[v] + lag[v][w] when x[v] = w, NO_LAG when none does; null
    // for a node v without such rows, and for all nodes when no lag depends on the successor
    long[][] lag;

    Chain(IntVar[] t, long[] demand, Constraint sum) {
      this.t = t;
      this.demand = demand;
      this.sum = sum;
    }
  }

  private List<Chain> chains(
      IntVar[] x, int offset, boolean[] fixed, boolean[] target, List<Integer> customers) {
    int n = x.length;
    int k = customers.size() - 1;
    // the arrays of variables read through the successor of every node not fixed
    Map<List<IntVar>, IntVar[]> values = new LinkedHashMap<>();
    Map<List<IntVar>, IntVar[]> arrays = new LinkedHashMap<>();
    for (int v = 0; v < n; v++) {
      if (fixed[v]) {
        continue;
      }
      List<Element> es = elements.get(x[v]);
      if (es == null) {
        return List.of();
      }
      for (Element e : es) {
        if (e.vars == null) {
          continue;
        }
        IntVar[] t = aligned(e, offset, n);
        if (t == null) {
          continue;
        }
        List<IntVar> key = Arrays.asList(t);
        IntVar[] a = values.computeIfAbsent(key, z -> new IntVar[n]);
        arrays.putIfAbsent(key, t);
        if (a[v] == null) {
          a[v] = e.value;
        }
      }
    }
    List<Chain> out = new ArrayList<>();
    for (Map.Entry<List<IntVar>, IntVar[]> entry : values.entrySet()) {
      IntVar[] a = entry.getValue();
      IntVar[] t = arrays.get(entry.getKey());
      boolean all = true;
      for (int v = 0; v < n && all; v++) {
        all = fixed[v] || a[v] != null;
      }
      if (!all) {
        continue;
      }
      // the least increment into the successor of each customer
      long[] demand = new long[k + 1];
      boolean localRows = false;
      boolean nonNegative = true;
      for (int i = 1; i <= k && demand != null; i++) {
        int v = customers.get(i);
        Long q = increment(a[v], t[v]);
        if (q == null) {
          demand = null;
        } else {
          localRows |= a[v] != t[v];
          nonNegative &= q >= 0;
          demand[i] = q;
        }
      }
      long[][] lag = lags(x, offset, fixed, a, t);
      if (demand == null ? lag == null : !localRows) {
        // a chain of times along the arcs only (rows enforced on the arcs to the customers, as in
        // a travelling salesman tour with time windows) has no increment on every arc
        continue;
      }
      // sum over the nodes not fixed of T[x[n]] = sum of T over the nodes no fixed link enters
      List<IntVar> vs = new ArrayList<>();
      List<Integer> ws = new ArrayList<>();
      long rhs = 0;
      for (int v = 0; v < n; v++) {
        if (!fixed[v]) {
          rhs = term(a[v], 1, vs, ws, rhs);
        }
        if (!target[v]) {
          rhs = term(t[v], -1, vs, ws, rhs);
        }
      }
      if (vs.size() < 2 || Math.abs(rhs) > Integer.MAX_VALUE) {
        continue;
      }
      Constraint sum =
          new LinearInt(
                  vs.toArray(new IntVar[0]),
                  ws.stream().mapToInt(Integer::intValue).toArray(),
                  "==",
                  (int) rhs)
              .setDegreeWeight(0);
      Chain chain = new Chain(t, demand != null && nonNegative ? demand : null, sum);
      chain.a = a;
      chain.lag = lag;
      out.add(chain);
    }
    return out;
  }

  // adds w * v to the row, a constant to its right-hand side
  private static long term(IntVar v, int w, List<IntVar> vs, List<Integer> ws, long rhs) {
    if (v.singleton()) {
      return rhs - (long) w * v.value();
    }
    int at = -1;
    for (int i = 0; i < vs.size(); i++) {
      if (vs.get(i) == v) {
        at = i;
        break;
      }
    }
    if (at < 0) {
      vs.add(v);
      ws.add(w);
    } else {
      ws.set(at, ws.get(at) + w);
    }
    return rhs;
  }

  // the array of an element by node: node v is read at index v + offset
  private static IntVar[] aligned(Element e, int offset, int n) {
    IntVar[] t = new IntVar[n];
    for (int v = 0; v < n; v++) {
      int i = v + offset - e.first;
      if (i < 0 || i >= e.vars.length) {
        return null;
      }
      t[v] = e.vars[i];
    }
    return t;
  }

  // the time windows of the nodes of the routes (customer i is node customers.get(i), 0 the
  // depot) and the least travel time of each arc, for the infeasible path cuts of the relaxation:
  // the depot is left at time 0 and its arcs to a customer take the least arrival from a start
  // node; the arcs back take the least lag to an end node, which is due at the latest end
  private static void timeWindows(
      Routes routes,
      IntVar[] x,
      int offset,
      List<Integer> customers,
      List<Integer> starts,
      boolean[] end,
      Chain c,
      long[][] windows) {
    int n = x.length;
    int k = customers.size() - 1;
    long[] lo = windows[0];
    long[] hi = windows[1];
    long[] earliest = new long[k + 1];
    long[] latest = new long[k + 1];
    long due = Long.MIN_VALUE;
    for (int v = 0; v < n; v++) {
      if (end[v]) {
        due = Math.max(due, hi[v]);
      }
    }
    latest[0] = due;
    for (int i = 1; i <= k; i++) {
      earliest[i] = lo[customers.get(i)];
      latest[i] = hi[customers.get(i)];
    }
    long[] travel = new long[routes.tails.length];
    for (int a = 0; a < travel.length; a++) {
      int i = routes.tails[a];
      int j = routes.heads[a];
      long t = Long.MAX_VALUE;
      if (i > 0 && j > 0) {
        long[] l = c.lag[customers.get(i)];
        t = l == null ? NO_LAG : l[customers.get(j)];
      } else if (i > 0) {
        long[] l = c.lag[customers.get(i)];
        for (int w = 0; w < n && t != NO_LAG; w++) {
          if (end[w] && x[customers.get(i)].domain.contains(w + offset)) {
            t = l == null || l[w] == NO_LAG ? NO_LAG : Math.min(t, l[w]);
          }
        }
      } else if (j > 0) {
        int w = customers.get(j);
        for (int s : starts) {
          if (t != NO_LAG && x[s].domain.contains(w + offset)) {
            long[] l = c.lag[s];
            t = l == null || l[w] == NO_LAG ? NO_LAG : Math.min(t, lo[s] + l[w]);
          }
        }
      }
      travel[a] = t == Long.MAX_VALUE ? NO_LAG : t;
    }
    routes.setTimeWindows(earliest, latest, travel);
    IntVar[] times = new IntVar[k + 1];
    for (int i = 1; i <= k; i++) {
      times[i] = c.t[customers.get(i)];
    }
    routes.setTimes(times);
  }

  // the share of the customers whose window is at most half the span of the routes
  private static double narrow(long[][] w, List<Integer> customers, boolean[] end) {
    long due = Long.MIN_VALUE;
    long start = Long.MAX_VALUE;
    for (int v = 0; v < end.length; v++) {
      if (end[v]) {
        due = Math.max(due, w[1][v]);
      }
    }
    for (int i = 1; i < customers.size(); i++) {
      start = Math.min(start, w[0][customers.get(i)]);
    }
    int k = 0;
    for (int i = 1; i < customers.size(); i++) {
      int v = customers.get(i);
      if (2 * (w[1][v] - w[0][v]) <= due - start) {
        k++;
      }
    }
    return (double) k / (customers.size() - 1);
  }

  // whether some customer has a time window of its own: bounds of its time tighter than what the
  // earliest start and the latest end of the routes give through the lags of its arcs; a distance
  // accumulated up to one horizon (cvrp) has none
  private static boolean ownWindows(
      IntVar[] x,
      int offset,
      Chain c,
      List<Integer> customers,
      List<Integer> starts,
      boolean[] end) {
    int n = x.length;
    long due = Long.MIN_VALUE;
    for (int v = 0; v < n; v++) {
      if (end[v]) {
        due = Math.max(due, c.t[v].max());
      }
    }
    for (int i = 1; i < customers.size(); i++) {
      int v = customers.get(i);
      long[] l = c.lag[v];
      long back = Long.MAX_VALUE;
      for (int w = 0; w < n && l != null; w++) {
        if (end[w] && l[w] != NO_LAG && x[v].domain.contains(w + offset)) {
          back = Math.min(back, l[w]);
        }
      }
      long reach = Long.MAX_VALUE;
      for (int s : starts) {
        long[] ls = c.lag[s];
        if (ls != null && ls[v] != NO_LAG && x[s].domain.contains(v + offset)) {
          reach = Math.min(reach, c.t[s].min() + ls[v]);
        }
      }
      if (back != Long.MAX_VALUE && c.t[v].max() < due - back
          || reach != Long.MAX_VALUE && c.t[v].min() > reach) {
        return true;
      }
    }
    return false;
  }

  // no row forces a lag on the arc
  private static final long NO_LAG = ArcTimes.NO_LAG;

  // the most rounds of the time window reduction
  private static final int WINDOW_ROUNDS = 20;

  // the lags lag[v][w] of the chain: T[x[v]] >= T[v] + lag[v][w] when x[v] = w, from the rows
  // alpha (a - t) + sum gamma y (==, or <= with alpha < 0) rhs over a[v] = T[x[v]], t = T[v] and
  // other variables y, where a y that is an element c[x[v]] over a constant array takes the value
  // c[w] of the arc (an arc cost, as a travel time) and the others their bounds; null when no lag
  // depends on the successor
  private long[][] lags(IntVar[] x, int offset, boolean[] fixed, IntVar[] a, IntVar[] t) {
    int n = x.length;
    long[][] lag = new long[n][];
    boolean varies = false;
    for (int v = 0; v < n; v++) {
      if (fixed[v] || a[v] == null || a[v] == t[v] || a[v].singleton()) {
        continue;
      }
      // the arc costs read through x[v]
      Map<IntVar, Element> costs = new IdentityHashMap<>();
      for (Element e : elements.getOrDefault(x[v], List.of())) {
        if (e.values != null) {
          costs.putIfAbsent(e.value, e);
        }
      }
      long[] best = null;
      for (Row given : rows.getOrDefault(a[v], List.of())) {
        Integer exempt = null;
        if (given.condition != null) {
          exempt = exemptValue(given.condition, x[v]);
          if (exempt == null) {
            continue;
          }
        }
        Row r = withTime(given, a[v], t[v], costs);
        long[] l = lag(r, a[v], t[v], x[v], offset, n, costs);
        if (l == null) {
          continue;
        }
        if (exempt != null && exempt - offset >= 0 && exempt - offset < n) {
          // the row does not hold on the arc to the exempt successor
          l[exempt - offset] = NO_LAG;
        }
        if (best == null) {
          best = l;
        } else {
          for (int w = 0; w < n; w++) {
            best[w] = Math.max(best[w], l[w]);
          }
        }
      }
      if (best == null) {
        continue;
      }
      lag[v] = best;
      long first = NO_LAG;
      for (int w = 0; w < n && !varies; w++) {
        if (best[w] != NO_LAG) {
          if (first == NO_LAG) {
            first = best[w];
          } else {
            varies = first != best[w];
          }
        }
      }
    }
    return varies ? lag : null;
  }

  // the row with a variable s replaced by its definition when the row does not hold t itself and
  // an equation s = t + y (coefficient of s 1 or -1) defines s, as a flattened a[x[v]] >= t[v] +
  // d[v] has it (XCSP TSPTW: s = t + d, s <= a); the row itself otherwise
  private Row withTime(Row r, IntVar a, IntVar t, Map<IntVar, Element> costs) {
    for (IntVar v : r.x) {
      if (v == t) {
        return r;
      }
    }
    for (int i = 0; i < r.x.length; i++) {
      IntVar s = r.x[i];
      if (s == a || costs.containsKey(s)) {
        continue;
      }
      for (Row eq : rows.getOrDefault(s, List.of())) {
        if (!eq.equation || eq.condition != null || eq == r) {
          continue;
        }
        long es = 0;
        boolean hasT = false;
        boolean hasA = false;
        for (int k = 0; k < eq.x.length; k++) {
          if (eq.x[k] == s) {
            es += eq.a[k];
          }
          hasT |= eq.x[k] == t;
          hasA |= eq.x[k] == a;
        }
        if (!hasT || hasA || Math.abs(es) != 1) {
          continue;
        }
        // r - (r_s / e_s) eq, with e_s = 1 or -1
        long f = r.a[i] * es;
        Map<IntVar, Long> w = new IdentityHashMap<>();
        for (int k = 0; k < r.x.length; k++) {
          w.merge(r.x[k], r.a[k], Long::sum);
        }
        for (int k = 0; k < eq.x.length; k++) {
          w.merge(eq.x[k], -f * eq.a[k], Long::sum);
        }
        w.values().removeIf(c -> c == 0);
        IntVar[] xs = w.keySet().toArray(new IntVar[0]);
        long[] as = w.values().stream().mapToLong(Long::longValue).toArray();
        Row out = new Row(as, xs, r.rhs - f * eq.rhs, r.equation);
        out.condition = r.condition;
        return out;
      }
    }
    return r;
  }

  // the lags of one row over the successors w of v, NO_LAG where the row gives none; null when
  // the row does not bound a - t from below
  private static long[] lag(
      Row r, IntVar a, IntVar t, IntVar xv, int offset, int n, Map<IntVar, Element> costs) {
    long alpha = 0;
    long beta = 0;
    for (int i = 0; i < r.x.length; i++) {
      if (r.x[i] == a) {
        alpha += r.a[i];
      } else if (r.x[i] == t) {
        beta += r.a[i];
      }
    }
    // a fixed t was folded into the right-hand side by row()
    if (alpha == 0 || (t.singleton() ? beta != 0 : beta != -alpha) || !r.equation && alpha > 0) {
      return null;
    }
    long rest = r.rhs;
    List<Element> arcCosts = new ArrayList<>();
    List<Long> gammas = new ArrayList<>();
    for (int i = 0; i < r.x.length; i++) {
      if (r.x[i] == a || r.x[i] == t) {
        continue;
      }
      long gamma = r.a[i];
      Element e = costs.get(r.x[i]);
      if (e != null) {
        arcCosts.add(e);
        gammas.add(gamma);
      } else {
        // the least numerator over a positive alpha, the largest over a negative one
        boolean low = gamma > 0 == alpha > 0;
        rest -= gamma * (low ? r.x[i].max() : r.x[i].min());
      }
    }
    if (arcCosts.isEmpty()) {
      return null;
    }
    long shift = t.singleton() ? t.value() : 0;
    long[] l = new long[n];
    Arrays.fill(l, NO_LAG);
    for (ValueEnumeration en = xv.domain.valueEnumeration(); en.hasMoreElements(); ) {
      int w = en.nextElement() - offset;
      if (w < 0 || w >= n) {
        continue;
      }
      long numerator = rest;
      boolean known = true;
      for (int k = 0; k < arcCosts.size() && known; k++) {
        Element e = arcCosts.get(k);
        int index = w + offset - e.first;
        known = index >= 0 && index < e.values.length;
        if (known) {
          numerator -= gammas.get(k) * e.values[index];
        }
      }
      if (known) {
        l[w] = Math.ceilDiv(numerator, alpha) - shift;
      }
    }
    return l;
  }

  // the time window reduction of a chain with lags (Desrochers, Desrosiers and Solomon): the
  // successor w of v is removed when T[v] + lag[v][w] exceeds the latest T[w] (or a[v]), the
  // earliest T[w] rises to the least arrival over its predecessors and the latest T[v] falls to the
  // latest departure over its successors, until nothing changes; the bounds go into the domains
  // of x and T. It returns the earliest and latest T of each node, or null when nothing holds.
  private long[][] reduceWindows(IntVar[] x, int offset, boolean[] fixed, Chain c) {
    int n = x.length;
    long[][] lag = c.lag;
    long[] lo = new long[n];
    long[] hi = new long[n];
    for (int v = 0; v < n; v++) {
      lo[v] = c.t[v].min();
      hi[v] = c.t[v].max();
    }
    boolean[][] gone = new boolean[n][];
    for (int v = 0; v < n; v++) {
      if (lag[v] != null) {
        gone[v] = new boolean[n];
      }
    }
    int removed = 0;
    boolean changed = true;
    for (int round = 0; changed && round < WINDOW_ROUNDS; round++) {
      changed = false;
      for (int v = 0; v < n; v++) {
        if (lag[v] == null) {
          continue;
        }
        long top = c.a[v].max();
        for (int w = 0; w < n; w++) {
          if (lag[v][w] != NO_LAG
              && !gone[v][w]
              && x[v].domain.contains(w + offset)
              && lo[v] + lag[v][w] > Math.min(hi[w], top)) {
            gone[v][w] = true;
            removed++;
            changed = true;
          }
        }
      }
      // the predecessors of each node: none of them may lack a lag
      long[] arrival = new long[n];
      Arrays.fill(arrival, Long.MAX_VALUE);
      boolean[] unknown = new boolean[n];
      for (int v = 0; v < n; v++) {
        long latest = Long.MIN_VALUE;
        boolean open = lag[v] == null;
        for (ValueEnumeration en = x[v].domain.valueEnumeration(); en.hasMoreElements(); ) {
          int w = en.nextElement() - offset;
          if (w < 0 || w >= n || w == v || gone[v] != null && gone[v][w]) {
            continue;
          }
          if (lag[v] == null || lag[v][w] == NO_LAG) {
            unknown[w] = true;
            open = true;
          } else {
            arrival[w] = Math.min(arrival[w], lo[v] + lag[v][w]);
            latest = Math.max(latest, hi[w] - lag[v][w]);
          }
        }
        if (!open && !fixed[v] && latest < hi[v]) {
          hi[v] = latest;
          changed = true;
        }
      }
      for (int w = 0; w < n; w++) {
        if (!unknown[w] && arrival[w] != Long.MAX_VALUE && arrival[w] > lo[w]) {
          lo[w] = arrival[w];
          changed = true;
        }
      }
      for (int v = 0; v < n; v++) {
        if (lo[v] > hi[v] || lo[v] > Integer.MAX_VALUE || hi[v] < Integer.MIN_VALUE) {
          // the model has no solution, which the search finds out itself
          return null;
        }
      }
    }
    for (int v = 0; v < n; v++) {
      if (gone[v] != null) {
        int left = 0;
        for (ValueEnumeration en = x[v].domain.valueEnumeration(); en.hasMoreElements(); ) {
          int w = en.nextElement() - offset;
          left += w >= 0 && w < n && gone[v][w] ? 0 : 1;
        }
        if (left == 0) {
          return null;
        }
      }
    }
    for (int v = 0; v < n; v++) {
      if (gone[v] != null) {
        for (int w = 0; w < n; w++) {
          if (gone[v][w] && x[v].domain.contains(w + offset)) {
            x[v].domain.inComplement(support.store.level, x[v], w + offset);
          }
        }
      }
      if (lo[v] > c.t[v].min() || hi[v] < c.t[v].max()) {
        c.t[v].domain.in(support.store.level, c.t[v], (int) lo[v], (int) hi[v]);
      }
    }
    windowArcs += removed;
    return new long[][] {lo, hi};
  }

  // the least value of a - t that a row of the model forces, or null
  private Long increment(IntVar a, IntVar t) {
    if (a == t) {
      return 0L;
    }
    if (a.singleton() || t.singleton()) {
      return null;
    }
    Long best = null;
    for (Row r : rows.getOrDefault(a, List.of())) {
      if (r.condition != null) {
        continue;
      }
      long alpha = 0;
      long beta = 0;
      for (int i = 0; i < r.x.length; i++) {
        if (r.x[i] == a) {
          alpha += r.a[i];
        } else if (r.x[i] == t) {
          beta += r.a[i];
        }
      }
      // alpha (a - t) + sum gamma d == rhs, or <= rhs with alpha < 0, so that
      // a - t >= (rhs - sum gamma d) / alpha, the least over the bounds of the other variables d
      if (alpha == 0 || beta != -alpha || !r.equation && alpha > 0) {
        continue;
      }
      long rest = r.rhs;
      for (int i = 0; i < r.x.length; i++) {
        if (r.x[i] != a && r.x[i] != t) {
          long gamma = r.a[i];
          // the least numerator over a positive alpha, the largest over a negative one
          boolean low = gamma > 0 == alpha > 0;
          rest -= gamma * (low ? r.x[i].max() : r.x[i].min());
        }
      }
      long q = Math.ceilDiv(rest, alpha);
      if (best == null || q > best) {
        best = q;
      }
    }
    return best;
  }

  // the rows of the arc costs: one for each element over a constant array of a customer, one for
  // the start nodes together; the number of rows
  private int costRows(
      IntVar[] x,
      int offset,
      int[] customer,
      List<Integer> customers,
      List<Integer> starts,
      boolean[] end,
      IntVar[][] arc,
      List<Constraint> posted) {
    int n = x.length;
    int k = customers.size() - 1;
    int made = 0;
    for (int i = 1; i <= k; i++) {
      int v = customers.get(i);
      int read = 0;
      for (Element e : elements.getOrDefault(x[v], List.of())) {
        if (e.values == null || read == MAX_COSTS) {
          continue;
        }
        read++;
        // d = sum c[j] b[i,j] + c[end] b[i,0]
        List<IntVar> vs = new ArrayList<>();
        List<Long> ws = new ArrayList<>();
        long endLow = Long.MAX_VALUE;
        long endHigh = Long.MIN_VALUE;
        boolean ok = true;
        for (ValueEnumeration en = x[v].domain.valueEnumeration(); en.hasMoreElements() && ok; ) {
          int value = en.nextElement();
          int w = value - offset;
          int at = value - e.first;
          if (w < 0 || w >= n || at < 0 || at >= e.values.length) {
            continue;
          }
          if (customer[w] > 0 && arc[i][customer[w]] != null) {
            vs.add(arc[i][customer[w]]);
            ws.add((long) e.values[at]);
          } else if (end[w]) {
            endLow = Math.min(endLow, e.values[at]);
            endHigh = Math.max(endHigh, e.values[at]);
          }
        }
        if (arc[i][0] != null && endLow != Long.MAX_VALUE) {
          vs.add(arc[i][0]);
          ws.add(endLow);
        }
        if (costRows(List.of(e.value), vs, ws, 0, endLow == endHigh || arc[i][0] == null, posted)) {
          made++;
        }
      }
    }
    // the start nodes: the same costs to each customer, read by the depot's arcs
    List<Element> kinds = elements.getOrDefault(x[starts.get(0)], List.of());
    for (Element kind : kinds) {
      if (kind.values == null) {
        continue;
      }
      long[] c = new long[k + 1];
      boolean[] has = new boolean[k + 1];
      List<Element> chosen = new ArrayList<>();
      for (int s : starts) {
        Element match = null;
        for (Element e : elements.getOrDefault(x[s], List.of())) {
          if (e.values != null && sameCustomerCosts(kind, e, offset, customers)) {
            match = e;
            break;
          }
        }
        if (match == null) {
          chosen = null;
          break;
        }
        chosen.add(match);
      }
      if (chosen == null) {
        continue;
      }
      for (int j = 1; j <= k; j++) {
        int at = customers.get(j) + offset - kind.first;
        if (at >= 0 && at < kind.values.length) {
          c[j] = kind.values[at];
          has[j] = true;
        }
      }
      long endLow = Long.MAX_VALUE;
      long endHigh = Long.MIN_VALUE;
      for (int si = 0; si < starts.size(); si++) {
        int s = starts.get(si);
        Element e = chosen.get(si);
        for (ValueEnumeration en = x[s].domain.valueEnumeration(); en.hasMoreElements(); ) {
          int value = en.nextElement();
          int w = value - offset;
          int at = value - e.first;
          if (w >= 0 && w < n && end[w] && at >= 0 && at < e.values.length) {
            endLow = Math.min(endLow, e.values[at]);
            endHigh = Math.max(endHigh, e.values[at]);
          }
        }
      }
      if (endLow == Long.MAX_VALUE) {
        endLow = 0;
        endHigh = 0;
      }
      // sum d[s] - sum (c[j] - c[end]) b[0,j] = c[end] |starts|
      List<IntVar> vs = new ArrayList<>();
      List<Long> ws = new ArrayList<>();
      boolean exact = endLow == endHigh;
      for (int j = 1; j <= k && exact; j++) {
        if (arc[0][j] != null && !has[j]) {
          exact = false;
        }
      }
      for (int j = 1; j <= k; j++) {
        if (arc[0][j] != null) {
          vs.add(arc[0][j]);
          ws.add(has[j] ? c[j] - endLow : 0);
        }
      }
      List<IntVar> ds = new ArrayList<>();
      for (Element e : chosen) {
        ds.add(e.value);
      }
      if (costRows(ds, vs, ws, endLow * starts.size(), exact, posted)) {
        made++;
      }
    }
    return made;
  }

  private static boolean sameCustomerCosts(
      Element a, Element b, int offset, List<Integer> customers) {
    if (a == b) {
      return true;
    }
    for (int j = 1; j < customers.size(); j++) {
      int value = customers.get(j) + offset;
      int i = value - a.first;
      int l = value - b.first;
      boolean ia = i >= 0 && i < a.values.length;
      boolean ib = l >= 0 && l < b.values.length;
      if (ia != ib || ia && a.values[i] != b.values[l]) {
        return false;
      }
    }
    return true;
  }

  // sum ds - sum ws vs == rhs (exact) or >= rhs
  private static boolean costRows(
      List<IntVar> ds,
      List<IntVar> vs,
      List<Long> ws,
      long rhs,
      boolean exact,
      List<Constraint> posted) {
    List<IntVar> list = new ArrayList<>();
    List<Integer> weights = new ArrayList<>();
    long r = rhs;
    for (IntVar d : ds) {
      r = term(d, 1, list, weights, r);
    }
    boolean any = false;
    for (int i = 0; i < vs.size(); i++) {
      long w = ws.get(i);
      if (Math.abs(w) > Integer.MAX_VALUE / 4) {
        return false;
      }
      if (w != 0) {
        list.add(vs.get(i));
        weights.add((int) -w);
        any = true;
      }
    }
    if (!any || Math.abs(r) > Integer.MAX_VALUE) {
      return false;
    }
    posted.add(
        new LinearInt(
                list.toArray(new IntVar[0]),
                weights.stream().mapToInt(Integer::intValue).toArray(),
                exact ? "==" : ">=",
                (int) r)
            .setDegreeWeight(0));
    return true;
  }
}
