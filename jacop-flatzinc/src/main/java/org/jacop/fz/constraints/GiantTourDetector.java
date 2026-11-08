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
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Routes;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
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
 * objective is the sum of the arc costs of the tour. On TSPLIB instances of 70 to 152 cities its
 * bound is within 1 % of the optimum (median 0.07 %, against 0.75 % with free search and 10 % with
 * the model's search without it), and proofs are often faster, but each LP solve costs time, so on
 * tours of more than about 120 cities the solutions found within a time limit can be worse.
 *
 * <p>All the constraints of the model stay. System property org.jacop.fz.giantTour=false turns the
 * detection off; org.jacop.fz.routes=false turns it off with the other routes.
 *
 * <p>References: P. Kilby and P. Shaw, Vehicle Routing, in Handbook of Constraint Programming,
 * Elsevier, 2006 (the giant-tour model); J. Lysgaard, A. N. Letchford and R. W. Eglese, A new
 * branch-and-cut algorithm for the capacitated vehicle routing problem, Mathematical Programming
 * 100(2), 2004 (the two-index relaxation and its rounded capacity cuts); G. Dantzig, R. Fulkerson
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

  // the most arcs of such a tour
  private static final int MAX_TSP_ARCS = Integer.getInteger("org.jacop.fz.tspArcs", 40_000);

  // the most variables of a row read for an increment: a[n] = T[n] + slack[n] + d[n] has four
  private static final int MAX_ROW = 5;

  // the most elements over a constant array read for one node
  private static final int MAX_COSTS = 4;

  private final Support support;

  private final List<Tour> tours = new ArrayList<>();

  private static final class Tour {
    final IntVar[] x;
    final int offset;

    Tour(IntVar[] x, int offset) {
      this.x = x;
      this.offset = offset;
    }
  }

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
            collect((ASTConstElem) item);
          }
        }
      }
    }
    for (Tour t : tours) {
      tour(t.x, t.offset);
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
      case "jacop_circuit" -> tours.add(new Tour(support.getVarArray(child(node, 0)), 1));
      case "jacop_circuit_offset" ->
          tours.add(new Tour(support.getVarArray(child(node, 0)), support.getInt(scalar(node, 1))));
      case "array_int_element" -> element(node, null, support.getIntArray(child(node, 1)), 1);
      case "array_var_int_element" -> element(node, support.getVarArray(child(node, 1)), null, 1);
      case "jacop_array_var_int_element_nonshifted" ->
          element(node, support.getVarArray(child(node, 1)), null, support.getInt(scalar(node, 3)));
      case "int_lin_eq" -> row(node, true);
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
    if (r.getType() == 2 && support.dictionary.getVariable(r.getIdent()) != null) {
      IntVar v = support.dictionary.getVariable(r.getIdent());
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
    for (IntVar v : vs) {
      rows.computeIfAbsent(v, k -> new ArrayList<>()).add(row);
    }
  }

  // ---------------------------------------------------------------------------------------------

  private void tour(IntVar[] x, int offset) {
    int n = x.length;
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
    if (tsp && !Boolean.getBoolean("org.jacop.fz.tsp")) {
      return;
    }
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
    for (Chain c : chains(x, offset, fixed, target, customers)) {
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
              + " tour sums");
    }
    support.delayedConstraints.addAll(posted);
    support.dictionary.addAuxiliaryVariables(literals);
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
      if (demand == null || !localRows) {
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
      out.add(new Chain(t, nonNegative ? demand : null, sum));
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
