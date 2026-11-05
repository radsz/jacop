/*
 * RoutesDetector.java
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Routes;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds vehicle routes written as 0/1 arc variables and posts a redundant {@link Routes}.
 *
 * <p>The pattern is the two-index vehicle routing model with Miller-Tucker-Zemlin load rows (the
 * vrp model of the MiniZinc Challenge):
 *
 * <ul>
 *   <li>{@code sum(i) x[i,j] = 1} and {@code sum(j) x[i,j] = 1} for every customer, so that every
 *       arc variable between customers is in one "out" row and one "in" row, and a variable in a
 *       single row is an arc from or to the depot;
 *   <li>{@code a*u[i] - a*u[j] + c*x[i,j] <= r} for every arc between customers, so that {@code
 *       x[i,j] = 1} forces {@code u[j] >= u[i] + d} with {@code d = ceil((c - r) / a) > 0}.
 * </ul>
 *
 * <p>The load rows forbid every circuit of customers (the loads would have to grow round it), and
 * {@code u} grows by at least the demand of each customer along a route and stays within its
 * domain, so every route carries at most the largest bound of the loads. Routes is therefore
 * implied: its demands are the smallest increments into each customer, the first customer's demand
 * also at most the least load it can have, and its capacity is the largest load. The model's own
 * constraints all stay.
 *
 * <p>System property org.jacop.fz.routes=false turns the detection off.
 */
public class RoutesDetector implements ParserTreeConstants {

  // the fewest customers worth a Routes
  private static final int MIN_CUSTOMERS = 3;

  private final Support support;

  // whether the routes found are imposed, or only recorded for the neighbourhoods of LNS
  private final boolean impose;

  // exactly-one rows: each a list of 0/1 variables
  private final List<IntVar[]> rows = new ArrayList<>();

  // the exactly-one rows of each 0/1 variable
  private final Map<IntVar, int[]> rowsOf = new IdentityHashMap<>();

  // the load row of each arc variable: tail load, head load, smallest increment
  private final Map<IntVar, Load> loads = new IdentityHashMap<>();

  private record Load(IntVar tail, IntVar head, long increment) {}

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public RoutesDetector(Support support) {
    this(support, true);
  }

  /**
   * It constructs a detector that imposes the routes it finds, or only records them for the route
   * neighbourhoods of large neighbourhood search (see {@code Tables.lnsRoutes()}).
   *
   * @param support the parser support.
   * @param impose true to impose the routes as redundant constraints.
   */
  public RoutesDetector(Support support, boolean impose) {
    this.support = support;
    this.impose = impose;
  }

  /**
   * It tells if the detection is on. It is off by default: on the vrp instances of the MiniZinc
   * Challenge the redundant Routes leaves the results level.
   *
   * @return true if the system property org.jacop.fz.routes is true.
   */
  public static boolean enabled() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.routes"));
  }

  /**
   * It scans the constraint items of the model and posts a Routes for each routing structure found.
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
    if (rows.size() < 2 * MIN_CUSTOMERS || loads.isEmpty()) {
      return;
    }
    components();
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private static boolean zeroOne(IntVar v) {
    return v.min() >= 0 && v.max() <= 1;
  }

  private void collect(ASTConstElem node) {
    String name = node.getName();
    if (!name.equals("int_lin_eq") && !name.equals("int_lin_le") && !name.equals("bool_lin_eq")) {
      return;
    }
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    if (a == null || x == null || a.length != x.length) {
      return;
    }
    int r = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (name.equals("int_lin_le")) {
      load(a, x, r);
    } else {
      exactlyOne(a, x, r);
    }
  }

  // sum x = 1 over at least two 0/1 variables, no variable twice
  private void exactlyOne(int[] a, IntVar[] x, int r) {
    if (x.length < 2 || r != 1 && r != -1) {
      return;
    }
    for (int k = 0; k < a.length; k++) {
      if (a[k] != r || !zeroOne(x[k])) {
        return;
      }
    }
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (IntVar v : x) {
      if (seen.put(v, Boolean.TRUE) != null) {
        return;
      }
    }
    int index = rows.size();
    rows.add(x);
    for (IntVar v : x) {
      int[] old = rowsOf.get(v);
      int[] now;
      if (old == null) {
        now = new int[] {index};
      } else {
        now = Arrays.copyOf(old, old.length + 1);
        now[old.length] = index;
      }
      rowsOf.put(v, now);
    }
  }

  // a*u - a*w + c*x <= r with x 0/1, a > 0 and c > 0: x = 1 forces w >= u + ceil((c - r) / a)
  private void load(int[] a, IntVar[] x, int r) {
    if (x.length != 3) {
      return;
    }
    int arc = -1;
    int plus = -1;
    int minus = -1;
    for (int k = 0; k < 3; k++) {
      if (zeroOne(x[k]) && a[k] > 0 && arc < 0) {
        arc = k;
      } else if (a[k] > 0) {
        plus = k;
      } else if (a[k] < 0) {
        minus = k;
      }
    }
    if (arc < 0 || plus < 0 || minus < 0 || a[plus] != -a[minus] || x[plus] == x[minus]) {
      return;
    }
    long c = a[arc];
    long step = a[plus];
    long increment = Math.floorDiv(c - r + step - 1, step);
    if (increment <= 0 || loads.containsKey(x[arc])) {
      return;
    }
    loads.put(x[arc], new Load(x[plus], x[minus], increment));
  }

  // the routing structures: exactly-one rows split into out rows and in rows by their arcs
  private void components() {
    int m = rows.size();
    int[] color = new int[m];
    Arrays.fill(color, -1);
    for (int start = 0; start < m; start++) {
      if (color[start] >= 0) {
        continue;
      }
      List<Integer> component = new ArrayList<>();
      boolean ok = true;
      color[start] = 0;
      component.add(start);
      for (int q = 0; q < component.size(); q++) {
        int row = component.get(q);
        for (IntVar v : rows.get(row)) {
          int[] rs = rowsOf.get(v);
          if (rs.length > 2) {
            ok = false;
            continue;
          }
          for (int other : rs) {
            if (other == row) {
              continue;
            }
            if (color[other] < 0) {
              color[other] = 1 - color[row];
              component.add(other);
            } else if (color[other] == color[row]) {
              ok = false;
            }
          }
        }
      }
      if (ok) {
        routes(component, color);
      }
    }
  }

  // one structure: the arcs between rows of different colours must each have a load row
  private void routes(List<Integer> component, int[] color) {
    for (int side = 0; side < 2; side++) {
      if (tryRoutes(component, color, side)) {
        return;
      }
    }
  }

  // side is the colour of the out rows
  private boolean tryRoutes(List<Integer> component, int[] color, int side) {
    // the load variable of each row: the tail load of its arcs (out rows) or the head load (in)
    Map<Integer, IntVar> loadOf = new HashMap<>();
    for (int row : component) {
      for (IntVar v : rows.get(row)) {
        if (rowsOf.get(v).length != 2) {
          continue;
        }
        Load l = loads.get(v);
        if (l == null) {
          return false;
        }
        IntVar u = color[row] == side ? l.tail : l.head;
        IntVar known = loadOf.putIfAbsent(row, u);
        if (known != null && known != u) {
          return false;
        }
      }
    }
    if (loadOf.size() != component.size()) {
      return false;
    }
    // node of each load variable: its out row and its in row
    Map<IntVar, Integer> node = new IdentityHashMap<>();
    List<IntVar> nodes = new ArrayList<>();
    nodes.add(null);
    Map<IntVar, int[]> sides = new IdentityHashMap<>();
    for (int row : component) {
      IntVar u = loadOf.get(row);
      int[] s = sides.computeIfAbsent(u, k -> new int[] {-1, -1});
      int which = color[row] == side ? 0 : 1;
      if (s[which] >= 0) {
        return false;
      }
      s[which] = row;
      if (!node.containsKey(u)) {
        node.put(u, nodes.size());
        nodes.add(u);
      }
    }
    for (int[] s : sides.values()) {
      if (s[0] < 0 || s[1] < 0) {
        return false;
      }
    }
    int customers = nodes.size() - 1;
    if (customers < MIN_CUSTOMERS) {
      return false;
    }
    // the arcs, the smallest increment into each customer, and the largest load
    List<int[]> arcs = new ArrayList<>();
    List<IntVar> literals = new ArrayList<>();
    long[] demand = new long[customers + 1];
    Arrays.fill(demand, Long.MAX_VALUE);
    Map<IntVar, Boolean> done = new IdentityHashMap<>();
    for (int row : component) {
      boolean out = color[row] == side;
      int here = node.get(loadOf.get(row));
      for (IntVar v : rows.get(row)) {
        if (rowsOf.get(v).length == 1) {
          arcs.add(out ? new int[] {here, 0} : new int[] {0, here});
          literals.add(v);
        } else if (done.put(v, Boolean.TRUE) == null) {
          Load l = loads.get(v);
          int t = node.get(l.tail);
          int h = node.get(l.head);
          if (t == h) {
            return false;
          }
          arcs.add(new int[] {t, h});
          literals.add(v);
          demand[h] = Math.min(demand[h], l.increment);
        }
      }
    }
    long capacity = 0;
    int[] demands = new int[customers + 1];
    for (int j = 1; j <= customers; j++) {
      IntVar u = nodes.get(j);
      // the first customer of a route adds its least load, not an increment
      if (u.min() < 0) {
        return false;
      }
      capacity = Math.max(capacity, u.max());
      demands[j] = (int) Math.min(demand[j], u.min());
    }
    int[] tails = new int[arcs.size()];
    int[] heads = new int[arcs.size()];
    for (int k = 0; k < tails.length; k++) {
      tails[k] = arcs.get(k)[0];
      heads[k] = arcs.get(k)[1];
    }
    Routes routes =
        new Routes(
            tails,
            heads,
            literals.toArray(new IntVar[0]),
            demands,
            (int) Math.min(capacity, Integer.MAX_VALUE));
    // the exactly-one rows keep the degrees
    routes.setDegrees(false);
    // redundant, so degree-based variable selections see the degrees of the model
    routes.setDegreeWeight(0);
    if (!impose) {
      support.dictionary.addLnsRoutes(routes);
      if (support.options.debug()) {
        FzConsole.println(
            "% routes for LNS: " + customers + " customers, " + tails.length + " arcs");
      }
      return true;
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% redundant Routes: "
              + customers
              + " customers, "
              + tails.length
              + " arcs, capacity "
              + capacity);
    }
    support.delayedConstraints.add(routes);
    return true;
  }
}
