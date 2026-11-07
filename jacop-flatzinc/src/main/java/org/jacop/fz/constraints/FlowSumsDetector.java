/*
 * FlowSumsDetector.java
 * <p>
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.FlowSums;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds systems of sums with unit coefficients in which every variable is in at most two sums
 * and the sums form a bipartite graph, and posts {@link FlowSums} for each as a redundant
 * constraint. A sum is a non-reified int_lin_eq, int_lin_le, bool_lin_eq or bool_lin_le whose
 * coefficients are all 1 or all -1, except at most one variable of the opposite sign, the total:
 * {@code sum(x) = total + c}, {@code sum(x) = c}, {@code sum(x) <= c} or {@code sum(x) >= c}. Sums
 * over the same variables are merged into one range. That is what MiniZinc makes of the games and
 * the final points of a league ({@code points[g, 1] + points[g, 2]} in 2..3 and {@code final[t] =
 * initial[t] + sum of t's points}, soccer-computational), and of the row and column sums of an
 * integer matrix. Each sum still propagates on its own; the flow adds Hoffman's conditions over
 * every set of sums together, and the least and greatest totals they allow (see {@link FlowSums}).
 *
 * <p>A variable in more than two sums takes the two smallest; the larger sums are left out. A
 * component of the graph with an odd cycle, fewer than {@link #MIN_NODES} sums, no sum of three or
 * more variables, or more than {@link #MAX_EDGES} variables is left out.
 *
 * <p>Setting the system property {@code org.jacop.fz.flowSums} to false turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class FlowSumsDetector implements ParserTreeConstants {

  /** The least number of sums in a component. */
  static final int MIN_NODES = Integer.getInteger("jacop.fz.flowSumsNodes", 4);

  /** The most variables in a component. */
  static final int MAX_EDGES = Integer.getInteger("jacop.fz.flowSumsEdges", 100_000);

  private final Support support;

  // the edge variables, by first appearance
  private final Map<IntVar, Integer> index = new IdentityHashMap<>();
  private final List<IntVar> vars = new ArrayList<>();

  // a sum over edges[] within [min, max], and equal to total + offset when total is not null
  private static final class Sum {
    final int[] edges;
    IntVar total;
    long offset;
    long min = Long.MIN_VALUE;
    long max = Long.MAX_VALUE;
    boolean live = true;
    int color = -1;

    Sum(int[] edges) {
      this.edges = edges;
    }
  }

  private final List<Sum> sums = new ArrayList<>();
  private final Map<String, Sum> byEdges = new HashMap<>();

  /** Statistics: the constraints posted. */
  int posted;

  /** Statistics: the edges of the constraints posted. */
  int postedEdges;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public FlowSumsDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.flowSums is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.flowSums"));
  }

  /**
   * It reads the sums of the model and posts their flows.
   *
   * @param astTree the root of the parsed model.
   * @return the number of constraints posted
   * @throws FailException when a flow fails as it is posted.
   */
  public int detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (sums.size() < MIN_NODES) {
      return 0;
    }
    int[] count = new int[vars.size()];
    List<List<Integer>> sumsOf = new ArrayList<>();
    for (int v = 0; v < vars.size(); v++) {
      sumsOf.add(new ArrayList<>());
    }
    for (int s = 0; s < sums.size(); s++) {
      for (int v : sums.get(s).edges) {
        count[v]++;
        sumsOf.get(v).add(s);
      }
    }
    // a variable in more than two sums keeps the two smallest
    for (int v = 0; v < vars.size(); v++) {
      while (count[v] > 2) {
        Sum largest = null;
        for (int s : sumsOf.get(v)) {
          Sum sum = sums.get(s);
          if (sum.live && (largest == null || sum.edges.length > largest.edges.length)) {
            largest = sum;
          }
        }
        if (largest == null) {
          break;
        }
        largest.live = false;
        for (int u : largest.edges) {
          count[u]--;
        }
      }
    }
    // components over the shared variables, two-coloured
    for (int s = 0; s < sums.size(); s++) {
      Sum start = sums.get(s);
      if (!start.live || start.color >= 0) {
        continue;
      }
      List<Integer> members = new ArrayList<>();
      boolean bipartite = true;
      ArrayDeque<Integer> queue = new ArrayDeque<>();
      start.color = 0;
      queue.add(s);
      while (!queue.isEmpty()) {
        int t = queue.poll();
        members.add(t);
        Sum sum = sums.get(t);
        for (int v : sum.edges) {
          for (int u : sumsOf.get(v)) {
            Sum other = sums.get(u);
            if (u == t || !other.live) {
              continue;
            }
            if (other.color < 0) {
              other.color = 1 - sum.color;
              queue.add(u);
            } else if (other.color == sum.color) {
              bipartite = false;
            }
          }
        }
      }
      if (bipartite) {
        post(members, sumsOf);
      }
    }
    if (support.options.debug() && posted > 0) {
      FzConsole.println("% FlowSums: " + posted + " constraints, " + postedEdges + " edges");
    }
    return posted;
  }

  private void post(List<Integer> members, List<List<Integer>> sumsOf) {
    if (members.size() < MIN_NODES) {
      return;
    }
    int widest = 0;
    int[] sideCount = new int[2];
    Map<Integer, Integer> local = new HashMap<>();
    for (int s : members) {
      Sum sum = sums.get(s);
      widest = Math.max(widest, sum.edges.length);
      local.put(s, sideCount[sum.color]++);
    }
    if (widest < 3 || sideCount[0] < 2 || sideCount[1] < 2) {
      return;
    }
    // the edges, each with its sums on both sides
    Map<Integer, int[]> ends = new HashMap<>();
    List<Integer> order = new ArrayList<>();
    for (int s : members) {
      Sum sum = sums.get(s);
      for (int v : sum.edges) {
        int[] e = ends.get(v);
        if (e == null) {
          e = new int[] {-1, -1};
          ends.put(v, e);
          order.add(v);
        }
        e[sum.color] = local.get(s);
      }
    }
    if (order.size() > MAX_EDGES) {
      return;
    }
    IntVar[] x = new IntVar[order.size()];
    int[] left = new int[x.length];
    int[] right = new int[x.length];
    Map<IntVar, Boolean> used = new IdentityHashMap<>();
    for (int k = 0; k < x.length; k++) {
      int v = order.get(k);
      x[k] = vars.get(v);
      left[k] = ends.get(v)[0];
      right[k] = ends.get(v)[1];
      used.put(x[k], Boolean.TRUE);
    }
    FlowSums.Node[][] nodes = {new FlowSums.Node[sideCount[0]], new FlowSums.Node[sideCount[1]]};
    for (int s : members) {
      Sum sum = sums.get(s);
      IntVar total = sum.total;
      // a total that is also an edge, or the total of another sum, only keeps its range
      if (total != null && used.put(total, Boolean.TRUE) != null) {
        total = null;
      }
      long offset = total == null ? 0 : sum.offset;
      if (offset < Integer.MIN_VALUE + 1L || offset > Integer.MAX_VALUE - 1L) {
        return;
      }
      int min = (int) Math.max(Integer.MIN_VALUE, sum.min);
      int max = (int) Math.min(Integer.MAX_VALUE, sum.max);
      nodes[sum.color][local.get(s)] = new FlowSums.Node(total, (int) offset, min, max);
    }
    FlowSums c;
    try {
      c = new FlowSums(x, left, right, nodes[0], nodes[1]);
    } catch (IllegalArgumentException e) {
      return;
    }
    c.setRedundant(true);
    support.pose(c);
    posted++;
    postedEdges += x.length;
  }

  private void collect(ASTConstElem node) {
    String name = node.getName();
    boolean eq = "int_lin_eq".equals(name) || "bool_lin_eq".equals(name);
    boolean le = "int_lin_le".equals(name) || "bool_lin_le".equals(name);
    if ((!eq && !le) || node.jjtGetNumChildren() != 3) {
      return;
    }
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (a == null || y == null || a.length != y.length || a.length < 2) {
      return;
    }
    IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    long rhs;
    IntVar extra = null;
    if (c.singleton()) {
      rhs = c.value();
    } else {
      // sum(a y) = c, with c a variable: the term -c
      rhs = 0;
      extra = c;
    }
    // the terms, constants moved to the right hand side
    Map<IntVar, Long> terms = new IdentityHashMap<>();
    List<IntVar> termOrder = new ArrayList<>();
    for (int k = 0; k <= y.length; k++) {
      IntVar v = k < y.length ? y[k] : extra;
      long w = k < y.length ? a[k] : -1;
      if (v == null || w == 0) {
        continue;
      }
      if (v.singleton()) {
        rhs -= w * v.value();
        continue;
      }
      Long old = terms.put(v, terms.getOrDefault(v, 0L) + w);
      if (old == null) {
        termOrder.add(v);
      }
    }
    int plus = 0;
    int minus = 0;
    IntVar onlyPlus = null;
    IntVar onlyMinus = null;
    for (IntVar v : termOrder) {
      long w = terms.get(v);
      if (w == 1) {
        plus++;
        onlyPlus = v;
      } else if (w == -1) {
        minus++;
        onlyMinus = v;
      } else if (w != 0) {
        return;
      }
    }
    int sign;
    IntVar total = null;
    if (minus == 0 || (minus == 1 && plus >= 2)) {
      sign = 1;
      total = minus == 1 ? onlyMinus : null;
    } else if (plus == 0 || (plus == 1 && minus >= 2)) {
      sign = -1;
      total = plus == 1 ? onlyPlus : null;
    } else {
      return;
    }
    if (total != null && !eq) {
      // sum(x) <= total + c is not a node of the flow
      return;
    }
    List<Integer> edgeList = new ArrayList<>();
    for (IntVar v : termOrder) {
      if (v != total && terms.get(v) != 0) {
        edgeList.add(node(v));
      }
    }
    if (edgeList.size() < 2) {
      return;
    }
    int[] edges = edgeList.stream().mapToInt(Integer::intValue).sorted().toArray();
    for (int k = 1; k < edges.length; k++) {
      if (edges[k] == edges[k - 1]) {
        return;
      }
    }
    // sign * (sum(x) - total) (= or <=) rhs
    long bound = sign * rhs;
    String key = Arrays.toString(edges);
    Sum sum = byEdges.get(key);
    if (sum == null) {
      sum = new Sum(edges);
      byEdges.put(key, sum);
      sums.add(sum);
    }
    if (total != null) {
      if (sum.total == null) {
        sum.total = total;
        sum.offset = bound;
      }
    } else if (eq) {
      sum.min = Math.max(sum.min, bound);
      sum.max = Math.min(sum.max, bound);
    } else if (sign > 0) {
      sum.max = Math.min(sum.max, rhs);
    } else {
      sum.min = Math.max(sum.min, -rhs);
    }
  }

  private int node(IntVar x) {
    return index.computeIfAbsent(
        x,
        v -> {
          vars.add(v);
          return vars.size() - 1;
        });
  }
}
