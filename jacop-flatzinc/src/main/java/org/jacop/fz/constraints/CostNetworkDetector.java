/*
 * CostNetworkDetector.java
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
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import org.jacop.constraints.cfn.CostNetwork;
import org.jacop.constraints.cfn.CostNetworkBound;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.fz.constraints.IntensionTableDetector.Bound;
import org.jacop.fz.constraints.IntensionTableDetector.Item;
import org.jacop.fz.constraints.IntensionTableDetector.Op;
import org.jacop.fz.constraints.IntensionTableDetector.Tabulator;

/**
 * Reads the cost function network of a model whose objective is a sum of unary and binary cost
 * functions, the form of weighted constraint satisfaction problems written in MiniZinc (CELAR radio
 * link frequency assignment, SPOT5 satellite scheduling, protein design), and builds the {@link
 * CostNetworkBound} of the objective.
 *
 * <ol>
 *   <li>the objective is defined by a linear equation {@code z = c + Σ w_k t_k};
 *   <li>each term t<sub>k</sub> is defined by the constraints reached from it through internal
 *       variables (not output, in at most two constraints besides the objective's equation): a
 *       table over t<sub>k</sub> and its other variables, or a chain of functions, reifications and
 *       linear equations such as {@code w * bool2int(abs(x - y) <= k)}. The other variables met, at
 *       most two, are the term's variables; its cost function is the least w<sub>k</sub>
 *       t<sub>k</sub> over the solutions of these constraints for each value pair, by the small
 *       search of {@link IntensionTableDetector}, and a pair without a solution is forbidden;
 *   <li>the other constraints over at most two network variables (through internal ones), such as
 *       the binary tables of SPOT5 and the hard distance constraints of CELAR, become hard binary
 *       functions; higher arities are left out.
 * </ol>
 *
 * Every function is the projection of some constraints of the model, so every solution of the model
 * costs at least the network's cost: the bound holds whatever is left out. A term the network does
 * not cover adds its least value. Switched on by {@code -Dorg.jacop.fz.costNetwork=true}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class CostNetworkDetector implements ParserTreeConstants {

  /** The values of a network variable at most. */
  static final int MAX_DOMAIN = Integer.getInteger("org.jacop.cfn.maxDomain", 1024);

  /** The binary cost entries at most, over all functions. */
  static final long MAX_ENTRIES = Long.getLong("org.jacop.cfn.maxEntries", 12_000_000L);

  /** The search nodes to tabulate one group at most. */
  static final long GROUP_NODES = 300_000;

  /** The search nodes over all groups at most. */
  static final boolean UNARY_ONLY = Boolean.getBoolean("org.jacop.cfn.unaryOnly");

  static final long BUDGET = Long.getLong("org.jacop.cfn.nodes", 40_000_000L);

  /** The constraints of one group at most. */
  static final int MAX_GROUP = 16;

  private final Support support;

  // one constraint of the model: an item the tabulator reads, or a table, or another constraint
  private static final class Rec {
    final Item item;
    final IntVar[] tableScope;
    final int[] tableTuples;
    final List<IntVar> vars = new ArrayList<>();
    boolean used;

    Rec(Item item, IntVar[] tableScope, int[] tableTuples, List<IntVar> vars) {
      this.item = item;
      this.tableScope = tableScope;
      this.tableTuples = tableTuples;
      Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
      for (IntVar v : vars) {
        if (!v.singleton() && seen.add(v)) {
          this.vars.add(v);
        }
      }
    }
  }

  private final List<Rec> recs = new ArrayList<>();

  /** Statistics: terms covered, terms left out, hard functions, tabulation nodes, seconds. */
  public int terms;

  public int termsLeft;

  public int hard;

  /** The terms that became binary cost functions. */
  public int binaryTerms;

  public long nodes;

  public double seconds;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public CostNetworkDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the bound is on.
   *
   * @return true if the system property org.jacop.fz.costNetwork is true.
   */
  public static boolean enabled() {
    return Boolean.getBoolean("org.jacop.fz.costNetwork");
  }

  /**
   * It reads the constraint items of the model.
   *
   * @param astTree the root of the parsed model.
   */
  public void collect(SimpleNode astTree) {
    support.forEachConstraint(
        astTree,
        node -> {
          String name = node.getName();
          try {
            if (name.equals("jacop_table_int")) {
              IntVar[] scope = support.getVarArray((SimpleNode) node.jjtGetChild(0));
              int[] tuples = support.getIntArray((SimpleNode) node.jjtGetChild(1));
              if (scope != null && tuples != null) {
                recs.add(new Rec(null, scope, tuples, List.of(scope)));
              }
              return;
            }
          } catch (RuntimeException _) {
            // fall through: an argument the detector does not read
          }
          Item it = Item.read(support, node);
          if (it != null) {
            recs.add(new Rec(it, null, null, List.of(it.terms)));
            return;
          }
          Map<IntVar, Integer> found = new IdentityHashMap<>();
          PartialCopyDetector.countVariables(support, node, found);
          recs.add(new Rec(null, null, null, new ArrayList<>(found.keySet())));
        });
  }

  /**
   * It builds the bound over the current domains.
   *
   * @param objective the objective variable.
   * @param maximize whether it is maximised.
   * @param output whether a variable is output (output variables are never internal).
   * @param debug print what was found.
   * @return the bound, not imposed, or null when the objective is not such a sum.
   */
  public CostNetworkBound build(
      IntVar objective, boolean maximize, Predicate<IntVar> output, boolean debug) {
    long start = System.nanoTime();
    try {
      return buildNetwork(objective, maximize, output, debug);
    } finally {
      seconds = (System.nanoTime() - start) / 1e9;
      recs.clear();
    }
  }

  private CostNetworkBound buildNetwork(
      IntVar objective, boolean maximize, Predicate<IntVar> output, boolean debug) {
    // the objective's defining equation: a z + Σ a_k t_k = c with |a| = 1
    Rec def = null;
    int zAt = -1;
    for (Rec r : recs) {
      if (r.item != null && r.item.op == Op.LIN_EQ) {
        IntVar[] t = r.item.terms;
        int at = -1;
        int count = 0;
        for (int k = 0; k < t.length; k++) {
          if (t[k] == objective) {
            at = k;
            count++;
          }
        }
        if (count == 1 && Math.abs(r.item.coefficients[at]) == 1) {
          def = r;
          zAt = at;
          break;
        }
      }
    }
    if (def == null) {
      return null;
    }
    long sign = maximize ? -1 : 1;
    int a = def.item.coefficients[zAt];
    int[] coef = def.item.coefficients;
    IntVar[] dt = def.item.terms;
    // sign z = sign (c - Σ a_k t_k) / a
    long constant = sign * coef[coef.length - 1] / a;
    Map<IntVar, Long> weight = new LinkedHashMap<>();
    for (int k = 0; k < dt.length; k++) {
      if (k == zAt) {
        continue;
      }
      long w = -sign * coef[k] / a;
      if (dt[k].singleton()) {
        constant += w * dt[k].value();
      } else if (w != 0) {
        weight.merge(dt[k], w, Long::sum);
      }
    }
    def.used = true;
    // occurrences outside the objective's equation
    Map<IntVar, List<Rec>> occurs = new IdentityHashMap<>();
    for (Rec r : recs) {
      if (r != def) {
        for (IntVar v : r.vars) {
          occurs.computeIfAbsent(v, k -> new ArrayList<>()).add(r);
        }
      }
    }
    Predicate<IntVar> internal =
        v ->
            v != objective
                && !weight.containsKey(v)
                && !output.test(v)
                && occurs.getOrDefault(v, List.of()).size() <= 2;

    // the terms: their groups and variables
    Map<IntVar, Group> termGroups = new LinkedHashMap<>();
    List<IntVar> netVars = new ArrayList<>();
    Map<IntVar, Integer> netIndex = new IdentityHashMap<>();
    for (IntVar t : weight.keySet()) {
      Group g = group(t, occurs, internal, weight.keySet());
      if (g == null || !tabulable(g, t) || !small(g.leaves)) {
        continue;
      }
      termGroups.put(t, g);
      for (Rec r : g.recs) {
        r.used = true;
      }
      for (IntVar v : g.leaves) {
        if (!netIndex.containsKey(v)) {
          netIndex.put(v, netVars.size());
          netVars.add(v);
        }
      }
    }
    if (termGroups.isEmpty() || netVars.isEmpty()) {
      return null;
    }
    // the network over the current domains
    int[][] values = new int[netVars.size()][];
    long entries = 0;
    for (int i = 0; i < values.length; i++) {
      IntDomain d = netVars.get(i).dom();
      values[i] = new int[d.getSize()];
      int p = 0;
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        values[i][p++] = e.nextElement();
      }
    }
    CostNetwork net = new CostNetwork(values);
    for (Map.Entry<IntVar, Long> e : weight.entrySet()) {
      IntVar t = e.getKey();
      long w = e.getValue();
      Group g = termGroups.get(t);
      boolean done = false;
      if (g != null && nodes < BUDGET) {
        long cells = 1;
        for (IntVar v : g.leaves) {
          cells *= values[netIndex.get(v)].length;
        }
        if (g.leaves.size() < 2 || entries + cells <= MAX_ENTRIES) {
          done = addTerm(net, netIndex, values, t, w, g);
          if (done && g.leaves.size() == 2) {
            entries += cells;
          }
        }
      }
      if (done) {
        terms++;
        if (g.leaves.size() == 2) {
          binaryTerms++;
        }
      } else {
        // a term left out: its least value
        termsLeft++;
        constant += w > 0 ? w * t.min() : w * t.max();
      }
    }
    net.addConstant(constant);
    // the hard functions over network variables: groups of the constraints left
    for (Rec r : recs) {
      if (r.used || nodes >= BUDGET) {
        continue;
      }
      Group g = hardGroup(r, occurs, internal);
      if (g == null) {
        continue;
      }
      for (Rec q : g.recs) {
        q.used = true;
      }
      if (g.leaves.size() != 2
          || !netIndex.containsKey(g.leaves.get(0))
          || !netIndex.containsKey(g.leaves.get(1))) {
        continue;
      }
      long cells =
          (long) values[netIndex.get(g.leaves.get(0))].length
              * values[netIndex.get(g.leaves.get(1))].length;
      if (entries + cells > MAX_ENTRIES || !tabulable(g, null)) {
        continue;
      }
      if (addHard(net, netIndex, values, g)) {
        hard++;
        entries += cells;
      }
    }
    if (binaryTerms == 0 && !UNARY_ONLY) {
      // unary costs under hard binary constraints only: the linear relaxation bounds those as well
      // and the long reasons of the network hurt learning (SPOT5)
      return null;
    }
    if (debug) {
      FzConsole.println(
          "% cost network: "
              + netVars.size()
              + " variables, "
              + terms
              + " terms ("
              + termsLeft
              + " left out), "
              + hard
              + " hard functions, "
              + net.edges()
              + " binary functions, "
              + nodes
              + " nodes");
    }
    return new CostNetworkBound(objective, maximize, netVars.toArray(new IntVar[0]), net);
  }

  private boolean small(List<IntVar> leaves) {
    if (leaves.isEmpty() || leaves.size() > 2) {
      return false;
    }
    for (IntVar v : leaves) {
      if (v.getSize() > MAX_DOMAIN) {
        return false;
      }
    }
    return true;
  }

  // a group: a single table, or items only
  private static boolean tabulable(Group g, IntVar t) {
    if (g.recs.size() == 1 && g.recs.getFirst().tableScope != null) {
      return true;
    }
    for (Rec r : g.recs) {
      if (r.item == null) {
        return false;
      }
    }
    return true;
  }

  private record Group(List<Rec> recs, List<IntVar> leaves, List<IntVar> inner) {}

  // the constraints reached from t through internal variables, null when too many
  private Group group(
      IntVar t, Map<IntVar, List<Rec>> occurs, Predicate<IntVar> internal, Set<IntVar> termSet) {
    List<Rec> rs = new ArrayList<>();
    Set<Rec> inGroup = Collections.newSetFromMap(new IdentityHashMap<>());
    List<IntVar> leaves = new ArrayList<>();
    List<IntVar> inner = new ArrayList<>();
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    Deque<IntVar> queue = new ArrayDeque<>();
    seen.add(t);
    queue.add(t);
    while (!queue.isEmpty()) {
      IntVar v = queue.poll();
      for (Rec r : occurs.getOrDefault(v, List.of())) {
        if (r.used || !inGroup.add(r)) {
          continue;
        }
        rs.add(r);
        if (rs.size() > MAX_GROUP) {
          return null;
        }
        for (IntVar w : r.vars) {
          if (seen.add(w)) {
            if (termSet.contains(w)) {
              return null;
            }
            if (internal.test(w)) {
              inner.add(w);
              queue.add(w);
            } else {
              leaves.add(w);
              if (leaves.size() > 2) {
                return null;
              }
            }
          }
        }
      }
    }
    if (rs.isEmpty()) {
      return null;
    }
    return new Group(rs, leaves, inner);
  }

  // the group of a constraint not used by a term: through its internal variables
  private Group hardGroup(Rec start, Map<IntVar, List<Rec>> occurs, Predicate<IntVar> internal) {
    List<Rec> rs = new ArrayList<>();
    Set<Rec> inGroup = Collections.newSetFromMap(new IdentityHashMap<>());
    List<IntVar> leaves = new ArrayList<>();
    List<IntVar> inner = new ArrayList<>();
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    Deque<Rec> queue = new ArrayDeque<>();
    inGroup.add(start);
    queue.add(start);
    boolean ok = true;
    while (!queue.isEmpty()) {
      Rec r = queue.poll();
      rs.add(r);
      if (rs.size() > MAX_GROUP) {
        ok = false;
      }
      for (IntVar w : r.vars) {
        if (!seen.add(w)) {
          continue;
        }
        if (internal.test(w)) {
          inner.add(w);
          for (Rec q : occurs.getOrDefault(w, List.of())) {
            if (!q.used && inGroup.add(q)) {
              queue.add(q);
            }
          }
        } else {
          leaves.add(w);
        }
      }
    }
    if (!ok || leaves.size() > 2) {
      for (Rec r : rs) {
        r.used = true;
      }
      return null;
    }
    return new Group(rs, leaves, inner);
  }

  // the outer tuples of a group (leaves, then t when given) that extend to a solution of it
  private int[][] tabulate(Group g, IntVar t) {
    if (g.recs.size() == 1 && g.recs.getFirst().tableScope != null) {
      Rec r = g.recs.getFirst();
      List<IntVar> outer = new ArrayList<>(g.leaves);
      if (t != null) {
        outer.add(t);
      }
      int[] pos = new int[outer.size()];
      int k = r.tableScope.length;
      for (int i = 0; i < pos.length; i++) {
        pos[i] = -1;
        for (int p = 0; p < k; p++) {
          if (r.tableScope[p] == outer.get(i)) {
            pos[i] = p;
          }
        }
        if (pos[i] < 0) {
          return null;
        }
      }
      List<int[]> rows = new ArrayList<>();
      int n = r.tableTuples.length / k;
      for (int q = 0; q < n; q++) {
        boolean fits = true;
        for (int p = 0; p < k && fits; p++) {
          IntVar s = r.tableScope[p];
          int v = r.tableTuples[q * k + p];
          fits = s.domain.contains(v);
          // a variable twice in the scope takes one value
          for (int p2 = 0; p2 < p && fits; p2++) {
            if (r.tableScope[p2] == s && r.tableTuples[q * k + p2] != v) {
              fits = false;
            }
          }
        }
        if (fits) {
          int[] row = new int[pos.length];
          for (int i = 0; i < pos.length; i++) {
            row[i] = r.tableTuples[q * k + pos[i]];
          }
          rows.add(row);
        }
      }
      return rows.toArray(new int[0][]);
    }
    List<IntVar> order = new ArrayList<>(g.leaves);
    if (t != null) {
      order.add(t);
    }
    int outer = order.size();
    order.addAll(g.inner);
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    for (int i = 0; i < order.size(); i++) {
      index.put(order.get(i), i);
    }
    Bound[] bounds = new Bound[g.recs.size()];
    for (int c = 0; c < bounds.length; c++) {
      bounds[c] = new Bound(g.recs.get(c).item, index);
    }
    Tabulator tab =
        new Tabulator(
            order.toArray(new IntVar[0]), outer, bounds, Math.min(GROUP_NODES, BUDGET - nodes));
    int[][] rows = tab.run();
    nodes += tab.nodes;
    return rows;
  }

  private boolean addTerm(
      CostNetwork net, Map<IntVar, Integer> netIndex, int[][] values, IntVar t, long w, Group g) {
    int[][] rows = tabulate(g, t);
    if (rows == null) {
      return false;
    }
    int i = netIndex.get(g.leaves.get(0));
    if (g.leaves.size() == 1) {
      long[] cost = new long[values[i].length];
      Arrays.fill(cost, CostNetwork.HARD);
      for (int[] row : rows) {
        int ai = Arrays.binarySearch(values[i], row[0]);
        if (ai >= 0) {
          long c = w * row[1];
          if (Math.abs(c) > CostNetwork.MAX_COST) {
            return false;
          }
          cost[ai] = Math.min(cost[ai], c);
        }
      }
      for (int ai = 0; ai < cost.length; ai++) {
        net.addUnary(i, ai, cost[ai]);
      }
      return true;
    }
    int j = netIndex.get(g.leaves.get(1));
    int dj = values[j].length;
    long[] cost = new long[values[i].length * dj];
    Arrays.fill(cost, CostNetwork.HARD);
    for (int[] row : rows) {
      int ai = Arrays.binarySearch(values[i], row[0]);
      int bj = Arrays.binarySearch(values[j], row[1]);
      if (ai >= 0 && bj >= 0) {
        long c = w * row[2];
        if (Math.abs(c) > CostNetwork.MAX_COST) {
          return false;
        }
        cost[ai * dj + bj] = Math.min(cost[ai * dj + bj], c);
      }
    }
    net.addBinary(i, j, cost);
    return true;
  }

  private boolean addHard(CostNetwork net, Map<IntVar, Integer> netIndex, int[][] values, Group g) {
    int[][] rows = tabulate(g, null);
    if (rows == null) {
      return false;
    }
    int i = netIndex.get(g.leaves.get(0));
    int j = netIndex.get(g.leaves.get(1));
    int dj = values[j].length;
    long[] cost = new long[values[i].length * dj];
    Arrays.fill(cost, CostNetwork.HARD);
    int allowed = 0;
    for (int[] row : rows) {
      int ai = Arrays.binarySearch(values[i], row[0]);
      int bj = Arrays.binarySearch(values[j], row[1]);
      if (ai >= 0 && bj >= 0 && cost[ai * dj + bj] != 0) {
        cost[ai * dj + bj] = 0;
        allowed++;
      }
    }
    if (allowed == cost.length) {
      return false;
    }
    net.addBinary(i, j, cost);
    return true;
  }
}
