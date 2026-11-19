/*
 * PartitionCuts.java
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

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Linearizations;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearForm;

/**
 * Cuts of the clique partitioning polytope over the pair indicators of a model: Booleans {@code b
 * <-> x[i] = x[j]} (or {@code x[i] != x[j]}) over variables x that take a value from a set of k
 * values, the classes. Writing p[i,j] for the indicator of "x[i] and x[j] are in the same class",
 * the separated inequalities are
 *
 * <ul>
 *   <li>the triangle inequalities {@code p[i,j] + p[j,l] - p[i,l] <= 1} (equality is transitive),
 *       of Grötschel and Wakabayashi, "A cutting plane algorithm for a clustering problem",
 *       Mathematical Programming 45 (1989) 59-96;
 *   <li>the clique inequalities of a partition into at most k classes: for a set S of s nodes,
 *       {@code sum(i < j in S) p[i,j] >= r * (q + 1) * q / 2 + (k - r) * q * (q - 1) / 2} with q =
 *       s div k and r = s mod k, since the pairs inside the classes are fewest when the classes are
 *       as equal as possible (for s = k + 1 the right-hand side is 1); Chopra and Rao, "The
 *       partition problem", Mathematical Programming 59 (1993) 87-115.
 * </ul>
 *
 * <p>A pair may also be stated by a constraint {@code x[i] = x[j]} or {@code x[i] != x[j]}, which
 * fixes its indicator. Objectives that are sums of weighted pair indicators (modularity of the
 * community detection of the MiniZinc Challenge) have a trivial LP bound without these cuts: every
 * indicator with a positive weight sits at 1. With the triangle inequalities the relaxation is the
 * one that Agarwal and Kempe, "Modularity-maximizing graph communities via mathematical
 * programming", European Physical Journal B 66 (2008) 409-418, found to be tight on most small
 * networks; it is also the bound that the RLT and zero-half cuts of CP-SAT reach on them.
 *
 * <p>All cuts use the domains at the time the cuts are made (the root), so they hold for the whole
 * search.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class PartitionCuts {

  /**
   * A Boolean that indicates whether two variables are equal ({@code b <-> x = y}); implemented by
   * the reified equalities of front ends that have their own class for them.
   */
  public interface Equality {
    /**
     * The first variable.
     *
     * @return x
     */
    IntVar left();

    /**
     * The second variable.
     *
     * @return y
     */
    IntVar right();

    /**
     * The 0/1 indicator of {@code x = y}, or null when the constraint is not a reified equality (an
     * implication only).
     *
     * @return b, or null
     */
    IntVar indicator();
  }

  // the least violation of a cut
  private static final double MIN_VIOLATION = 1e-4;
  // the fewest nodes of a partition worth separating, and the most (the triangle separation
  // costs nodes^3 per round)
  static final int MIN_NODES = 4;
  static final int MAX_NODES = Integer.getInteger("org.jacop.lp.partitionNodes", 250);
  // the share of the pairs that need an indicator or a fixed relation
  private static final double MIN_DENSITY = 0.5;

  // a pair with no indicator
  private static final int NONE = -1;
  // a pair fixed equal (p = 1) or fixed different (p = 0)
  private static final int SAME = -2;
  private static final int APART = -3;

  private final IntVar[] literals;
  // for each literal, whether it indicates x != y (p = 1 - b)
  private final boolean[] negated;
  // pair[i][j] = the index of the literal of the pair, or NONE, SAME, APART
  private final int[][] pair;
  private final int nodes;
  private final int classes;

  private PartitionCuts(IntVar[] literals, boolean[] negated, int[][] pair, int classes) {
    this.literals = literals;
    this.negated = negated;
    this.pair = pair;
    this.nodes = pair.length;
    this.classes = classes;
  }

  /** A cut {@code sum weights * literals <= rhs}, over indexes of {@link #literals()}. */
  public record Cut(int[] literals, long[] weights, long rhs, double efficacy) {}

  /**
   * The Booleans the cuts are stated over.
   *
   * @return the pair indicators
   */
  public IntVar[] literals() {
    return literals;
  }

  /**
   * The number of nodes (variables) of the partition.
   *
   * @return the nodes
   */
  public int nodes() {
    return nodes;
  }

  /**
   * The most classes of the partition: the values of the nodes' domains.
   *
   * @return k
   */
  public int classes() {
    return classes;
  }

  /**
   * Returns a copy of the cuts over the copies of the literals.
   *
   * @param map the copies of the variables
   * @return the copy
   */
  public PartitionCuts copy(VarMap map) {
    IntVar[] l = new IntVar[literals.length];
    for (int i = 0; i < l.length; i++) {
      l[i] = map.get(literals[i]);
    }
    return new PartitionCuts(l, negated, pair, classes);
  }

  // an equality pair with its indicator: b <-> x = y, or b <-> x != y when negated
  private record Link(IntVar x, IntVar y, IntVar b, boolean negated) {}

  /**
   * Returns the partitions of the given constraints: the connected groups of variables linked by
   * reified equalities (or disequalities) with enough of their pairs linked, at least {@link
   * #MIN_NODES} and at most {@code org.jacop.lp.partitionNodes} (250) variables, and fewer values
   * than variables.
   *
   * @param constraints the constraints of the model
   * @return the partitions, possibly none
   */
  public static List<PartitionCuts> of(Collection<Constraint> constraints) {
    List<Link> links = new ArrayList<>();
    List<IntVar[]> same = new ArrayList<>();
    List<IntVar[]> apart = new ArrayList<>();
    for (Constraint c : constraints) {
      if (c instanceof Equality e && e.indicator() != null) {
        links.add(new Link(e.left(), e.right(), e.indicator(), false));
      } else if (c.getClass() == Reified.class && ((Reified) c).c.getClass() == XeqY.class) {
        XeqY eq = (XeqY) ((Reified) c).c;
        links.add(new Link(eq.x(), eq.y(), ((Reified) c).b, false));
      } else if (c.getClass() == Reified.class && ((Reified) c).c.getClass() == XneqY.class) {
        XneqY ne = (XneqY) ((Reified) c).c;
        links.add(new Link(ne.x(), ne.y(), ((Reified) c).b, true));
      } else if (c.getClass() == XneqY.class) {
        apart.add(new IntVar[] {((XneqY) c).x(), ((XneqY) c).y()});
      } else if (c.getClass() == XeqY.class) {
        same.add(new IntVar[] {((XeqY) c).x(), ((XeqY) c).y()});
      }
    }
    if (links.size() < 3) {
      return List.of();
    }
    // the groups of variables connected by links (union-find over the variables)
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    for (Link l : links) {
      if (l.x != l.y && l.b.min() >= 0 && l.b.max() <= 1) {
        for (IntVar v : new IntVar[] {l.x, l.y}) {
          if (!index.containsKey(v)) {
            index.put(v, vars.size());
            vars.add(v);
          }
        }
      }
    }
    int[] parent = new int[vars.size()];
    for (int i = 0; i < parent.length; i++) {
      parent[i] = i;
    }
    for (Link l : links) {
      Integer a = index.get(l.x);
      Integer b = index.get(l.y);
      if (a != null && b != null && a.intValue() != b.intValue()) {
        parent[find(parent, a)] = find(parent, b);
      }
    }
    Map<Integer, List<Integer>> groups = new HashMap<>();
    for (int i = 0; i < parent.length; i++) {
      groups.computeIfAbsent(find(parent, i), r -> new ArrayList<>()).add(i);
    }
    Map<IntVar, Map<Integer, IntVar>> valueBooleans = Linearizations.valueBooleans(constraints);
    List<PartitionCuts> result = new ArrayList<>();
    for (List<Integer> group : groups.values()) {
      if (group.size() < MIN_NODES || group.size() > MAX_NODES) {
        continue;
      }
      PartitionCuts p = partition(group, vars, index, links, same, apart, valueBooleans);
      if (p != null) {
        result.add(p);
      }
    }
    return result;
  }

  private static PartitionCuts partition(
      List<Integer> group,
      List<IntVar> vars,
      Map<IntVar, Integer> index,
      List<Link> links,
      List<IntVar[]> same,
      List<IntVar[]> apart,
      Map<IntVar, Map<Integer, IntVar>> valueBooleans) {
    int m = group.size();
    int[] local = new int[vars.size()];
    Arrays.fill(local, -1);
    IntDomain values = null;
    // the anchors: one node for each value that some variable of the group has a Boolean for
    // (b <-> x = v), standing for the class of the value; a variable fixed to the value (the first
    // node under value precedence) is such a node, and its pairs are those Booleans
    java.util.TreeSet<Integer> anchorValues = new java.util.TreeSet<>();
    for (int k = 0; k < m; k++) {
      IntVar x = vars.get(group.get(k));
      local[group.get(k)] = k;
      values = values == null ? x.dom().cloneLight() : values.union(x.dom());
      anchorValues.addAll(valueBooleans.getOrDefault(x, Map.of()).keySet());
    }
    IntDomain union = values;
    anchorValues.removeIf(v -> !union.contains(v));
    int[] anchor = anchorValues.stream().mapToInt(Integer::intValue).toArray();
    int n = m + anchor.length;
    int classes = values.getSize();
    if (classes >= n) {
      return null;
    }
    int[][] pair = new int[n][n];
    for (int[] row : pair) {
      Arrays.fill(row, NONE);
    }
    List<IntVar> literals = new ArrayList<>();
    List<Boolean> negated = new ArrayList<>();
    for (Link l : links) {
      int a = at(l.x, index, local);
      int b = at(l.y, index, local);
      if (a >= 0 && b >= 0 && a != b && pair[a][b] == NONE) {
        link(pair, a, b, l.b, l.negated, literals, negated);
      }
    }
    for (int k = 0; k < m; k++) {
      IntVar x = vars.get(group.get(k));
      Map<Integer, IntVar> byValue = valueBooleans.getOrDefault(x, Map.of());
      for (int t = 0; t < anchor.length; t++) {
        IntVar b = byValue.get(anchor[t]);
        if (!x.dom().contains(anchor[t])) {
          pair[k][m + t] = APART;
          pair[m + t][k] = APART;
        } else if (b != null) {
          link(pair, k, m + t, b, false, literals, negated);
        }
      }
    }
    for (int s = m; s < n; s++) {
      for (int t = m; t < n; t++) {
        pair[s][t] = s == t ? NONE : APART;
      }
    }
    for (List<IntVar[]> fixedPairs : List.of(same, apart)) {
      int fixed = fixedPairs == same ? SAME : APART;
      for (IntVar[] xy : fixedPairs) {
        int a = at(xy[0], index, local);
        int b = at(xy[1], index, local);
        if (a >= 0 && b >= 0 && a != b) {
          pair[a][b] = fixed;
          pair[b][a] = fixed;
        }
      }
    }
    // pairs of variables with disjoint domains are apart
    long known = 0;
    for (int a = 0; a < n; a++) {
      for (int b = a + 1; b < n; b++) {
        if (pair[a][b] == NONE
            && b < m
            && !vars.get(group.get(a)).dom().isIntersecting(vars.get(group.get(b)).dom())) {
          pair[a][b] = APART;
          pair[b][a] = APART;
        }
        known += pair[a][b] != NONE ? 1 : 0;
      }
    }
    if (literals.size() < 3 || known < MIN_DENSITY * n * (n - 1) / 2) {
      return null;
    }
    boolean[] neg = new boolean[negated.size()];
    for (int i = 0; i < neg.length; i++) {
      neg[i] = negated.get(i);
    }
    return new PartitionCuts(literals.toArray(new IntVar[0]), neg, pair, classes);
  }

  // the pair a, b indicated by the literal b (b <-> same class, or different when negated), or
  // fixed by its value
  private static void link(
      int[][] pair,
      int a,
      int b,
      IntVar literal,
      boolean negate,
      List<IntVar> literals,
      List<Boolean> negated) {
    int k;
    if (literal.singleton()) {
      k = (literal.value() == 1) != negate ? SAME : APART;
    } else {
      k = literals.size();
      literals.add(literal);
      negated.add(negate);
    }
    pair[a][b] = k;
    pair[b][a] = k;
  }

  private static int at(IntVar v, Map<IntVar, Integer> index, int[] local) {
    Integer i = index.get(v);
    return i == null ? -1 : local[i];
  }

  private static int find(int[] parent, int i) {
    while (parent[i] != i) {
      parent[i] = parent[parent[i]];
      i = parent[i];
    }
    return i;
  }

  // the value of the pair indicator p[a][b] for the literal values, or NaN when the pair has none
  private double value(int a, int b, double[] value) {
    int k = pair[a][b];
    if (k >= 0) {
      return negated[k] ? 1 - value[k] : value[k];
    }
    return k == SAME ? 1 : k == APART ? 0 : Double.NaN;
  }

  /**
   * The least number of pairs of s nodes in the same class when they are split into at most k
   * classes.
   *
   * @param s the nodes
   * @param k the classes
   * @return the pairs
   */
  static long leastPairs(int s, int k) {
    long q = s / k;
    long r = s % k;
    return r * (q + 1) * q / 2 + (k - r) * q * (q - 1) / 2;
  }

  /**
   * Returns violated cuts for the given values of the literals, most violated first.
   *
   * @param value the values of {@link #literals()} in the LP solution
   * @param limit the most cuts
   * @return the cuts
   */
  public List<Cut> separate(double[] value, int limit) {
    List<Cut> found = new ArrayList<>();
    double[][] p = new double[nodes][nodes];
    for (int a = 0; a < nodes; a++) {
      for (int b = 0; b < nodes; b++) {
        p[a][b] = a == b ? 1 : value(a, b, value);
      }
    }
    triangles(p, found);
    cliques(p, found);
    stars(p, found);
    found.sort((c, d) -> Double.compare(d.efficacy, c.efficacy));
    return found.size() > limit ? new ArrayList<>(found.subList(0, limit)) : found;
  }

  // p[a][b] + p[b][c] - p[a][c] <= 1, b the apex
  private void triangles(double[][] p, List<Cut> found) {
    for (int b = 0; b < nodes; b++) {
      for (int a = 0; a < nodes; a++) {
        double ab = p[a][b];
        if (a == b || !(ab > MIN_VIOLATION)) {
          continue;
        }
        for (int c = a + 1; c < nodes; c++) {
          double cb = p[c][b];
          if (c == b || !(ab + cb > 1 + MIN_VIOLATION)) {
            continue;
          }
          double ac = p[a][c];
          if (Double.isNaN(ac) || !(ab + cb - ac > 1 + MIN_VIOLATION)) {
            continue;
          }
          add(new int[] {a, c, a}, new int[] {b, b, c}, new long[] {1, 1, -1}, 1, p, found);
        }
      }
    }
  }

  // the 2-partition inequalities of Grötschel and Wakabayashi with one node s on one side:
  // sum(t in T) p[s][t] - sum(t < u in T) p[t][u] <= 1, T grown greedily from the nodes nearest
  // to s while each one adds to the left-hand side
  private void stars(double[][] p, List<Cut> found) {
    Integer[] order = new Integer[nodes];
    int[] members = new int[nodes];
    double[] toSet = new double[nodes];
    for (int s = 0; s < nodes; s++) {
      final int centre = s;
      for (int v = 0; v < nodes; v++) {
        order[v] = v;
      }
      Arrays.sort(order, (u, v) -> Double.compare(nan0(p[centre][v]), nan0(p[centre][u])));
      Arrays.fill(toSet, 0);
      int size = 0;
      double lhs = 0;
      for (int v : order) {
        double ps = p[s][v];
        if (v == s || !(ps > MIN_VIOLATION)) {
          continue;
        }
        if (Double.isNaN(toSet[v]) || ps - toSet[v] <= MIN_VIOLATION) {
          continue;
        }
        members[size++] = v;
        lhs += ps - toSet[v];
        for (int u = 0; u < nodes; u++) {
          toSet[u] += p[u][v];
        }
      }
      if (size >= 2 && lhs > 1 + MIN_VIOLATION) {
        int pairs = size + size * (size - 1) / 2;
        int[] as = new int[pairs];
        int[] bs = new int[pairs];
        long[] ws = new long[pairs];
        int k = 0;
        for (int i = 0; i < size; i++) {
          as[k] = s;
          bs[k] = members[i];
          ws[k++] = 1;
          for (int j = i + 1; j < size; j++) {
            as[k] = members[i];
            bs[k] = members[j];
            ws[k++] = -1;
          }
        }
        add(as, bs, ws, 1, p, found);
      }
    }
  }

  private static double nan0(double v) {
    return Double.isNaN(v) ? -1 : v;
  }

  // sum(i < j in S) p[i][j] >= leastPairs(|S|, k), S grown greedily from each node by the node
  // whose pairs with S sum least
  private void cliques(double[][] p, List<Cut> found) {
    int maxSize = Math.min(nodes, 3 * classes + 1);
    boolean[] in = new boolean[nodes];
    double[] toSet = new double[nodes];
    int[] members = new int[nodes];
    for (int start = 0; start < nodes; start++) {
      Arrays.fill(in, false);
      in[start] = true;
      members[0] = start;
      int size = 1;
      double sum = 0;
      for (int v = 0; v < nodes; v++) {
        toSet[v] = p[v][start];
      }
      double best = MIN_VIOLATION;
      int bestSize = 0;
      while (size < maxSize) {
        int next = -1;
        for (int v = 0; v < nodes; v++) {
          if (!in[v] && !Double.isNaN(toSet[v]) && (next < 0 || toSet[v] < toSet[next])) {
            next = v;
          }
        }
        if (next < 0) {
          break;
        }
        in[next] = true;
        members[size++] = next;
        sum += toSet[next];
        for (int v = 0; v < nodes; v++) {
          toSet[v] += p[v][next];
        }
        if (size > classes) {
          double violation = leastPairs(size, classes) - sum;
          // the norm grows with the pairs: compare by efficacy
          double efficacy = violation / Math.sqrt(size * (size - 1) / 2.0);
          if (efficacy > best) {
            best = efficacy;
            bestSize = size;
          }
        }
      }
      // only the lowest start of a set
      if (bestSize > 0 && smallest(members, bestSize) == start) {
        int pairs = bestSize * (bestSize - 1) / 2;
        int[] as = new int[pairs];
        int[] bs = new int[pairs];
        long[] ws = new long[pairs];
        int k = 0;
        for (int i = 0; i < bestSize; i++) {
          for (int j = i + 1; j < bestSize; j++) {
            as[k] = members[i];
            bs[k] = members[j];
            ws[k++] = -1;
          }
        }
        add(as, bs, ws, -leastPairs(bestSize, classes), p, found);
      }
    }
  }

  private static int smallest(int[] members, int size) {
    int m = Integer.MAX_VALUE;
    for (int i = 0; i < size; i++) {
      m = Math.min(m, members[i]);
    }
    return m;
  }

  /**
   * Returns rows that make the literals missing from the given variables columns of the relaxation:
   * for each such literal of a pair i, j, a triangle inequality {@code p[i][l] + p[l][j] - p[i][j]
   * <= 1} over a node l with both pairs known. The pairs with no weight in the objective (zero
   * modularity) are in no row of the model, and without them as columns no triangle over them could
   * be separated.
   *
   * @param present the variables that are already in rows of the relaxation
   * @return the rows, as {@code sum weights * vars <= rhs}
   */
  public List<LinearForm> columnRows(java.util.Set<IntVar> present) {
    List<LinearForm> rows = new ArrayList<>();
    boolean[] covered = new boolean[literals.length];
    for (int k = 0; k < literals.length; k++) {
      covered[k] = present.contains(literals[k]);
    }
    for (int i = 0; i < nodes; i++) {
      for (int j = i + 1; j < nodes; j++) {
        int k = pair[i][j];
        if (k < 0 || covered[k]) {
          continue;
        }
        for (int l = 0; l < nodes; l++) {
          if (l != i && l != j && pair[i][l] != NONE && pair[l][j] != NONE) {
            List<Cut> one = new ArrayList<>(1);
            add(new int[] {i, l, i}, new int[] {l, j, j}, new long[] {1, 1, -1}, 1, null, one);
            if (!one.isEmpty()) {
              Cut c = one.get(0);
              IntVar[] vs = new IntVar[c.literals.length];
              for (int t = 0; t < vs.length; t++) {
                vs[t] = literals[c.literals[t]];
                covered[c.literals[t]] = true;
              }
              rows.add(new LinearForm(vs, c.weights, c.rhs, LinearForm.LE));
            }
            break;
          }
        }
      }
    }
    return rows;
  }

  // the cut sum w p[a][b] <= rhs over the pairs, stated over the literals; with p null, the row
  // whatever its violation
  private void add(int[] as, int[] bs, long[] ws, long rhs, double[][] p, List<Cut> found) {
    double violation = -rhs;
    Map<Integer, Long> weights = new java.util.TreeMap<>();
    for (int t = 0; t < as.length; t++) {
      int k = pair[as[t]][bs[t]];
      if (k == NONE) {
        return;
      }
      violation += p == null ? 0 : ws[t] * p[as[t]][bs[t]];
      if (k >= 0) {
        if (negated[k]) {
          // w (1 - b)
          rhs -= ws[t];
          weights.merge(k, -ws[t], Long::sum);
        } else {
          weights.merge(k, ws[t], Long::sum);
        }
      } else if (k == SAME) {
        rhs -= ws[t];
      }
    }
    weights.values().removeIf(w -> w == 0);
    if (weights.isEmpty() || !(violation > MIN_VIOLATION || p == null)) {
      return;
    }
    int[] ls = new int[weights.size()];
    long[] wl = new long[weights.size()];
    int i = 0;
    double norm = 0;
    for (Map.Entry<Integer, Long> e : weights.entrySet()) {
      ls[i] = e.getKey();
      wl[i++] = e.getValue();
      norm += (double) e.getValue() * e.getValue();
    }
    found.add(new Cut(ls, wl, rhs, violation / Math.sqrt(norm)));
  }
}
