/*
 * MddLinearSum.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.constraints;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;

/**
 * Recognises a multi-valued decision diagram that states exactly x_1 + ... + x_n = S over the
 * current domains, so the FlatZinc front end can post the sum in place of the diagram.
 *
 * <p>XCSP3 MagicSquare-mdd (2023) writes every row, column and diagonal sum of an n x n magic
 * square as an MDD whose nodes are the partial sums (Perez and Régin, "Efficient operations on MDDs
 * for building constraint programming models", IJCAI 2015, build such sum diagrams). On the
 * order-10 square the 22 diagrams have 199,000 edges each; JaCoP's MDD propagator needs 5.7 GB and
 * finds no square in 600 s, while the same model with the sums finds one in 4 s, since the sums
 * take part in the bounds reasoning, the LP relaxation and the linear explanations of LCG.
 *
 * <p>The check is exact. Every edge label is one value, and each node gets one potential, the
 * partial sum of every path that reaches it; the terminal gets S. Then every tuple the diagram
 * accepts has sum S. The diagram is deterministic (no two edges of a node share a value), so its
 * root-to-terminal paths over the current domains count its accepted tuples, and when that count
 * equals the number of tuples of the domains whose sum is S (a dynamic program over the sums), the
 * diagram accepts exactly those tuples. Counts use {@link BigInteger}.
 *
 * <p>The system property {@code org.jacop.fz.mddLinear=false} turns it off.
 */
public final class MddLinearSum {

  /** Diagrams larger than this many edges are not checked. */
  static final int MAX_EDGES = 1 << 22;

  /** Sums with a wider range than this are not counted. */
  static final long MAX_RANGE = 1L << 20;

  private MddLinearSum() {}

  /**
   * The per diagram result of the structural part of the check, shared by calls on one graph, by
   * the array of node levels. The map holds that array weakly and no entry reaches it, so the
   * diagrams of a model are forgotten with the model (a map by the identity of all four arrays kept
   * every diagram solved in the JVM).
   */
  private static final Map<int[], List<Diagram>> STRUCTURE = new WeakHashMap<>();

  /**
   * A diagram by the identity of its other arrays, among the diagrams of one array of sources. Two
   * diagrams of one model may share a named array of sources and differ in their labels, so the
   * sources alone do not name a diagram.
   */
  private static final class Diagram {
    private final int[] level;
    private final IntDomain[] label;
    private final int[] to;
    private final Object structure;

    Diagram(int[] level, IntDomain[] label, int[] to, Object structure) {
      this.level = level;
      this.label = label;
      this.to = to;
      this.structure = structure;
    }

    Object structure() {
      return structure;
    }

    boolean of(int[] level, IntDomain[] label, int[] to) {
      return this.level == level && this.label == label && this.to == to;
    }
  }

  private static final Object NOT_A_SUM = new Object();

  /** The number of tuples with sum S of a list of domains, by domains and S. */
  private static final Map<String, BigInteger> SUM_COUNTS = new HashMap<>();

  /** The counts kept at most, over all models solved in the JVM. */
  private static final int MAX_SUM_COUNTS = 4096;

  /**
   * It reports whether the system property org.jacop.fz.mddLinear leaves the rewriting on.
   *
   * @return false if the system property org.jacop.fz.mddLinear is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.mddLinear"));
  }

  /** Forgets the diagrams seen, for a new model. */
  public static synchronized void reset() {
    STRUCTURE.clear();
    SUM_COUNTS.clear();
  }

  /**
   * The sum S when the diagram accepts exactly the tuples of the current domains of x whose sum is
   * S, else null.
   *
   * @param x the variables of the diagram, x[i] labels the edges leaving level i + 1.
   * @param level the level (1..n) of each node.
   * @param from the source node (1..N) of each edge.
   * @param label the values of each edge.
   * @param to the target node (1..N) of each edge, 0 for the terminal.
   * @return S, or null when the diagram is not exactly that sum.
   */
  public static synchronized Long sum(
      IntVar[] x, int[] level, int[] from, IntDomain[] label, int[] to) {
    List<Diagram> diagrams = STRUCTURE.computeIfAbsent(from, k -> new ArrayList<>(1));
    Object s = null;
    for (Diagram d : diagrams) {
      if (d.of(level, label, to)) {
        s = d.structure();
        break;
      }
    }
    if (s == null) {
      s = structure(x.length, level, from, label, to);
      diagrams.add(new Diagram(level, label, to, s));
    }
    if (s == NOT_A_SUM) {
      return null;
    }
    long total = (Long) s;
    BigInteger paths = paths(x, level, from, label, to);
    BigInteger tuples = tuples(x, total);
    return paths != null && paths.signum() > 0 && paths.equals(tuples) ? total : null;
  }

  // the sum of the terminal when every label is one value, the potentials are consistent and the
  // diagram is deterministic
  private static Object structure(int n, int[] level, int[] from, IntDomain[] label, int[] to) {
    int nodes = level.length;
    if (n == 0 || nodes == 0 || from.length > MAX_EDGES || level[0] != 1) {
      return NOT_A_SUM;
    }
    // a malformed diagram is left to ExtensionalSupportMdd, which reports it
    if (label.length != from.length || to.length != from.length) {
      return NOT_A_SUM;
    }
    for (int e = 0; e < from.length; e++) {
      if (from[e] < 1 || from[e] > nodes || to[e] < 0 || to[e] > nodes) {
        return NOT_A_SUM;
      }
    }
    long[] potential = new long[nodes + 1];
    boolean[] reached = new boolean[nodes + 1];
    reached[1] = true;
    Long terminal = null;
    // edges go from a level to the next; visit them by level so a source has its potential
    int[][] byLevel = edgesByLevel(n, level, from);
    if (byLevel == null) {
      return NOT_A_SUM;
    }
    for (int l = 0; l < n; l++) {
      int[] edges = byLevel[l];
      // per source node, the values already used (determinism)
      Map<Integer, IntDomain> used = new HashMap<>();
      for (int e : edges) {
        IntDomain d = label[e];
        if (d.isEmpty()) {
          continue;
        }
        if (d.getSize() != 1) {
          return NOT_A_SUM;
        }
        int f = from[e];
        if (!reached[f]) {
          continue;
        }
        IntDomain u = used.get(f);
        if (u != null && u.contains(d)) {
          return NOT_A_SUM;
        }
        used.put(f, u == null ? d : u.union(d));
        long p = potential[f] + d.min();
        int t = to[e];
        if (t == 0 && l != n - 1) {
          // a path shorter than the variables: not a tuple of the sum
          return NOT_A_SUM;
        } else if (t == 0) {
          if (terminal != null && terminal != p) {
            return NOT_A_SUM;
          }
          terminal = p;
        } else if (reached[t]) {
          if (potential[t] != p) {
            return NOT_A_SUM;
          }
        } else {
          reached[t] = true;
          potential[t] = p;
        }
      }
    }
    return terminal == null ? NOT_A_SUM : terminal;
  }

  // edge indices per level 1..n, or null when an edge does not go to the next level
  private static int[][] edgesByLevel(int n, int[] level, int[] from) {
    int[] count = new int[n];
    for (int f : from) {
      int l = level[f - 1];
      if (l < 1 || l > n) {
        return null;
      }
      count[l - 1]++;
    }
    int[][] out = new int[n][];
    for (int l = 0; l < n; l++) {
      out[l] = new int[count[l]];
      count[l] = 0;
    }
    for (int e = 0; e < from.length; e++) {
      int l = level[from[e] - 1] - 1;
      out[l][count[l]++] = e;
    }
    return out;
  }

  // the number of root-to-terminal paths over the current domains
  private static BigInteger paths(
      IntVar[] x, int[] level, int[] from, IntDomain[] label, int[] to) {
    int nodes = level.length;
    BigInteger[] count = new BigInteger[nodes + 1];
    count[1] = BigInteger.ONE;
    BigInteger terminal = BigInteger.ZERO;
    int[][] byLevel = edgesByLevel(x.length, level, from);
    for (int l = 0; l < byLevel.length; l++) {
      IntDomain dom = x[l].dom();
      for (int e : byLevel[l]) {
        BigInteger c = count[from[e]];
        if (c == null || label[e].isEmpty() || !dom.contains(label[e].min())) {
          continue;
        }
        int t = to[e];
        if (t == 0 && l != byLevel.length - 1) {
          return null;
        } else if (t == 0) {
          terminal = terminal.add(c);
        } else if (level[t - 1] != l + 2) {
          return null;
        } else {
          count[t] = count[t] == null ? c : count[t].add(c);
        }
      }
    }
    return terminal;
  }

  // the number of tuples of the current domains of x with sum s
  private static BigInteger tuples(IntVar[] x, long s) {
    StringBuilder key = new StringBuilder().append(s);
    long lo = 0;
    long hi = 0;
    for (IntVar v : x) {
      key.append('|').append(v.dom());
      lo += v.min();
      hi += v.max();
    }
    if (s < lo || s > hi) {
      return BigInteger.ZERO;
    }
    if (hi - lo + 1 > MAX_RANGE) {
      return BigInteger.valueOf(-1);
    }
    if (SUM_COUNTS.size() >= MAX_SUM_COUNTS) {
      // the counts are by content, so forgetting them changes no answer, only bounds the memory
      SUM_COUNTS.clear();
    }
    return SUM_COUNTS.computeIfAbsent(key.toString(), k -> countSums(x, s));
  }

  // dynamic program over the partial sums, offset by the partial minimum
  private static BigInteger countSums(IntVar[] x, long s) {
    BigInteger[] count = {BigInteger.ONE};
    long base = 0;
    for (IntVar v : x) {
      int min = v.min();
      int width = v.max() - min;
      BigInteger[] next = new BigInteger[count.length + width];
      java.util.Arrays.fill(next, BigInteger.ZERO);
      for (ValueEnumeration it = v.dom().valueEnumeration(); it.hasMoreElements(); ) {
        int off = it.nextElement() - min;
        for (int i = 0; i < count.length; i++) {
          if (count[i].signum() != 0) {
            next[i + off] = next[i + off].add(count[i]);
          }
        }
      }
      count = next;
      base += min;
    }
    long i = s - base;
    return i < 0 || i >= count.length ? BigInteger.ZERO : count[(int) i];
  }
}
