/*
 * CostPathExplanation.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints.regular;

import java.util.Arrays;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of cost constraints over a layered graph (cost regular, cost MDD, multi-cost
 * regular) by shortest and longest paths. With the domains just before an atom and its negation in
 * place of its variable's domain, an edge is alive when its label is in the domain of its level's
 * variable. The atom follows when every path through the edges its negation leaves either costs
 * more than the maximum of a cost or less than its minimum; each of those edges is assigned to one
 * such bound.
 *
 * <p>For a bound K that every path must exceed, the reason is the bound of the cost and the removal
 * of some dead edges, chosen as Gange, Stuckey and Van Hentenryck do for edge-valued decision
 * diagrams ("Explaining Propagators for Edge-valued Decision Diagrams", CP 2013): going down the
 * levels with the shortest paths f from the source over the alive and the restored edges, a dead
 * edge (s, t) is restored, so its removal is not cited, when f(s) + cost + b(t) is still above K, b
 * the shortest path to the sink over the alive edges. The last restored edge of any path then keeps
 * its cost above K. A bound that every path must stay below is explained the same way with longest
 * paths. A failure is explained as the atom whose negation is the empty restriction.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CostPathExplanation {

  private static final long INF = Long.MAX_VALUE / 4;

  /** The most edges of a graph explained. */
  private static final int EDGE_LIMIT = 1 << 22;

  private final AtomicTrail trail;
  private final int position;
  private final IntVar[] list;
  private final int levels;
  private final int[] nodeStart;
  private final int[] edgeStart;
  private final int[] source;
  private final int[] target;
  private final int[] label;
  // cost[r][e]: the cost of edge e for resource r
  private final int[][] cost;
  private final IntVar[] costVar;

  // the negated atom: its variable, kind and value (none for a failure)
  private IntVar negated;
  private int negatedKind;
  private int negatedValue;
  // the level of the negated variable, -1 when it is a cost or there is none
  private int negatedLevel = -1;

  private Before[] before;
  private boolean[] aliveEdge;

  /**
   * The graph of a constraint.
   *
   * @param trail the trail
   * @param position the position the domains are read before
   * @param list the variable of each level
   * @param nodeStart the nodes of level l are nodeStart[l]..nodeStart[l+1]-1; node 0 is the source
   *     and the nodes of the last level are the sinks
   * @param edgeStart the edges of level l are edgeStart[l]..edgeStart[l+1]-1
   * @param source the source node of each edge
   * @param target the target node of each edge
   * @param label the value of each edge
   * @param cost the cost of each edge, per resource
   * @param costVar the cost variable of each resource
   */
  CostPathExplanation(
      AtomicTrail trail,
      int position,
      IntVar[] list,
      int[] nodeStart,
      int[] edgeStart,
      int[] source,
      int[] target,
      int[] label,
      int[][] cost,
      IntVar[] costVar) {
    this.trail = trail;
    this.position = position;
    this.list = list;
    this.levels = list.length;
    this.nodeStart = nodeStart;
    this.edgeStart = edgeStart;
    this.source = source;
    this.target = target;
    this.label = label;
    this.cost = cost;
    this.costVar = costVar;
  }

  /**
   * Adds to {@code out} the reason of an entry of a variable of the word or of a cost.
   *
   * @param entry the entry, which must be the position of this explanation
   * @param out where the reason entries are added
   * @return false when the paths do not imply it or the graph is too large
   */
  boolean explain(int entry, EntryList out) {
    negated = trail.variable(entry);
    negatedKind = trail.kind(entry);
    negatedValue = trail.value(entry);
    int occurrences = 0;
    for (int l = 0; l < levels; l++) {
      if (list[l] == negated) {
        negatedLevel = l;
        occurrences++;
      }
    }
    int costIndex = -1;
    for (int r = 0; r < costVar.length; r++) {
      if (costVar[r] == negated) {
        costIndex = r;
        occurrences++;
      }
    }
    if (occurrences != 1) {
      return false;
    }
    if (!prepare()) {
      return false;
    }
    int mark = out.size();
    boolean done;
    if (costIndex >= 0) {
      // cost >= a: every path costs more than a - 1; cost <= a: every path costs less than a + 1
      done =
          switch (negatedKind) {
            case AtomicTrail.GE -> bound(costIndex, true, negatedValue - 1L, false, null, out);
            case AtomicTrail.LE -> bound(costIndex, false, negatedValue + 1L, false, null, out);
            default -> false;
          };
    } else {
      done = assign(negatedLevel, out);
    }
    if (!done) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure now.
   *
   * @param out where the reason entries are added
   * @return false when the paths do not imply it
   */
  boolean explainFailure(EntryList out) {
    if (!prepare()) {
      return false;
    }
    int mark = out.size();
    // no path at all, or every path too expensive or too cheap for one resource
    for (int r = 0; r < costVar.length; r++) {
      for (boolean upper : new boolean[] {true, false}) {
        long k =
            upper ? trail.maxBefore(costVar[r], position) : trail.minBefore(costVar[r], position);
        if (bound(r, upper, k, true, null, out)) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
      }
    }
    // a level whose every alive edge is ruled out by some bound
    for (int l = 0; l < levels; l++) {
      if (assign(l, out)) {
        out.sortUnique(mark);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  private boolean prepare() {
    int edges = edgeStart[levels];
    if (edges > EDGE_LIMIT) {
      return false;
    }
    before = new Before[levels];
    for (int l = 0; l < levels; l++) {
      before[l] = new Before(list[l]);
    }
    aliveEdge = new boolean[edges];
    for (int l = 0; l < levels; l++) {
      for (int e = edgeStart[l]; e < edgeStart[l + 1]; e++) {
        aliveEdge[e] = allowed(list[l], label[e]) && before[l].contains(label[e]);
      }
    }
    return true;
  }

  // whether the negated atom allows value v of variable x
  private boolean allowed(IntVar x, int v) {
    if (x != negated) {
      return true;
    }
    return switch (negatedKind) {
      case AtomicTrail.GE -> v < negatedValue;
      case AtomicTrail.LE -> v > negatedValue;
      default -> v == negatedValue;
    };
  }

  /**
   * Explains that no path goes through the alive edges of level l: each one costs more than the
   * maximum of a resource or less than its minimum on every path through it.
   */
  private boolean assign(int l, EntryList out) {
    int resources = costVar.length;
    long[][] fmin = new long[resources][];
    long[][] bmin = new long[resources][];
    long[][] fmax = new long[resources][];
    long[][] bmax = new long[resources][];
    for (int r = 0; r < resources; r++) {
      fmin[r] = forward(r, true, -1, null);
      bmin[r] = backward(r, true, -1);
      fmax[r] = forward(r, false, -1, null);
      bmax[r] = backward(r, false, -1);
    }
    // for each resource and side, the edges of level l it rules out
    boolean[][] upperSet = new boolean[resources][edgeStart[l + 1] - edgeStart[l]];
    boolean[][] lowerSet = new boolean[resources][edgeStart[l + 1] - edgeStart[l]];
    boolean[] upperUsed = new boolean[resources];
    boolean[] lowerUsed = new boolean[resources];
    for (int e = edgeStart[l]; e < edgeStart[l + 1]; e++) {
      if (!aliveEdge[e]) {
        continue;
      }
      boolean ruled = false;
      for (int r = 0; r < resources && !ruled; r++) {
        long shortest = add(fmin[r][source[e]], cost[r][e], bmin[r][target[e]], true);
        if (shortest > trail.maxBefore(costVar[r], position)) {
          upperSet[r][e - edgeStart[l]] = true;
          upperUsed[r] = true;
          ruled = true;
          continue;
        }
        long longest = add(fmax[r][source[e]], cost[r][e], bmax[r][target[e]], false);
        if (longest < trail.minBefore(costVar[r], position)) {
          lowerSet[r][e - edgeStart[l]] = true;
          lowerUsed[r] = true;
          ruled = true;
        }
      }
      if (!ruled) {
        return false;
      }
    }
    // the dead edges of level l with a label the negation allows are restored or cited by the
    // first group that sees them, and left out of the others
    boolean first = true;
    for (int r = 0; r < resources; r++) {
      for (boolean upper : new boolean[] {true, false}) {
        if (!(upper ? upperUsed[r] : lowerUsed[r])) {
          continue;
        }
        boolean[] set = upper ? upperSet[r] : lowerSet[r];
        long k =
            upper ? trail.maxBefore(costVar[r], position) : trail.minBefore(costVar[r], position);
        LevelRestriction only = new LevelRestriction(l, set, first);
        if (!bound(r, upper, k, true, only, out)) {
          return false;
        }
        first = false;
      }
    }
    if (first) {
      // no alive edge on level l: the dead ones are cited, or restored when no path reaches them
      LevelRestriction none =
          new LevelRestriction(l, new boolean[edgeStart[l + 1] - edgeStart[l]], true);
      return bound(0, true, Long.MAX_VALUE / 8, false, none, out);
    }
    return true;
  }

  /**
   * The edges of one level a group of the explanation keeps, and whether it handles the dead ones.
   */
  private record LevelRestriction(int level, boolean[] keep, boolean dead) {}

  /**
   * Explains that every path (through the kept edges of the restricted level) costs more than k
   * (upper) or less than k for resource r: the dead edges that cannot be restored are cited, and
   * the bound of the cost unless it comes from the negated atom (fromCost false).
   */
  private boolean bound(
      int r, boolean upper, long k, boolean fromCost, LevelRestriction only, EntryList out) {
    long[] b = backward(r, upper, only == null ? -1 : only.level, only);
    long[] f = new long[nodeStart[levels + 1]];
    long unreached = upper ? INF : -INF;
    Arrays.fill(f, unreached);
    f[0] = 0;
    Exclusions[] cite = new Exclusions[levels];
    for (int l = 0; l < levels; l++) {
      for (int e = edgeStart[l]; e < edgeStart[l + 1]; e++) {
        long fs = f[source[e]];
        if (fs == unreached) {
          continue;
        }
        boolean use;
        if (aliveEdge[e]) {
          use = only == null || only.level != l || only.keep[e - edgeStart[l]];
        } else if (!allowed(list[l], label[e]) || only != null && only.level == l && !only.dead) {
          use = false;
        } else {
          long through = add(fs, cost[r][e], b[target[e]], upper);
          if (upper ? through > k : through < k) {
            use = true;
          } else {
            if (cite[l] == null) {
              cite[l] = new Exclusions(l);
            }
            cite[l].exclude(label[e]);
            use = false;
          }
        }
        if (use) {
          long reach = fs + cost[r][e];
          int t = target[e];
          if (upper ? reach < f[t] : reach > f[t]) {
            f[t] = reach;
          }
        }
      }
    }
    long best = unreached;
    for (int n = nodeStart[levels]; n < nodeStart[levels + 1]; n++) {
      best = upper ? Math.min(best, f[n]) : Math.max(best, f[n]);
    }
    if (upper ? best <= k : best >= k) {
      return false;
    }
    for (Exclusions ex : cite) {
      if (ex != null && !ex.addTo(out)) {
        return false;
      }
    }
    if (fromCost && best != unreached) {
      IntVar c = costVar[r];
      // the weakest bound of the cost that every path still passes
      int entry =
          upper
              ? trail.earliestUpperBound(c, best - 1, position)
              : trail.earliestLowerBound(c, best + 1, position);
      if (entry == Integer.MAX_VALUE) {
        return false;
      }
      if (entry >= 0) {
        out.add(entry);
      }
    }
    return true;
  }

  private static long add(long a, long c, long b, boolean upper) {
    if (upper ? a >= INF || b >= INF : a <= -INF || b <= -INF) {
      return upper ? INF : -INF;
    }
    return a + c + b;
  }

  // shortest (upper) or longest paths from the source over the alive edges
  private long[] forward(int r, boolean upper, int restricted, LevelRestriction only) {
    long[] f = new long[nodeStart[levels + 1]];
    long unreached = upper ? INF : -INF;
    Arrays.fill(f, unreached);
    f[0] = 0;
    for (int l = 0; l < levels; l++) {
      for (int e = edgeStart[l]; e < edgeStart[l + 1]; e++) {
        if (!aliveEdge[e]
            || l == restricted && !only.keep[e - edgeStart[l]]
            || f[source[e]] == unreached) {
          continue;
        }
        long reach = f[source[e]] + cost[r][e];
        int t = target[e];
        if (upper ? reach < f[t] : reach > f[t]) {
          f[t] = reach;
        }
      }
    }
    return f;
  }

  private long[] backward(int r, boolean upper, int restricted) {
    return backward(r, upper, restricted, null);
  }

  // shortest (upper) or longest paths to a sink over the alive edges (of the kept ones on the
  // restricted level)
  private long[] backward(int r, boolean upper, int restricted, LevelRestriction only) {
    long[] b = new long[nodeStart[levels + 1]];
    long unreached = upper ? INF : -INF;
    Arrays.fill(b, unreached);
    for (int n = nodeStart[levels]; n < nodeStart[levels + 1]; n++) {
      b[n] = 0;
    }
    for (int l = levels - 1; l >= 0; l--) {
      for (int e = edgeStart[l]; e < edgeStart[l + 1]; e++) {
        if (!aliveEdge[e]
            || l == restricted && only != null && !only.keep[e - edgeStart[l]]
            || b[target[e]] == unreached) {
          continue;
        }
        long reach = b[target[e]] + cost[r][e];
        int s = source[e];
        if (upper ? reach < b[s] : reach > b[s]) {
          b[s] = reach;
        }
      }
    }
    return b;
  }

  /** A variable's domain just before the position, from its atoms. */
  private final class Before {
    final IntVar x;
    final IntDomain root;
    final int min;
    final int max;
    final int[] holeValue;
    final int[] holeEntry;

    Before(IntVar x) {
      this.x = x;
      root = trail.rootDomain(x);
      min = trail.minBefore(x, position);
      max = trail.maxBefore(x, position);
      EntryList atoms = new EntryList();
      trail.atomsBefore(x, position, atoms);
      int holes = 0;
      long[] pairs = new long[atoms.size()];
      for (int k = 0; k < atoms.size(); k++) {
        int f = atoms.get(k);
        if (trail.kind(f) == AtomicTrail.NE) {
          pairs[holes++] = ((long) trail.value(f) << 32) | (f & 0xffffffffL);
        }
      }
      Arrays.sort(pairs, 0, holes);
      holeValue = new int[holes];
      holeEntry = new int[holes];
      for (int k = 0; k < holes; k++) {
        holeValue[k] = (int) (pairs[k] >> 32);
        holeEntry[k] = (int) pairs[k];
      }
    }

    boolean contains(int v) {
      return v >= min && v <= max && root.contains(v) && Arrays.binarySearch(holeValue, v) < 0;
    }
  }

  /** The labels a level's variable must be kept away from, gathered before the atoms are added. */
  private final class Exclusions {
    private final Before d;
    private long below = Long.MIN_VALUE;
    private long above = Long.MAX_VALUE;
    private final EntryList holes = new EntryList();
    private boolean missing;

    Exclusions(int level) {
      this.d = before[level];
    }

    void exclude(int v) {
      if (!d.root.contains(v)) {
        return;
      }
      if (v < d.min) {
        below = Math.max(below, v);
      } else if (v > d.max) {
        above = Math.min(above, v);
      } else {
        int k = Arrays.binarySearch(d.holeValue, v);
        if (k >= 0) {
          holes.add(d.holeEntry[k]);
        } else {
          missing = true;
        }
      }
    }

    boolean addTo(EntryList out) {
      if (missing) {
        return false;
      }
      if (below != Long.MIN_VALUE) {
        int e = trail.earliestLowerBound(d.x, below + 1, position);
        if (e == Integer.MAX_VALUE) {
          return false;
        }
        if (e >= 0) {
          out.add(e);
        }
      }
      if (above != Long.MAX_VALUE) {
        int e = trail.earliestUpperBound(d.x, above - 1, position);
        if (e == Integer.MAX_VALUE) {
          return false;
        }
        if (e >= 0) {
          out.add(e);
        }
      }
      for (int k = 0; k < holes.size(); k++) {
        out.add(holes.get(k));
      }
      return true;
    }
  }
}
