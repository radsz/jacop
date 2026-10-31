/*
 * AlldiffExplanation.java
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

package org.jacop.constraints;

import java.util.Arrays;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of all different constraints by Hall sets. A value w removed from y is taken by a
 * set H of other variables whose domains together hold exactly |H| values, w among them; the reason
 * is the atoms that kept the domains of H inside those values. A failure is a set H whose domains
 * hold fewer than |H| values. Variables that may take an exception value are left out of the sets,
 * as they need no value of their own.
 *
 * <p>The sets are found from a maximum matching of the domains just before the entry: w is in a
 * Hall set when no alternating path leads from it to a free value, and the variables and values
 * that path search reaches are the set. Every pruning of a propagator of all different is implied
 * by such sets, so the explanation refuses only for large domains.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class AlldiffExplanation {

  /** The widest span of the variables' values considered. */
  private static final int SPAN_LIMIT = 1 << 16;

  /** The most edges of the value graph considered. */
  private static final int EDGE_LIMIT = 1 << 20;

  /** The most removed values of one atom explained one by one. */
  private static final int REMOVED_LIMIT = 256;

  private final AtomicTrail trail;
  private final int position;
  private IntVar[] vars;
  private int n;
  private int base;
  private int[] adjStart;
  private int[] adj;
  // per variable its strongest bound entries (or -1) and its != entries inside the bounds
  private int[] lowerEntry;
  private int[] upperEntry;
  private int[][] holeEntries;
  private int[] owner;
  private int[] mate;
  private boolean[] inValues;
  private boolean[] inSet;
  private int[] visited;
  private int stamp;
  private int[] queue;
  private int[] parent;

  private AlldiffExplanation(AtomicTrail trail, int position) {
    this.trail = trail;
    this.position = position;
  }

  /**
   * Adds to {@code out} the reason of an entry of one of the variables.
   *
   * @param trail the trail
   * @param entry the entry
   * @param list the variables
   * @param except the values the variables may share
   * @param out where the reason entries are added
   * @return false when some removed value is in no Hall set, or the domains are too large
   */
  static boolean explain(
      AtomicTrail trail, int entry, IntVar[] list, IntDomain except, EntryList out) {
    IntVar y = trail.variable(entry);
    IntDomain root = trail.rootDomain(y);
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    int mark = out.size();
    int min = trail.minBefore(y, entry);
    if (lo < min) {
      trail.addLowerBound(y, entry, out);
      lo = min;
    }
    int max = trail.maxBefore(y, entry);
    if (hi > max) {
      trail.addUpperBound(y, entry, out);
      hi = max;
    }
    if (lo > hi) {
      return true;
    }
    if ((long) hi - lo >= REMOVED_LIMIT) {
      out.truncate(mark);
      return false;
    }
    int bounded = out.size();
    if (byFixedVariables(trail, entry, list, y, lo, hi, root, except, out)) {
      out.sortUnique(mark);
      return true;
    }
    out.truncate(bounded);
    AlldiffExplanation e = new AlldiffExplanation(trail, entry);
    if (!e.build(list, y, except)) {
      out.truncate(mark);
      return false;
    }
    int unmatched = e.match();
    if (unmatched >= 0) {
      // the other variables could not all take different values already
      out.truncate(mark);
      e.violatedSet(unmatched);
      e.addReason(out);
      out.sortUnique(mark);
      return true;
    }
    for (int w = lo; w <= hi; w++) {
      if (!root.contains(w) || trail.excludedBefore(y, w, entry, out)) {
        continue;
      }
      if (except.contains(w) || !e.hallSet(w)) {
        out.truncate(mark);
        return false;
      }
    }
    e.addReason(out);
    out.sortUnique(mark);
    return true;
  }

  /**
   * The common case without the value graph: each removed value is the value of another variable
   * already fixed to it, so the Hall set of that value is the variable alone and its bounds are the
   * reason. The graph costs the size of all the variables' domains, the scan only their bounds.
   */
  private static boolean byFixedVariables(
      AtomicTrail trail,
      int entry,
      IntVar[] list,
      IntVar y,
      int lo,
      int hi,
      IntDomain root,
      IntDomain except,
      EntryList out) {
    for (int w = lo; w <= hi; w++) {
      if (!root.contains(w) || trail.excludedBefore(y, w, entry, out)) {
        continue;
      }
      if (except.contains(w)) {
        return false;
      }
      IntVar fixed = null;
      for (IntVar z : list) {
        if (z != y && trail.minBefore(z, entry) == w && trail.maxBefore(z, entry) == w) {
          fixed = z;
          break;
        }
      }
      if (fixed == null) {
        return false;
      }
      trail.addLowerBound(fixed, entry, out);
      trail.addUpperBound(fixed, entry, out);
    }
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure: a set of variables with fewer values than
   * variables.
   *
   * @param trail the trail
   * @param list the variables
   * @param except the values the variables may share
   * @param out where the reason entries are added
   * @return false when the variables can take different values, or the domains are too large
   */
  static boolean explainFailure(AtomicTrail trail, IntVar[] list, IntDomain except, EntryList out) {
    AlldiffExplanation e = new AlldiffExplanation(trail, trail.size());
    if (!e.build(list, null, except)) {
      return false;
    }
    int unmatched = e.match();
    if (unmatched < 0) {
      return false;
    }
    int mark = out.size();
    e.violatedSet(unmatched);
    e.addReason(out);
    out.sortUnique(mark);
    return true;
  }

  // the value graph of the variables other than y that cannot take an exception value
  private boolean build(IntVar[] list, IntVar y, IntDomain except) {
    int count = list.length;
    vars = new IntVar[count];
    lowerEntry = new int[count];
    upperEntry = new int[count];
    holeEntries = new int[count][];
    int[] min = new int[count];
    int[] max = new int[count];
    int lowest = Integer.MAX_VALUE;
    int highest = Integer.MIN_VALUE;
    EntryList atoms = new EntryList();
    for (IntVar z : list) {
      if (z == y) {
        continue;
      }
      int lo = trail.minBefore(z, position);
      int hi = trail.maxBefore(z, position);
      if (except.isIntersecting(lo, hi) && hasException(z, lo, hi, except)) {
        continue;
      }
      if ((long) hi - lo >= SPAN_LIMIT) {
        return false;
      }
      atoms.clear();
      trail.atomsBefore(z, position, atoms);
      int ge = -1;
      int le = -1;
      int holes = 0;
      int[] hole = new int[atoms.size()];
      for (int k = 0; k < atoms.size(); k++) {
        int f = atoms.get(k);
        switch (trail.kind(f)) {
          case AtomicTrail.GE -> ge = f;
          case AtomicTrail.LE -> le = f;
          default -> hole[holes++] = f;
        }
      }
      vars[n] = z;
      lowerEntry[n] = ge;
      upperEntry[n] = le;
      holeEntries[n] = Arrays.copyOf(hole, holes);
      min[n] = lo;
      max[n] = hi;
      lowest = Math.min(lowest, lo);
      highest = Math.max(highest, hi);
      n++;
    }
    if (n == 0) {
      base = 0;
      owner = new int[0];
      inValues = new boolean[0];
      inSet = new boolean[0];
      mate = new int[0];
      return true;
    }
    if ((long) highest - lowest >= SPAN_LIMIT) {
      return false;
    }
    base = lowest;
    int span = highest - lowest + 1;
    boolean[] isHole = new boolean[span];
    adjStart = new int[n + 1];
    int[] edges = new int[64];
    int e = 0;
    for (int k = 0; k < n; k++) {
      adjStart[k] = e;
      for (int f : holeEntries[k]) {
        isHole[trail.value(f) - base] = true;
      }
      // the root domain's intervals, so that a sparse domain costs its size and not its span
      for (IntervalEnumeration en = trail.rootDomain(vars[k]).intervalEnumeration();
          en.hasMoreElements(); ) {
        Interval i = en.nextElement();
        int to = Math.min(i.max(), max[k]);
        for (int v = Math.max(i.min(), min[k]); v <= to; v++) {
          if (!isHole[v - base]) {
            if (e == edges.length) {
              if (e >= EDGE_LIMIT) {
                return false;
              }
              edges = Arrays.copyOf(edges, 2 * e);
            }
            edges[e++] = v - base;
          }
        }
      }
      for (int f : holeEntries[k]) {
        isHole[trail.value(f) - base] = false;
      }
    }
    adjStart[n] = e;
    adj = edges;
    owner = new int[span];
    Arrays.fill(owner, -1);
    mate = new int[n];
    inValues = new boolean[span];
    inSet = new boolean[n];
    visited = new int[Math.max(n, span)];
    queue = new int[Math.max(n, span)];
    parent = new int[n];
    return true;
  }

  // whether z could take an exception value just before the position
  private boolean hasException(IntVar z, int lo, int hi, IntDomain except) {
    IntDomain root = trail.rootDomain(z);
    IntDomain candidates = except.intersect(lo, hi);
    if (candidates.getSize() > REMOVED_LIMIT) {
      return true;
    }
    for (ValueEnumeration en = candidates.valueEnumeration(); en.hasMoreElements(); ) {
      int v = en.nextElement();
      if (root.contains(v) && !trail.excludedBefore(z, v, position, new EntryList())) {
        return true;
      }
    }
    return false;
  }

  /** Finds a maximum matching; returns a variable it leaves unmatched, or -1. */
  private int match() {
    for (int k = 0; k < n; k++) {
      mate[k] = -1;
      for (int f = adjStart[k]; f < adjStart[k + 1]; f++) {
        if (owner[adj[f]] < 0) {
          mate[k] = adj[f];
          owner[adj[f]] = k;
          break;
        }
      }
    }
    for (int k = 0; k < n; k++) {
      if (mate[k] < 0 && !augment(k)) {
        return k;
      }
    }
    return -1;
  }

  private boolean augment(int root) {
    stamp++;
    int head = 0;
    int tail = 0;
    queue[tail++] = root;
    visited[root] = stamp;
    while (head < tail) {
      int u = queue[head++];
      for (int f = adjStart[u]; f < adjStart[u + 1]; f++) {
        int w = adj[f];
        int o = owner[w];
        if (o < 0) {
          int cur = u;
          int val = w;
          while (true) {
            int old = mate[cur];
            mate[cur] = val;
            owner[val] = cur;
            if (cur == root) {
              return true;
            }
            cur = parent[cur];
            val = old;
          }
        }
        if (visited[o] != stamp) {
          visited[o] = stamp;
          parent[o] = u;
          queue[tail++] = o;
        }
      }
    }
    return false;
  }

  /**
   * Whether value w (an actual value) is in a Hall set: matched, with no alternating path to a free
   * value. If so the set's variables and values are added to the marked ones.
   */
  private boolean hallSet(int w) {
    long offset = (long) w - base;
    if (offset < 0 || offset >= owner.length || owner[(int) offset] < 0) {
      return false;
    }
    int start = (int) offset;
    if (inValues[start]) {
      return true;
    }
    stamp++;
    int head = 0;
    int tail = 0;
    queue[tail++] = start;
    visited[start] = stamp;
    while (head < tail) {
      int z = owner[queue[head++]];
      for (int f = adjStart[z]; f < adjStart[z + 1]; f++) {
        int u = adj[f];
        if (owner[u] < 0) {
          return false;
        }
        if (visited[u] != stamp && !inValues[u]) {
          visited[u] = stamp;
          queue[tail++] = u;
        }
      }
    }
    for (int k = 0; k < tail; k++) {
      inValues[queue[k]] = true;
      inSet[owner[queue[k]]] = true;
    }
    return true;
  }

  /** Marks the variables reached from an unmatched one by alternating paths, and their values. */
  private void violatedSet(int unmatched) {
    int head = 0;
    int tail = 0;
    queue[tail++] = unmatched;
    inSet[unmatched] = true;
    while (head < tail) {
      int z = queue[head++];
      for (int f = adjStart[z]; f < adjStart[z + 1]; f++) {
        int u = adj[f];
        inValues[u] = true;
        int o = owner[u];
        if (o >= 0 && !inSet[o]) {
          inSet[o] = true;
          queue[tail++] = o;
        }
      }
    }
  }

  /** Adds the atoms that kept each marked variable's domain inside the marked values. */
  private void addReason(EntryList out) {
    for (int k = 0; k < n; k++) {
      if (!inSet[k]) {
        continue;
      }
      IntDomain root = trail.rootDomain(vars[k]);
      if (lowerEntry[k] >= 0 && outsideBelow(root, trail.value(lowerEntry[k]))) {
        out.add(lowerEntry[k]);
      }
      if (upperEntry[k] >= 0 && outsideAbove(root, trail.value(upperEntry[k]))) {
        out.add(upperEntry[k]);
      }
      for (int f : holeEntries[k]) {
        if (!inValues[trail.value(f) - base]) {
          out.add(f);
        }
      }
    }
  }

  // whether some value of root below bound is not marked
  private boolean outsideBelow(IntDomain root, int bound) {
    if (root.min() < base) {
      return true;
    }
    for (int v = root.min(); v < bound; v++) {
      if (root.contains(v) && !inValues[v - base]) {
        return true;
      }
    }
    return false;
  }

  // whether some value of root above bound is not marked
  private boolean outsideAbove(IntDomain root, int bound) {
    if (root.max() >= base + inValues.length) {
      return true;
    }
    for (int v = bound + 1; v <= root.max(); v++) {
      if (root.contains(v) && !inValues[v - base]) {
        return true;
      }
    }
    return false;
  }
}
