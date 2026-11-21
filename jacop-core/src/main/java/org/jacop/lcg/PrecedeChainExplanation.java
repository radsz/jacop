/*
 * PrecedeChainExplanation.java
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

package org.jacop.lcg;

import java.util.Arrays;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;

/**
 * Explanations of value_precede_chain(c, x) and seq_precede_chain(x) ({@link
 * org.jacop.constraints.SeqPrecedeChain}). Value c[r - 1] has rank r and every other value rank 0
 * (for seq_precede_chain value v &gt; 0 has rank v); a value of rank r &gt; 1 needs rank r - 1 at
 * an earlier position.
 *
 * <p>Two arguments give every pruning of the propagator:
 *
 * <ul>
 *   <li>forward: when the value of rank s is out of every domain before position i, no position
 *       before i takes a rank of at least s (the first one would have to be s), so x[i] takes no
 *       rank above s. The reason is the removal of that value before i.
 *   <li>backward: a position whose domain has only ranks of at least R needs rank R at or before
 *       it, and each rank r needs rank r - 1 before its own first position. Going down from R, the
 *       latest position that can hold rank r is the last one up to the deadline (the forcing
 *       position, or the position before the latest one of rank r + 1) whose domain has its value.
 *       When that is position i and the value is out of every domain before i, x[i] takes that
 *       value. The reason is the forcing domain and the removals of each rank's value between its
 *       latest position and its deadline.
 * </ul>
 *
 * <p>A failure is explained by a position none of whose values survives these arguments, or by a
 * rank with no position left before its deadline.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class PrecedeChainExplanation {

  // atom ranges larger than this are left to the generic reason
  private static final int MAX_VALUES = 10_000;

  private final AtomicTrail trail;
  private final IntVar[] x;
  private final int[] chain;
  private final int n;
  private final EntryList scratch = new EntryList();

  // the trail position the domains are read at
  private int position;

  // backward argument: the latest position of each rank, the deadline and whether it came from a
  // forcing position (forcedAt) rather than from the next rank
  private int[] latest = new int[0];
  private int[] deadline = new int[0];
  private int[] forcedAt = new int[0];

  private PrecedeChainExplanation(AtomicTrail trail, IntVar[] x, int[] chain) {
    this.trail = trail;
    this.x = x;
    this.chain = chain;
    this.n = x.length;
  }

  /**
   * Adds to {@code out} the reason of an atom the constraint propagated.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param x the variables of the constraint
   * @param chain the value chain, or null for seq_precede_chain
   * @param out where the reason entries are added
   * @return false when the arguments do not give the atom
   */
  public static boolean explain(
      AtomicTrail trail, int entry, IntVar[] x, int[] chain, EntryList out) {
    PrecedeChainExplanation e = new PrecedeChainExplanation(trail, x, chain);
    e.position = entry;
    IntVar v = trail.variable(entry);
    int mark = out.size();
    for (int i = 0; i < x.length; i++) {
      if (x[i] == v) {
        if (e.explainValues(i, trail.removedMin(entry), trail.removedMax(entry), out)) {
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  /**
   * Adds to {@code out} the reason of a failure of the constraint now.
   *
   * @param trail the trail
   * @param x the variables of the constraint
   * @param chain the value chain, or null for seq_precede_chain
   * @param out where the reason entries are added
   * @return false when the arguments do not give the failure
   */
  public static boolean explainFailure(AtomicTrail trail, IntVar[] x, int[] chain, EntryList out) {
    PrecedeChainExplanation e = new PrecedeChainExplanation(trail, x, chain);
    e.position = trail.size();
    int mark = out.size();
    int top = e.backward();
    if (top == -2) {
      return false;
    }
    if (top > 0) {
      // a rank with no position before its deadline (the ranks below it were not reached)
      for (int r = top; r >= 1; r--) {
        if (e.latest[r] < 0) {
          for (int j = 0; j <= e.deadline[r]; j++) {
            e.addExcluded(j, e.valueOf(r), out);
          }
          e.addDeadline(r, out);
          return true;
        }
      }
    }
    for (int i = 0; i < x.length; i++) {
      IntDomain root = trail.rootDomain(x[i]);
      if (root.isEmpty()) {
        continue;
      }
      if (e.explainValues(i, root.min(), root.max(), out)) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  private int rank(int v) {
    if (chain == null) {
      return Math.max(v, 0);
    }
    for (int r = 0; r < chain.length; r++) {
      if (chain[r] == v) {
        return r + 1;
      }
    }
    return 0;
  }

  private int valueOf(int r) {
    return chain == null ? r : chain[r - 1];
  }

  private boolean contains(int j, int v) {
    int mark = scratch.size();
    boolean out = trail.excludedBefore(x[j], v, position, scratch);
    scratch.truncate(mark);
    return !out;
  }

  private void addExcluded(int j, int v, EntryList out) {
    boolean excluded = trail.excludedBefore(x[j], v, position, out);
    assert excluded : x[j] + " still has " + v;
  }

  /**
   * Explains that no value of x[i] in [lo, hi] (of its root domain) is left: each is out of the
   * domain before the position, or excluded by the forward or the backward argument.
   */
  private boolean explainValues(int i, int lo, int hi, EntryList out) {
    IntDomain root = trail.rootDomain(x[i]);
    lo = Math.max(lo, root.min());
    hi = Math.min(hi, root.max());
    if (lo > hi) {
      return true;
    }
    if ((long) hi - lo > MAX_VALUES && root.getSize() > MAX_VALUES) {
      return false;
    }
    int s = -1; // the forward rank, computed when needed (0: none)
    int forced = -1; // the backward rank of x[i], computed when needed (0: none)
    boolean forward = false;
    boolean backward = false;
    for (int u = root.contains(lo) ? lo : root.nextValue(lo); u <= hi; u = root.nextValue(u)) {
      if (!trail.excludedBefore(x[i], u, position, out)) {
        if (s < 0) {
          s = forwardRank(i);
        }
        if (s > 0 && rank(u) > s) {
          forward = true;
        } else {
          if (forced < 0) {
            forced = backwardRank(i);
          }
          if (forced == 0 || u == valueOf(forced)) {
            return false;
          }
          backward = true;
        }
      }
      if (u >= root.max()) {
        break;
      }
    }
    if (forward) {
      for (int j = 0; j < i; j++) {
        addExcluded(j, valueOf(s), out);
      }
    }
    if (backward) {
      int v = valueOf(forced);
      for (int j = 0; j < i; j++) {
        addExcluded(j, v, out);
      }
      for (int j = i + 1; j <= deadline[forced]; j++) {
        addExcluded(j, v, out);
      }
      addDeadline(forced, out);
    }
    return true;
  }

  /** The rank of the forward argument at position i: the rank whose value is out of x[0..i). */
  private int forwardRank(int i) {
    int up = 0;
    for (int j = 0; j < i; j++) {
      if ((chain == null || up < chain.length) && contains(j, valueOf(up + 1))) {
        up++;
      }
    }
    if (chain != null && up >= chain.length) {
      return 0;
    }
    int v = valueOf(up + 1);
    for (int j = 0; j < i; j++) {
      if (contains(j, v)) {
        return 0;
      }
    }
    return up + 1;
  }

  /**
   * The rank the backward argument forces on x[i], or 0: the latest position of that rank is i and
   * its value is out of x[0..i).
   */
  private int backwardRank(int i) {
    int top = backward();
    if (top <= 0) {
      return 0;
    }
    for (int r = top; r >= 1; r--) {
      if (latest[r] < i) {
        return 0;
      }
      if (latest[r] == i) {
        int v = valueOf(r);
        for (int j = 0; j < i; j++) {
          if (contains(j, v)) {
            return 0;
          }
        }
        return r;
      }
    }
    return 0;
  }

  /**
   * Runs the backward argument from the largest forced rank: fills latest, deadline and forcedAt
   * for ranks 1..top. Returns top (0 when no position is forced to a positive rank), or -2 when a
   * domain is too large to read.
   */
  private int backward() {
    int[] minRank = new int[n];
    int top = 0;
    for (int j = 0; j < n; j++) {
      minRank[j] = minRank(j);
      if (minRank[j] < 0) {
        return -2;
      }
      top = Math.max(top, minRank[j]);
    }
    if (top == 0) {
      return 0;
    }
    latest = new int[top + 2];
    deadline = new int[top + 2];
    forcedAt = new int[top + 2];
    Arrays.fill(latest, -1);
    // the first position forced to rank r or above
    int[] earliest = new int[top + 2];
    Arrays.fill(earliest, n);
    for (int j = n - 1; j >= 0; j--) {
      for (int r = 1; r <= minRank[j]; r++) {
        earliest[r] = j;
      }
    }
    int next = n; // latest position of rank r + 1
    for (int r = top; r >= 1; r--) {
      int d;
      if (earliest[r] < next) {
        d = earliest[r];
        forcedAt[r] = earliest[r];
      } else {
        d = next - 1;
        forcedAt[r] = -1;
      }
      deadline[r] = d;
      int v = valueOf(r);
      int p = d;
      while (p >= 0 && !contains(p, v)) {
        p--;
      }
      latest[r] = p;
      if (p < 0) {
        return top;
      }
      next = p;
    }
    return top;
  }

  /** The smallest rank in x[j]'s domain before the position, or -1 when it is too large to read. */
  private int minRank(int j) {
    if (chain == null) {
      return Math.max(trail.minBefore(x[j], position), 0);
    }
    IntDomain root = trail.rootDomain(x[j]);
    if (root.getSize() > MAX_VALUES) {
      return -1;
    }
    int best = Integer.MAX_VALUE;
    for (var e = root.valueEnumeration(); e.hasMoreElements(); ) {
      int u = e.nextElement();
      if (contains(j, u)) {
        best = Math.min(best, rank(u));
        if (best == 0) {
          break;
        }
      }
    }
    return best == Integer.MAX_VALUE ? 0 : best;
  }

  /** Adds why rank r must be taken at or before its deadline. */
  private void addDeadline(int r, EntryList out) {
    for (int q = r; ; q++) {
      if (forcedAt[q] >= 0) {
        // x[forcedAt[q]] has no value below rank q
        int j = forcedAt[q];
        if (chain == null) {
          trail.addBoundReaching(x[j], position, true, q, out);
        } else {
          IntDomain root = trail.rootDomain(x[j]);
          for (var e = root.valueEnumeration(); e.hasMoreElements(); ) {
            int u = e.nextElement();
            if (rank(u) < q) {
              addExcluded(j, u, out);
            }
          }
        }
        return;
      }
      // rank q + 1 is taken at latest[q + 1] at the latest: its value is out after it
      int v = valueOf(q + 1);
      for (int j = latest[q + 1] + 1; j <= deadline[q + 1]; j++) {
        addExcluded(j, v, out);
      }
    }
  }
}
