/*
 * FixPropagateRepair.java
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

package org.jacop.search.ls;

import java.util.Arrays;
import java.util.SplittableRandom;
import java.util.function.BooleanSupplier;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * A fix-propagate-repair dive in the store (Salvagnin, Roberti and Fischetti, "A
 * fix-propagate-repair heuristic for mixed integer programming", Mathematical Programming
 * Computation 17, 2025, pp. 111-139). Variables are fixed one at a time to a preferred value, each
 * fixing propagated. When a fixing fails, the value is first removed (a one-level backtrack). When
 * that fails as well, the dive does not backtrack: the partial assignment is repaired in place in
 * the manner of WalkSAT (Selman, Kautz and Cohen, "Noise strategies for improving local search",
 * AAAI 1994), by moving an earlier fixing of a variable of the constraint that failed to another
 * value of its domain. The fixings made after it are replayed; those that no longer hold are
 * dropped (their number is the damage of the move) and their variables are fixed again later in the
 * dive.
 *
 * <p>The paper's repair works on the activities of linear rows; here the constraint that failed in
 * the store's propagation stands for the violated row, and propagation, not a shift by the row's
 * slack, gives the implications of a move. A variable that repair cannot place within its budget is
 * left out of the dive; the values of the dive then start the local search ({@link LocalSearch}),
 * which repairs the rest.
 *
 * <p>The store is at the level it had before {@link #dive} when it returns.
 */
final class FixPropagateRepair {

  // repair moves tried for one variable that cannot be fixed
  private static final int MOVES_PER_FAILURE = 12;
  // values removed from one variable before it goes to repair
  private static final int REMOVALS_PER_VARIABLE = 2;
  // decisions of the failed constraint a repair chooses among
  private static final int CANDIDATES = 8;
  // the WalkSAT noise: the chance of a random candidate in place of the most recent one
  private static final double NOISE = 0.5;

  private final Store store;
  private final IntVar[] vars;
  private final SplittableRandom random;
  private final BooleanSupplier expired;
  private final java.util.Map<IntVar, Integer> index;

  // the decisions: variable, value, and whether it was a removal (x != v) rather than a fixing
  private int[] decVar;
  private int[] decVal;
  private boolean[] decRemoval;
  private int depth;
  // the decision fixing each variable, or -1
  private final int[] decOf;
  // the level of the first decision is root + 1
  private int root;
  // variables dropped by replays, fixed again before the dive goes on
  private int[] pending;
  private int pendingCount;

  // statistics
  long dives;
  long complete;
  long fixings;
  long repairs;
  long repairMoves;
  long dropped;
  long skipped;

  FixPropagateRepair(
      Store store,
      IntVar[] vars,
      java.util.Map<IntVar, Integer> index,
      SplittableRandom random,
      BooleanSupplier expired) {
    this.store = store;
    this.vars = vars;
    this.index = index;
    this.random = random;
    this.expired = expired;
    int n = vars.length;
    decVar = new int[Math.max(16, n)];
    decVal = new int[decVar.length];
    decRemoval = new boolean[decVar.length];
    decOf = new int[n];
    pending = new int[16];
  }

  /**
   * One dive over the variables in the given order.
   *
   * @param order the indices of the variables, in the order they are fixed.
   * @param preferred the preferred value of each variable, clipped to its domain when fixed.
   * @param cost the cost variable whose maximum is bound, or null.
   * @param bound the largest cost allowed when cost is given.
   * @param out the values of the variables at the end of the dive: the fixed value, or for a
   *     variable left out, its preferred value nearest in its domain at the end.
   * @return true when every variable was fixed with propagation, which makes the values a solution
   *     of the store's constraints.
   */
  boolean dive(int[] order, int[] preferred, IntVar cost, long bound, int[] out) {
    dives++;
    int base = store.level;
    Arrays.fill(decOf, -1);
    depth = 0;
    pendingCount = 0;
    boolean[] left = new boolean[vars.length];
    boolean whole = true;
    try {
      if (cost != null && bound < cost.max()) {
        store.setLevel(store.level + 1);
        try {
          if (bound < cost.min()) {
            return false;
          }
          cost.domain.inMax(store.level, cost, (int) bound);
          if (!store.consistency()) {
            return false;
          }
        } catch (FailException _) {
          return false;
        }
      }
      root = store.level;
      int cursor = 0;
      int removals = 0;
      int last = -1;
      while (true) {
        if (expired.getAsBoolean()) {
          whole = false;
          break;
        }
        int i = -1;
        while (pendingCount > 0) {
          int p = pending[--pendingCount];
          if (!vars[p].singleton() && !left[p]) {
            i = p;
            break;
          }
        }
        if (i < 0) {
          while (cursor < order.length
              && (vars[order[cursor]].singleton() || left[order[cursor]])) {
            cursor++;
          }
          if (cursor == order.length) {
            break;
          }
          i = order[cursor];
        }
        if (i != last) {
          removals = 0;
          last = i;
        }
        IntVar x = vars[i];
        int v = nearest(x.dom(), preferred[i]);
        if (fix(i, v, false)) {
          continue;
        }
        Constraint failed = store.recentlyFailedConstraint;
        if (removals++ < REMOVALS_PER_VARIABLE && fix(i, v, true)) {
          continue;
        }
        if (!repair(i, preferred[i], failed)) {
          left[i] = true;
          whole = false;
          skipped++;
        }
      }
      for (int k = 0; k < vars.length; k++) {
        IntVar x = vars[k];
        out[k] = x.singleton() ? x.value() : nearest(x.dom(), preferred[k]);
        if (!x.singleton()) {
          whole = false;
        }
      }
      if (whole) {
        complete++;
      }
      return whole;
    } finally {
      while (store.level > base) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
    }
  }

  /**
   * Repairs the partial assignment so that variable i can be fixed: moves an earlier fixing of a
   * variable of the failed constraint to another value, replays the later fixings, and tries i
   * again.
   */
  private boolean repair(int i, int pref, Constraint failed) {
    repairs++;
    int[] cands = new int[CANDIDATES];
    for (int move = 0; move < MOVES_PER_FAILURE && !expired.getAsBoolean(); move++) {
      int nc = candidates(failed, cands);
      if (nc == 0) {
        return false;
      }
      // WalkSAT's greedy choice, the move that undoes least, is approximated by the most recent
      // decision (the fewest fixings to replay); with the noise, a random one
      int k = cands[0];
      if (random.nextDouble() < NOISE) {
        k = cands[random.nextInt(nc)];
      }
      repairMoves++;
      if (!moveDecision(k)) {
        continue;
      }
      IntVar x = vars[i];
      if (x.singleton()) {
        return true;
      }
      if (fix(i, nearest(x.dom(), pref), false)) {
        return true;
      }
      Constraint f = store.recentlyFailedConstraint;
      if (f != null) {
        failed = f;
      }
    }
    return false;
  }

  /**
   * The decisions that fixed variables of the failed constraint, most recent first; the most recent
   * decisions when the constraint has none or is not known.
   */
  private int candidates(Constraint failed, int[] out) {
    int n = 0;
    if (failed != null) {
      int best = -1;
      for (Var v : failed.arguments()) {
        Integer p = index.get(v);
        if (p == null) {
          continue;
        }
        int d = decOf[p];
        if (d < 0 || decRemoval[d] || has(out, n, d)) {
          continue;
        }
        if (n < out.length) {
          out[n++] = d;
        } else {
          // keep the most recent ones
          int min = 0;
          for (int t = 1; t < n; t++) {
            if (out[t] < out[min]) {
              min = t;
            }
          }
          if (d > out[min]) {
            out[min] = d;
          }
        }
        best = Math.max(best, d);
      }
      if (n > 0) {
        // the most recent first
        for (int t = 0; t < n; t++) {
          if (out[t] == best) {
            out[t] = out[0];
            out[0] = best;
            break;
          }
        }
        return n;
      }
    }
    for (int d = depth - 1; d >= 0 && n < 3; d--) {
      if (!decRemoval[d]) {
        out[n++] = d;
      }
    }
    return n;
  }

  private static boolean has(int[] a, int n, int x) {
    for (int k = 0; k < n; k++) {
      if (a[k] == x) {
        return true;
      }
    }
    return false;
  }

  /**
   * Moves decision k to another value of its variable and replays the decisions after it. A
   * decision that no longer holds is dropped and its variable fixed again later.
   *
   * @return false when no other value holds, with the decisions as they were.
   */
  private boolean moveDecision(int k) {
    int y = decVar[k];
    int w = decVal[k];
    int tail = depth - k - 1;
    int[] tv = Arrays.copyOfRange(decVar, k + 1, depth);
    int[] tw = Arrays.copyOfRange(decVal, k + 1, depth);
    boolean[] tr = Arrays.copyOfRange(decRemoval, k + 1, depth);
    backtrackTo(k);
    IntDomain d = vars[y].dom();
    int other = shifted(d, w);
    boolean moved = other != w && fix(y, other, false);
    if (!moved) {
      // the old decision holds again: propagation is the same
      if (!fix(y, w, false)) {
        // cannot happen unless propagation is not deterministic; the variable goes back to the dive
        push(y);
      }
    }
    for (int t = 0; t < tail; t++) {
      int z = tv[t];
      IntVar x = vars[z];
      if (tr[t]) {
        if (x.domain.contains(tw[t]) && !x.singleton()) {
          fix(z, tw[t], true);
        }
        continue;
      }
      if (x.singleton() && x.value() == tw[t]) {
        continue;
      }
      if (x.singleton() || !x.domain.contains(tw[t]) || !fix(z, tw[t], false)) {
        dropped++;
        push(z);
      }
    }
    return moved;
  }

  // another value of the domain: the neighbour of w on a random side, or one at random
  private int shifted(IntDomain d, int w) {
    if (d.singleton()) {
      return d.min();
    }
    if (random.nextInt(4) == 0) {
      int v = d.getElementAt(random.nextInt(d.getSize()));
      if (v != w) {
        return v;
      }
    }
    boolean up = random.nextBoolean();
    if (w >= d.max()) {
      up = false;
    } else if (w <= d.min()) {
      up = true;
    }
    int v = up ? d.nextValue(w) : d.previousValue(w);
    if (v == w) {
      v = up ? d.previousValue(w) : d.nextValue(w);
    }
    return v;
  }

  private void push(int i) {
    if (pendingCount == pending.length) {
      pending = Arrays.copyOf(pending, 2 * pendingCount);
    }
    pending[pendingCount++] = i;
  }

  // removes the levels of decision k and the later ones
  private void backtrackTo(int k) {
    int level = root + k;
    while (store.level > level) {
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }
    for (int t = k; t < depth; t++) {
      if (!decRemoval[t] && decOf[decVar[t]] == t) {
        decOf[decVar[t]] = -1;
      }
    }
    depth = k;
  }

  /**
   * Fixes variable i to v (or removes v) at a new level and propagates; the level is kept as a
   * decision when propagation holds, removed otherwise.
   */
  private boolean fix(int i, int v, boolean removal) {
    IntVar x = vars[i];
    store.setLevel(store.level + 1);
    boolean ok;
    try {
      if (removal) {
        x.domain.inComplement(store.level, x, v);
      } else {
        x.domain.in(store.level, x, v, v);
      }
      ok = store.consistency();
    } catch (FailException _) {
      ok = false;
    }
    if (!ok) {
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
      return false;
    }
    fixings++;
    if (depth == decVar.length) {
      decVar = Arrays.copyOf(decVar, 2 * depth);
      decVal = Arrays.copyOf(decVal, 2 * depth);
      decRemoval = Arrays.copyOf(decRemoval, 2 * depth);
    }
    decVar[depth] = i;
    decVal[depth] = v;
    decRemoval[depth] = removal;
    if (!removal) {
      decOf[i] = depth;
    }
    depth++;
    return true;
  }

  // the value of the domain nearest to v
  static int nearest(IntDomain d, int v) {
    if (d.contains(v)) {
      return v;
    }
    if (v <= d.min()) {
      return d.min();
    }
    if (v >= d.max()) {
      return d.max();
    }
    int up = d.nextValue(v);
    int down = d.previousValue(v);
    return (long) up - v <= (long) v - down ? up : down;
  }
}
