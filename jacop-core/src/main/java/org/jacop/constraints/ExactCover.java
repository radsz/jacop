/*
 * ExactCover.java
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Exact cover: every element {@code e} in {@code 0..n-1} is covered by exactly one selected option,
 * where option {@code o} is selected when the 0/1 variable {@code x[o]} is 1 and covers the
 * elements {@code sets[o]}. It is the conjunction of {@code sum(x[o] : e in sets[o]) = 1} over all
 * elements.
 *
 * <p>The propagator keeps, for every element, the number of options that can still cover it and the
 * selected option covering it, and restores them on backtracking from a stack of the changes, as
 * the dancing links of Knuth's Algorithm X hide and unhide the rows and columns of the matrix. It
 * does what the decomposition into one equality per element does (rule DL of Chabert and Solnon):
 * an option sharing an element with a selected option is removed, an element no option can cover
 * fails, and the only option left for an element is selected. It also does the stronger rule DL+ of
 * Chabert and Solnon, which the decomposition does not do: when every option that can still cover
 * an element {@code a} also covers an element {@code b}, the options that cover {@code b} but not
 * {@code a} are removed, since selecting one of them would leave {@code a} without an option. In a
 * tiling, where every piece is an element covered by its placements, this removes the placements of
 * a piece that miss a cell only that piece can still cover. The rule is checked for the elements
 * whose number of options changed.
 *
 * <p>For lazy clause generation the reasons are short: a removal because of a selected option is
 * explained by that option, a selection by the removed other options of its element, a failure by
 * the removed options of an element or by two selected options sharing one. A removal of {@code o}
 * by DL+ at element {@code a} is explained by the removed options of {@code a} that do not share an
 * element with {@code o}: with them removed and {@code o} selected, no option can cover {@code a}.
 *
 * <p>The constraint must be imposed at level 0. It watches the values of its variables ({@link
 * Store#watchValue}) instead of being attached to them.
 *
 * <p>References:
 *
 * <ul>
 *   <li>Maxime Chabert and Christine Solnon. A Global Constraint for the Exact Cover Problem:
 *       Application to Conceptual Clustering. Journal of Artificial Intelligence Research 67, pages
 *       509-547, 2020. doi: 10.1613/jair.1.11870
 *   <li>Donald E. Knuth. Dancing Links. In Millennial Perspectives in Computer Science, pages
 *       187-214, Palgrave, 2000. arXiv: cs/0011047
 *   <li>Donald E. Knuth. The Art of Computer Programming, Volume 4B, Combinatorial Algorithms, Part
 *       2, Section 7.2.2.1, Dancing links. Addison-Wesley, 2022.
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ExactCover extends Constraint
    implements SatisfiedPresent, Stateful, Copyable<ExactCover>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The variables of the options. */
  private final IntVar[] x;

  /** The elements covered by every option, sorted, without repetitions. */
  private final int[][] sets;

  /** The options covering every element. */
  private final int[][] cover;

  private final Map<IntVar, Integer> position = new IdentityHashMap<>();

  /** Number of options of every element that are not 0. */
  private final int[] count;

  /** The selected option of every element, or -1. */
  private final int[] chosen;

  /** Changes processed, as option * 2 + value, with their levels, undone on backtracking. */
  private int[] done;

  private int[] doneLevel;
  private int doneSize;

  /** The options whose values are not processed yet, as option * 2 + value. */
  private int[] pending;

  private int pendingSize;

  /** Whether the value of an option is processed (bit 0 for value 0, bit 1 for value 1). */
  private final byte[] state;

  /** The elements whose number of options changed, for DL+. */
  private final int[] dirty;

  private final boolean[] isDirty;
  private int dirtySize;

  // scratch for DL+: options of the element, and how many of them cover each element
  private final int[] mark;
  private final int[] hits;
  private int stamp;
  private final int[] touched;

  /** Why an option got its value: the kind and an option or element. */
  private final byte[] reasonKind;

  private final int[] reasonArg;

  static final byte BY_SELECTED = 1;
  static final byte BY_ELEMENT = 2;
  static final byte BY_INCLUSION = 3;

  /** The failure found last: its kind, element and options. */
  private int failElement = -1;

  private int failOption1 = -1;
  private int failOption2 = -1;

  private byte failKind;

  static final byte FAIL_ELEMENT = 1;
  static final byte FAIL_PAIR = 2;
  static final byte FAIL_INCLUSION = 3;

  private final int[] seenAt;

  private boolean firstCall = true;

  /** Switches the DL+ rule off (system property org.jacop.exactCover.inclusion=false). */
  static final boolean INCLUSION =
      !"false".equalsIgnoreCase(System.getProperty("org.jacop.exactCover.inclusion"));

  /** Statistics: options removed by DL+. */
  public long inclusionRemovals;

  /** Statistics: options removed or selected by the other rules. */
  public long propagations;

  /**
   * It constructs an exact cover constraint.
   *
   * @param x the 0/1 variables of the options, without repetitions
   * @param sets the elements covered by every option, in 0..n-1
   * @param n the number of elements
   */
  public ExactCover(IntVar[] x, int[][] sets, int n) {
    checkInputForNullness("x", x);
    checkInputForNullness("sets", sets);
    if (x.length != sets.length) {
      throw new IllegalArgumentException("ExactCover: x and sets differ in length.");
    }
    numberId = idNumber.incrementAndGet();
    queueIndex = 1;
    this.x = Arrays.copyOf(x, x.length);
    this.sets = new int[x.length][];
    int[] size = new int[n];
    for (int o = 0; o < x.length; o++) {
      IntVar v = x[o];
      if (v.min() < 0 || v.max() > 1) {
        throw new IllegalArgumentException("ExactCover: variable " + v + " is not 0/1.");
      }
      if (position.put(v, o) != null) {
        throw new IllegalArgumentException("ExactCover: variable " + v + " is listed twice.");
      }
      int[] s = Arrays.stream(sets[o]).sorted().distinct().toArray();
      for (int e : s) {
        if (e < 0 || e >= n) {
          throw new IllegalArgumentException(
              "ExactCover: element " + e + " is not in 0.." + (n - 1));
        }
        size[e]++;
      }
      this.sets[o] = s;
    }
    cover = new int[n][];
    for (int e = 0; e < n; e++) {
      cover[e] = new int[size[e]];
    }
    int[] fill = new int[n];
    for (int o = 0; o < x.length; o++) {
      for (int e : this.sets[o]) {
        cover[e][fill[e]++] = o;
      }
    }
    count = size.clone();
    chosen = new int[n];
    Arrays.fill(chosen, -1);
    done = new int[64];
    doneLevel = new int[64];
    pending = new int[64];
    state = new byte[x.length];
    dirty = new int[n];
    isDirty = new boolean[n];
    mark = new int[x.length];
    hits = new int[n];
    touched = new int[n];
    seenAt = new int[n];
    reasonKind = new byte[x.length];
    reasonArg = new int[x.length];
    setScope(this.x);
  }

  /**
   * It returns the number of elements.
   *
   * @return the number of elements
   */
  public int numberOfElements() {
    return cover.length;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  /**
   * Imposes the constraint, which watches the values of its variables. It must be imposed at level
   * 0.
   *
   * @param store the constraint store
   */
  @Override
  public void impose(Store store) {
    if (store.level != 0) {
      throw new IllegalStateException("ExactCover must be imposed at level 0");
    }
    for (int o = 0; o < x.length; o++) {
      x[o].adjustDegree(1);
      if (!x[o].singleton()) {
        store.watchValue(x[o], 0, this, 2 * o);
        store.watchValue(x[o], 1, this, 2 * o + 1);
      }
    }
    store.addChanged(this);
    store.countConstraint();
    store.registerRemoveLevelListener(this);
  }

  @Override
  public boolean valueWatchFired(int level, Var v, int tag) {
    push(tag);
    return true;
  }

  @Override
  public boolean countsValueWatch(int value, int tag) {
    return (tag & 1) == value;
  }

  private void push(int event) {
    if (pendingSize == pending.length) {
      pending = Arrays.copyOf(pending, 2 * pendingSize);
    }
    pending[pendingSize++] = event;
  }

  @Override
  public void removeLevel(int level) {
    pendingSize = 0;
    while (doneSize > 0 && doneLevel[doneSize - 1] >= level) {
      int event = done[--doneSize];
      int o = event >>> 1;
      state[o] = 0;
      if ((event & 1) == 0) {
        for (int e : sets[o]) {
          count[e]++;
        }
      } else {
        for (int e : sets[o]) {
          chosen[e] = -1;
        }
      }
    }
    while (dirtySize > 0) {
      isDirty[dirty[--dirtySize]] = false;
    }
  }

  @Override
  public void consistency(Store store) {
    if (firstCall) {
      firstCall = false;
      for (int o = 0; o < x.length; o++) {
        if (x[o].singleton()) {
          push(2 * o + x[o].value());
        }
      }
      for (int e = 0; e < cover.length; e++) {
        markDirty(e);
        if (cover[e].length == 0) {
          fail(FAIL_ELEMENT, e, -1, -1);
        }
        if (cover[e].length == 1 && x[cover[e][0]].min() == 0) {
          int p = cover[e][0];
          reasonKind[p] = BY_ELEMENT;
          reasonArg[p] = e;
          x[p].domain.inValue(store.level, x[p], 1);
        }
      }
    }
    do {
      while (pendingSize > 0) {
        process(store, pending[--pendingSize]);
      }
      if (INCLUSION) {
        while (dirtySize > 0 && pendingSize == 0) {
          int a = dirty[--dirtySize];
          isDirty[a] = false;
          inclusion(store, a);
        }
      } else {
        while (dirtySize > 0) {
          isDirty[dirty[--dirtySize]] = false;
        }
      }
    } while (pendingSize > 0);
    assert atFixpoint() : "ExactCover: the counts differ from the domains";
  }

  // the number of options of every element agrees with the domains, and no element is left
  // without an option or with one option that is not selected
  private boolean atFixpoint() {
    for (int e = 0; e < cover.length; e++) {
      int alive = 0;
      int ones = 0;
      for (int p : cover[e]) {
        alive += x[p].max();
        ones += x[p].min();
      }
      if (alive != count[e] || ones > 1 || alive == 0 || alive == 1 && ones == 0) {
        return false;
      }
    }
    return true;
  }

  // an event is recorded only once its changes are all made, so that undoing it is exact
  private void process(Store store, int event) {
    int o = event >>> 1;
    int value = event & 1;
    if ((state[o] & (1 << value)) != 0) {
      return;
    }
    if (value == 0) {
      state[o] |= 1;
      record(event, store.level);
      for (int e : sets[o]) {
        count[e]--;
      }
      for (int e : sets[o]) {
        if (chosen[e] < 0) {
          removed(store, e);
        }
      }
    } else {
      for (int e : sets[o]) {
        if (chosen[e] >= 0 && chosen[e] != o) {
          fail(FAIL_PAIR, -1, o, chosen[e]);
        }
      }
      state[o] |= 2;
      record(event, store.level);
      for (int e : sets[o]) {
        chosen[e] = o;
      }
      for (int e : sets[o]) {
        for (int p : cover[e]) {
          if (p != o && x[p].max() == 1) {
            if (x[p].min() == 1) {
              fail(FAIL_PAIR, -1, o, p);
            }
            reasonKind[p] = BY_SELECTED;
            reasonArg[p] = o;
            propagations++;
            x[p].domain.inValue(store.level, x[p], 0);
          }
        }
      }
    }
  }

  // an option of e, not covered yet, was removed: fail without options, select the last one
  private void removed(Store store, int e) {
    if (count[e] == 0) {
      fail(FAIL_ELEMENT, e, -1, -1);
    }
    markDirty(e);
    if (count[e] == 1) {
      for (int p : cover[e]) {
        if (x[p].max() == 1) {
          if (x[p].min() == 0) {
            reasonKind[p] = BY_ELEMENT;
            reasonArg[p] = e;
            propagations++;
            x[p].domain.inValue(store.level, x[p], 1);
          }
          return;
        }
      }
    }
  }

  private void record(int event, int level) {
    if (doneSize == done.length) {
      done = Arrays.copyOf(done, 2 * doneSize);
      doneLevel = Arrays.copyOf(doneLevel, 2 * doneSize);
    }
    done[doneSize] = event;
    doneLevel[doneSize++] = level;
  }

  private void markDirty(int e) {
    if (!isDirty[e]) {
      isDirty[e] = true;
      dirty[dirtySize++] = e;
    }
  }

  // DL+: when every option of a covers b, the options of b that miss a are removed
  private void inclusion(Store store, int a) {
    if (chosen[a] >= 0) {
      return;
    }
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(mark, 0);
      Arrays.fill(seenAt, 0);
      stamp = 1;
    }
    int options = 0;
    int size = 0;
    for (int c : cover[a]) {
      if (x[c].max() == 0) {
        continue;
      }
      mark[c] = stamp;
      options++;
      for (int b : sets[c]) {
        if (seenAt[b] != stamp) {
          seenAt[b] = stamp;
          hits[b] = 0;
          touched[size++] = b;
        }
        hits[b]++;
      }
    }
    for (int t = 0; t < size; t++) {
      int b = touched[t];
      if (b == a || hits[b] != options || chosen[b] >= 0 || count[b] == options) {
        continue;
      }
      for (int p : cover[b]) {
        // every option of a that is not 0 is marked, so p misses a
        if (mark[p] != stamp && x[p].max() == 1) {
          if (x[p].min() == 1) {
            fail(FAIL_INCLUSION, a, p, -1);
          }
          reasonKind[p] = BY_INCLUSION;
          reasonArg[p] = a;
          inclusionRemovals++;
          x[p].domain.inValue(store.level, x[p], 0);
        }
      }
    }
  }

  private void fail(byte kind, int element, int option1, int option2) {
    failKind = kind;
    failElement = element;
    failOption1 = option1;
    failOption2 = option2;
    throw Store.failException;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    Integer pos = position.get(trail.variable(entry));
    if (pos == null) {
      return false;
    }
    int p = pos;
    int before = entry;
    boolean one = trail.kind(entry) == AtomicTrail.GE;
    switch (reasonKind[p]) {
      case BY_SELECTED -> {
        int o = reasonArg[p];
        if (one || trail.minBefore(x[o], before) != 1) {
          return false;
        }
        trail.addLowerBound(x[o], before, out);
        return true;
      }
      case BY_ELEMENT -> {
        int e = reasonArg[p];
        if (!one) {
          return false;
        }
        for (int q : cover[e]) {
          if (q != p && !zeroBefore(trail, q, before, out)) {
            return false;
          }
        }
        return true;
      }
      case BY_INCLUSION -> {
        if (one) {
          return false;
        }
        return missing(trail, reasonArg[p], p, before, out);
      }
      default -> {
        return false;
      }
    }
  }

  // the options of a that share no element with p, all 0 before the position
  private boolean missing(AtomicTrail trail, int a, int p, int before, EntryList out) {
    for (int q : cover[a]) {
      if (q != p && !intersects(sets[q], sets[p]) && !zeroBefore(trail, q, before, out)) {
        return false;
      }
    }
    return true;
  }

  private boolean zeroBefore(AtomicTrail trail, int q, int before, EntryList out) {
    if (trail.maxBefore(x[q], before) != 0) {
      return false;
    }
    trail.addUpperBound(x[q], before, out);
    return true;
  }

  private static boolean intersects(int[] s, int[] t) {
    int i = 0;
    int j = 0;
    while (i < s.length && j < t.length) {
      if (s[i] == t[j]) {
        return true;
      }
      if (s[i] < t[j]) {
        i++;
      } else {
        j++;
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    byte kind = failKind;
    failKind = 0;
    int now = trail.size();
    switch (kind) {
      case FAIL_PAIR -> {
        if (trail.minBefore(x[failOption1], now) != 1
            || trail.minBefore(x[failOption2], now) != 1) {
          return false;
        }
        trail.addLowerBound(x[failOption1], now, out);
        trail.addLowerBound(x[failOption2], now, out);
        return true;
      }
      case FAIL_ELEMENT -> {
        for (int q : cover[failElement]) {
          if (!zeroBefore(trail, q, now, out)) {
            return false;
          }
        }
        return true;
      }
      case FAIL_INCLUSION -> {
        int p = failOption1;
        if (trail.minBefore(x[p], now) != 1) {
          return false;
        }
        trail.addLowerBound(x[p], now, out);
        return missing(trail, failElement, p, now, out);
      }
      default -> {
        return false;
      }
    }
  }

  @Override
  public boolean satisfied() {
    int[] covered = new int[cover.length];
    for (int o = 0; o < x.length; o++) {
      if (!x[o].singleton()) {
        return false;
      }
      if (x[o].value() == 1) {
        for (int e : sets[o]) {
          covered[e]++;
        }
      }
    }
    for (int c : covered) {
      if (c != 1) {
        return false;
      }
    }
    return true;
  }

  @Override
  public ExactCover copy(VarMap map) {
    IntVar[] copied = new IntVar[x.length];
    for (int o = 0; o < x.length; o++) {
      copied[o] = map.get(x[o]);
    }
    return new ExactCover(copied, sets, cover.length);
  }

  /**
   * It returns the elements of every option.
   *
   * @return a copy of the sets of the options
   */
  public List<int[]> sets() {
    List<int[]> result = new ArrayList<>();
    for (int[] s : sets) {
      result.add(s.clone());
    }
    return result;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : ExactCover([");
    for (int o = 0; o < x.length; o++) {
      if (o > 0) {
        result.append(", ");
      }
      result.append(x[o].id()).append(':').append(Arrays.toString(sets[o]));
    }
    result.append("], ").append(cover.length).append(')');
    return result.toString();
  }
}
