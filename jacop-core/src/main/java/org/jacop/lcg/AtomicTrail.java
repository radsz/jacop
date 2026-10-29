/*
 * AtomicTrail.java
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
import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.api.RemoveLevelLate;
import org.jacop.constraints.Constraint;
import org.jacop.core.BooleanVar;
import org.jacop.core.DomainChangeRecorder;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * The atomic trail of lazy clause generation: every change of an integer variable's domain,
 * recorded in order as atoms {@code [x >= v]}, {@code [x <= v]} and {@code [x != v]}, each with the
 * store level and the constraint that was propagating ({@link Store#currentConstraint}, null
 * outside propagation). Atoms describe changes from the domains at {@link #attach}: those domains
 * are facts that need no atom.
 *
 * <p>Each variable's entries form a chain, so the atoms that held for a variable at any trail
 * position can be found ({@link #atomsBefore}). That gives the generic reason of a propagation: the
 * atoms of the propagating constraint's variables just before it.
 *
 * <p>Entries above a removed level are dropped when the store backtracks.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class AtomicTrail implements DomainChangeRecorder, RemoveLevelLate {

  /** Atom kind {@code [x >= value]}. */
  public static final int GE = 0;

  /** Atom kind {@code [x <= value]}. */
  public static final int LE = 1;

  /** Atom kind {@code [x != value]}. */
  public static final int NE = 2;

  private final Store store;

  // entries
  private IntVar[] entryVar = new IntVar[256];
  private int[] kind = new int[256];
  private int[] value = new int[256];
  private int[] level = new int[256];
  private Constraint[] reason = new Constraint[256];
  private int[] previous = new int[256]; // the variable's previous entry, or -1
  private int size;

  // per variable (by id): the domain the entries so far describe, as its bounds and, when it has
  // holes, its runs; and the last entry
  private int[][] runs = new int[0][]; // the runs (first, last) of a domain with holes
  private int[] numRuns = new int[0]; // values in runs[i]: twice the runs, or 0 without holes
  private int[] shadowSize = new int[0];
  private IntVar removing; // the variable and value of the last removingValue call
  private int removingValue;
  private int[] shadowMin = new int[0];
  private int[] shadowMax = new int[0];
  private IntDomain[] root = new IntDomain[0]; // the domain when recording started
  private int[] last = new int[0];
  // the variable's GE entries (at 2 * id) and LE entries (at 2 * id + 1) in trail order, so that
  // the bound before a position is found by binary search instead of a walk along the chain
  private int[][] bounds = new int[0][];
  private int[] numBounds = new int[0];
  // the NE entry of each removed value, so that whether a value was removed before a position is
  // found without a walk along the variable's chain
  private final EntryIndex removals = new EntryIndex();

  // boolean variables, which have no store index, by the order they were first seen
  private final Map<IntVar, Integer> booleanIds = new IdentityHashMap<>();

  /**
   * Creates the trail and starts recording the changes of every integer variable of the store. The
   * current domains are the facts the atoms are relative to.
   *
   * @param store the store
   */
  public AtomicTrail(Store store) {
    this.store = store;
    for (int i = 0; i < store.size(); i++) {
      Var v = store.vars[i];
      if (v instanceof IntVar x) {
        slot(x);
      }
    }
    store.variablesHashMap.values().stream()
        .filter(BooleanVar.class::isInstance)
        .map(BooleanVar.class::cast)
        .sorted((a, b) -> a.id().compareTo(b.id()))
        .forEach(this::slot);
    store.domainChangeRecorder = this;
    store.registerRemoveLevelLateListener(this);
  }

  /**
   * Domains with more values than this keep only the bounds of a domain {@link #in} copies into
   * them while the changes are recorded; {@code -Djacop.lcg.holeLimit} changes it.
   */
  public static final int HOLE_LIMIT = Integer.getInteger("jacop.lcg.holeLimit", 10_000);

  /**
   * Intersects the domain of x with d, as {@code x.domain.in} does, but while a trail records the
   * changes and x has more than {@link #HOLE_LIMIT} values only with d's bounds. Every value
   * removed between the bounds is a {@code !=} atom with its own literals, so copying a sparse
   * domain into a large one (an equality between a variable of millions of values and one of a few)
   * would make millions of them. The weaker pruning is sound; the holes come once x is small
   * enough.
   *
   * @param store the store
   * @param x the variable
   * @param d the domain x is restricted to
   */
  public static void in(Store store, IntVar x, IntDomain d) {
    if (store.domainChangeRecorder != null && x.getSize() > HOLE_LIMIT) {
      x.domain.in(store.level, x, d.min(), d.max());
    } else {
      x.domain.in(store.level, x, d);
    }
  }

  /** Stops recording. */
  public void detach() {
    store.domainChangeRecorder = null;
    store.removeLevelLateListeners.remove(this);
  }

  /**
   * Returns the number by which this trail knows a variable: twice its store index, or for a {@link
   * BooleanVar}, which has no store index, an odd number given when the trail first sees it.
   *
   * @param x the variable
   * @return its number, at least 0
   */
  public int id(IntVar x) {
    int i = x.index();
    if (i >= 0) {
      return 2 * i;
    }
    if (x instanceof BooleanVar b) {
      if (b.trailOwner != this) {
        b.trailId = 2 * booleanIds.computeIfAbsent(x, v -> booleanIds.size()) + 1;
        b.trailOwner = this;
      }
      return b.trailId;
    }
    return 2 * booleanIds.computeIfAbsent(x, v -> booleanIds.size()) + 1;
  }

  private int slot(IntVar x) {
    int i = id(x);
    if (i >= numRuns.length) {
      int n = Math.max(i + 1, 2 * numRuns.length);
      int old = numRuns.length;
      runs = Arrays.copyOf(runs, n);
      numRuns = Arrays.copyOf(numRuns, n);
      shadowSize = Arrays.copyOf(shadowSize, n);
      shadowMin = Arrays.copyOf(shadowMin, n);
      shadowMax = Arrays.copyOf(shadowMax, n);
      root = Arrays.copyOf(root, n);
      last = Arrays.copyOf(last, n);
      Arrays.fill(last, old, n, -1);
      bounds = Arrays.copyOf(bounds, 2 * n);
      numBounds = Arrays.copyOf(numBounds, 2 * n);
    }
    if (root[i] == null) {
      root[i] = x.dom().cloneLight();
      setShadow(i, root[i]);
    }
    return i;
  }

  // copies a domain into the shadow: its bounds, and its runs when it has holes
  private void setShadow(int i, IntDomain d) {
    int min = d.min();
    int max = d.max();
    shadowMin[i] = min;
    shadowMax[i] = max;
    shadowSize[i] = d.getSize();
    if (d.getSize() == (long) max - min + 1) {
      numRuns[i] = 0;
      return;
    }
    int[] r = runs[i] == null ? new int[16] : runs[i];
    int n = 0;
    for (int v = min; ; ) {
      int end = d.runEnd(v);
      if (n + 2 > r.length) {
        r = Arrays.copyOf(r, 2 * r.length);
      }
      r[n++] = v;
      r[n++] = end;
      if (end >= max) {
        break;
      }
      v = d.nextValue(end);
    }
    runs[i] = r;
    numRuns[i] = n;
  }

  @Override
  public void removingValue(IntVar x, int value) {
    removing = x;
    removingValue = value;
  }

  @Override
  public void domainChanged(IntVar x, int event) {
    int i = slot(x);
    IntDomain now = x.dom();
    int min = now.min();
    int max = now.max();
    if (x == removing) {
      removing = null;
      if (min == shadowMin[i]
          && max == shadowMax[i]
          && now.getSize() == shadowSize[i] - 1
          && !now.contains(removingValue)
          && removeFromShadow(i, removingValue)) {
        add(x, i, NE, removingValue);
        return;
      }
    }
    if (min > shadowMin[i]) {
      add(x, i, GE, min);
    }
    if (max < shadowMax[i]) {
      add(x, i, LE, max);
    }
    if (now.getSize() < (long) max - min + 1) {
      int n = numRuns[i];
      if (n == 0) {
        // every value of [min, max] was in the domain
        addHoles(x, i, now, min, max);
      } else {
        int[] r = runs[i];
        int k = 0;
        while (r[k + 1] < min) {
          k += 2;
        }
        for (; k < n && r[k] <= max; k += 2) {
          addHoles(x, i, now, Math.max(r[k], min), Math.min(r[k + 1], max));
        }
      }
    }
    setShadow(i, now);
  }

  /**
   * Removes an inner value from a shadow without rebuilding it; false when the value is not in the
   * shadow. The bounds stay.
   */
  private boolean removeFromShadow(int i, int v) {
    if (v <= shadowMin[i] || v >= shadowMax[i]) {
      return false;
    }
    int n = numRuns[i];
    int[] r = runs[i];
    int k;
    if (n == 0) {
      if (r == null) {
        r = new int[16];
        runs[i] = r;
      }
      r[0] = shadowMin[i];
      r[1] = shadowMax[i];
      n = 2;
      k = 0;
    } else {
      int lo = 0;
      int hi = n / 2 - 1; // the run containing v, by binary search over first values
      while (lo < hi) {
        int mid = (lo + hi + 1) >>> 1;
        if (r[2 * mid] <= v) {
          lo = mid;
        } else {
          hi = mid - 1;
        }
      }
      k = 2 * lo;
      if (v < r[k] || v > r[k + 1]) {
        return false;
      }
    }
    if (r[k] == v && r[k + 1] == v) {
      System.arraycopy(r, k + 2, r, k, n - k - 2);
      n -= 2;
    } else if (r[k] == v) {
      r[k] = v + 1;
    } else if (r[k + 1] == v) {
      r[k + 1] = v - 1;
    } else {
      if (n + 2 > r.length) {
        r = Arrays.copyOf(r, 2 * r.length);
        runs[i] = r;
      }
      System.arraycopy(r, k + 2, r, k + 4, n - k - 2);
      r[k + 2] = v + 1;
      r[k + 3] = r[k + 1];
      r[k + 1] = v - 1;
      n += 2;
    }
    numRuns[i] = n;
    shadowSize[i]--;
    return true;
  }

  // adds an entry for each value of [lo, hi], all in the domain before, that is not in it now
  private void addHoles(IntVar x, int i, IntDomain now, int lo, int hi) {
    if (now.contains(lo, hi)) {
      return;
    }
    for (int u = lo; u <= hi; ) {
      if (now.contains(u)) {
        u = now.runEnd(u) + 1;
      } else {
        int next = now.nextValue(u);
        int end = next > u ? Math.min(next - 1, hi) : hi;
        for (; u <= end; u++) {
          add(x, i, NE, u);
        }
      }
    }
  }

  private void add(IntVar x, int i, int k, int v) {
    if (size == entryVar.length) {
      int n = 2 * size;
      entryVar = Arrays.copyOf(entryVar, n);
      kind = Arrays.copyOf(kind, n);
      value = Arrays.copyOf(value, n);
      level = Arrays.copyOf(level, n);
      reason = Arrays.copyOf(reason, n);
      previous = Arrays.copyOf(previous, n);
    }
    entryVar[size] = x;
    kind[size] = k;
    value[size] = v;
    level[size] = store.level;
    reason[size] = store.currentConstraint;
    previous[size] = last[i];
    last[i] = size;
    if (k == NE) {
      removals.put(i, v, size);
    } else {
      int b = 2 * i + k;
      if (bounds[b] == null) {
        bounds[b] = new int[8];
      } else if (numBounds[b] == bounds[b].length) {
        bounds[b] = Arrays.copyOf(bounds[b], 2 * numBounds[b]);
      }
      bounds[b][numBounds[b]++] = size;
    }
    size++;
  }

  @Override
  public void removeLevelLate(int removedLevel) {
    while (size > 0 && level[size - 1] >= removedLevel) {
      size--;
      IntVar x = entryVar[size];
      int i = id(x);
      last[i] = previous[size];
      if (kind[size] != NE) {
        numBounds[2 * i + kind[size]]--;
      } else {
        removals.remove(i, value[size]);
      }
      if (last[i] < 0 || level[last[i]] < removedLevel) {
        setShadow(i, x.dom()); // the variable's last removed entry: its domain is restored
      }
      entryVar[size] = null;
      reason[size] = null;
    }
  }

  /**
   * Returns the number of entries.
   *
   * @return the trail size
   */
  public int size() {
    return size;
  }

  /**
   * Returns the variable of an entry.
   *
   * @param entry the entry
   * @return its variable
   */
  public IntVar variable(int entry) {
    return entryVar[entry];
  }

  /**
   * Returns the kind of an entry's atom: {@link #GE}, {@link #LE} or {@link #NE}.
   *
   * @param entry the entry
   * @return its kind
   */
  public int kind(int entry) {
    return kind[entry];
  }

  /**
   * Returns the smallest value an entry's atom removes, within its variable's root bounds: the root
   * minimum for {@link #GE}, the atom's value + 1 for {@link #LE} and the value for {@link #NE}.
   *
   * @param entry the entry
   * @return the smallest removed value
   */
  public int removedMin(int entry) {
    return switch (kind[entry]) {
      case GE -> rootDomain(variable(entry)).min();
      case LE -> value[entry] + 1;
      default -> value[entry];
    };
  }

  /**
   * Returns the largest value an entry's atom removes, within its variable's root bounds: the
   * atom's value - 1 for {@link #GE}, the root maximum for {@link #LE} and the value for {@link
   * #NE}.
   *
   * @param entry the entry
   * @return the largest removed value
   */
  public int removedMax(int entry) {
    return switch (kind[entry]) {
      case GE -> value[entry] - 1;
      case LE -> rootDomain(variable(entry)).max();
      default -> value[entry];
    };
  }

  /**
   * Returns the value of an entry's atom.
   *
   * @param entry the entry
   * @return its value
   */
  public int value(int entry) {
    return value[entry];
  }

  /**
   * Returns the store level at which an entry was recorded.
   *
   * @param entry the entry
   * @return its level
   */
  public int level(int entry) {
    return level[entry];
  }

  /**
   * Returns the constraint that was propagating when an entry was recorded.
   *
   * @param entry the entry
   * @return the constraint, or null outside propagation (a decision, or a change made by search)
   */
  public Constraint reason(int entry) {
    return reason[entry];
  }

  /**
   * Returns a variable's last entry before a trail position. With {@link #previousEntry} it walks
   * the variable's entries from the latest to the earliest.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @return the entry, or -1 when the variable has none before the position
   */
  public int lastEntry(IntVar x, int position) {
    return lastBefore(x, position);
  }

  /**
   * Returns the entry of the same variable recorded before an entry.
   *
   * @param entry the entry
   * @return the variable's previous entry, or -1 when there is none
   */
  public int previousEntry(int entry) {
    return previous[entry];
  }

  private int lastBefore(IntVar x, int position) {
    int i = id(x);
    if (i >= last.length) {
      return -1;
    }
    int e = last[i];
    while (e >= position) {
      e = previous[e];
    }
    return e;
  }

  private int latest(IntVar x, int position, int k) {
    if (k != NE) {
      int b = 2 * id(x) + k;
      if (b >= numBounds.length) {
        return -1;
      }
      // the last of the variable's k entries before the position
      int[] list = bounds[b];
      int lo = 0;
      int hi = numBounds[b] - 1;
      while (lo <= hi) {
        int mid = (lo + hi) >>> 1;
        if (list[mid] < position) {
          lo = mid + 1;
        } else {
          hi = mid - 1;
        }
      }
      return hi >= 0 ? list[hi] : -1;
    }
    int e = lastBefore(x, position);
    while (e >= 0 && kind[e] != k) {
      e = previous[e];
    }
    return e;
  }

  /**
   * Returns a variable's domain when the trail started recording it: the facts its atoms are
   * relative to.
   *
   * @param x the variable
   * @return its initial domain, which must not be changed
   */
  public IntDomain rootDomain(IntVar x) {
    return root[slot(x)];
  }

  /**
   * Adds to {@code out} the entry of a variable's lower bound just before trail position {@code
   * position}, unless that bound is the initial one.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param out where the entry is added
   */
  public void addLowerBound(IntVar x, int position, EntryList out) {
    int e = latest(x, position, GE);
    if (e >= 0) {
      out.add(e);
    }
  }

  /**
   * Adds to {@code out} the entry of a variable's upper bound just before trail position {@code
   * position}, unless that bound is the initial one.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param out where the entry is added
   */
  public void addUpperBound(IntVar x, int position, EntryList out) {
    int e = latest(x, position, LE);
    if (e >= 0) {
      out.add(e);
    }
  }

  /**
   * Adds to {@code out} the earliest entry of a variable's bound before trail position {@code
   * position} that still reaches {@code limit} (a lower bound of at least it, or an upper bound of
   * at most it), unless the initial bound already does: the weakest atom on the trail that serves.
   * Explanations weaken bounds this way where the propagation leaves slack (lifting).
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param lower whether it is the lower bound, else the upper bound
   * @param limit the weakest bound that serves; the bound just before the position reaches it
   * @param out where the entry is added
   * @return the bound added, or the initial bound
   */
  public int addBoundReaching(IntVar x, int position, boolean lower, long limit, EntryList out) {
    int e = latest(x, position, lower ? GE : LE);
    return addWeakest(x, e, lower, limit, out);
  }

  /**
   * Adds to {@code out} the earliest entry of a variable's bound before trail position {@code
   * position} that is at most {@code room} weaker than the bound just before it, as {@link
   * #addBoundReaching} does with the limit that far from the current bound.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param lower whether it is the lower bound, else the upper bound
   * @param room how much weaker the cited bound may be, at least 0
   * @param out where the entry is added
   * @return how much weaker the cited bound (or the initial one) is than the current bound
   */
  public long addBoundWithin(IntVar x, int position, boolean lower, long room, EntryList out) {
    int e = latest(x, position, lower ? GE : LE);
    int now = e >= 0 ? value[e] : lower ? root[slot(x)].min() : root[slot(x)].max();
    int used = addWeakest(x, e, lower, lower ? now - room : now + room, out);
    return Math.abs((long) now - used);
  }

  // lifted reasons: bounds weakened as far as the propagation allows, unless -Djacop.lcg.lift=false
  private static final boolean LIFTING = !"false".equals(System.getProperty("jacop.lcg.lift"));

  // whether reasons are lifted, so an explanation may leave out a bound the slack covers
  static boolean lifting() {
    return LIFTING;
  }

  // adds the earliest entry of e's kind, from e back, that still reaches limit; e < 0 for none
  private int addWeakest(IntVar x, int e, boolean lower, long limit, EntryList out) {
    int rootBound = lower ? root[slot(x)].min() : root[slot(x)].max();
    if (e < 0) {
      return rootBound;
    }
    if (!LIFTING) {
      out.add(e);
      return value[e];
    }
    if (lower ? rootBound >= limit : rootBound <= limit) {
      return rootBound;
    }
    int k = kind[e];
    for (int f = previous[e]; f >= 0; f = previous[f]) {
      if (kind[f] == k) {
        if (lower ? value[f] < limit : value[f] > limit) {
          break;
        }
        e = f;
      }
    }
    out.add(e);
    return value[e];
  }

  /**
   * Returns a variable's minimum just before a trail position.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @return its minimum then
   */
  public int minBefore(IntVar x, int position) {
    int e = latest(x, position, GE);
    return e >= 0 ? value[e] : root[slot(x)].min();
  }

  /**
   * Returns a variable's maximum just before a trail position.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @return its maximum then
   */
  public int maxBefore(IntVar x, int position) {
    int e = latest(x, position, LE);
    return e >= 0 ? value[e] : root[slot(x)].max();
  }

  /**
   * Returns the earliest entry whose atom gives {@code x >= v} just before a trail position: the
   * weakest {@code >=} atom recorded for x that implies the bound, so a reason built on it is as
   * general and as early as it can be with the atoms on the trail.
   *
   * @param x the variable
   * @param v the bound
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @return the entry, -1 when the initial domain gives the bound, or {@link Integer#MAX_VALUE}
   *     when x could be below v then
   */
  public int earliestLowerBound(IntVar x, long v, int position) {
    return earliest(x, v, position, GE);
  }

  /**
   * Returns the earliest entry whose atom gives {@code x <= v} just before a trail position: the
   * weakest {@code <=} atom recorded for x that implies the bound.
   *
   * @param x the variable
   * @param v the bound
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @return the entry, -1 when the initial domain gives the bound, or {@link Integer#MAX_VALUE}
   *     when x could be above v then
   */
  public int earliestUpperBound(IntVar x, long v, int position) {
    return earliest(x, v, position, LE);
  }

  // the bounds of one kind only tighten along a variable's chain
  private int earliest(IntVar x, long v, int position, int k) {
    IntDomain d = root[slot(x)];
    if (k == GE ? d.min() >= v : d.max() <= v) {
      return -1;
    }
    int found = Integer.MAX_VALUE;
    for (int e = latest(x, position, k); e >= 0; e = previous[e]) {
      if (kind[e] != k) {
        continue;
      }
      if (k == GE ? value[e] < v : value[e] > v) {
        break;
      }
      found = e;
    }
    return found;
  }

  /**
   * Tells whether a value was out of a variable's domain just before a trail position, and if so
   * adds to {@code out} the entry that removed it (none when the value was never in the domain
   * recording started from).
   *
   * @param x the variable
   * @param v the value
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param out where the entry is added
   * @return true when v was not in the domain
   */
  public boolean excludedBefore(IntVar x, int v, int position, EntryList out) {
    int i = slot(x);
    if (!root[i].contains(v)) {
      return true;
    }
    // the latest entry before the position that removes v: the value's NE entry, or the last bound
    // of either kind, which removes v when any bound of its kind before it does
    int f = removals.get(i, v);
    int found = f < position ? f : -1;
    int g = latest(x, position, GE);
    if (g > found && value[g] > v) {
      found = g;
    }
    int l = latest(x, position, LE);
    if (l > found && value[l] < v) {
      found = l;
    }
    if (found < 0) {
      return false;
    }
    out.add(found);
    return true;
  }

  /**
   * Adds to {@code out} the {@code !=} atoms that a bound entry skipped: the holes of its variable,
   * recorded before it, between the bound a propagator computed and the bound the domain moved to.
   * A propagator that prunes a bound by {@code inMin} or {@code inMax} implies only the computed
   * bound, so its explanation adds these to reach the recorded one.
   *
   * @param entry a {@link #GE} or {@link #LE} entry
   * @param bound the bound the propagator computed: at most the value of a {@link #GE} entry, at
   *     least the value of a {@link #LE} entry; when it is not known, {@link Integer#MIN_VALUE} or
   *     {@link Integer#MAX_VALUE} adds the holes next to the recorded bound, up to the value
   *     nearest to it that was still in the domain: the entry removed that value, so the computed
   *     bound was past it
   * @param out where the entries are added
   */
  public void addSkippedHoles(int entry, int bound, EntryList out) {
    int v = value[entry];
    boolean ge = kind[entry] == GE;
    if (bound == (ge ? Integer.MIN_VALUE : Integer.MAX_VALUE)) {
      // the holes are inside the bounds before the entry, so each is a != entry of its own
      int lo = minBefore(entryVar[entry], entry);
      int hi = maxBefore(entryVar[entry], entry);
      for (int u = ge ? v - 1 : v + 1; u > lo && u < hi; u += ge ? -1 : 1) {
        if (!excludedBefore(entryVar[entry], u, entry, out)) {
          return;
        }
      }
      return;
    }
    for (int f = previous[entry]; f >= 0; f = previous[f]) {
      if (kind[f] == NE
          && (ge ? value[f] >= bound && value[f] < v : value[f] <= bound && value[f] > v)) {
        out.add(f);
      }
    }
  }

  /**
   * Adds to {@code out} the entries that describe a variable's domain just before trail position
   * {@code position}: its strongest {@code >=} and {@code <=} atoms and its {@code !=} atoms inside
   * those bounds. Each such entry is the latest of its atom.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param out where the entries are added
   */
  public void atomsBefore(IntVar x, int position, EntryList out) {
    int ge = latest(x, position, GE);
    int le = latest(x, position, LE);
    int lo = ge >= 0 ? value[ge] : Integer.MIN_VALUE;
    int hi = le >= 0 ? value[le] : Integer.MAX_VALUE;
    if (ge >= 0) {
      out.add(ge);
    }
    if (le >= 0) {
      out.add(le);
    }
    for (int f = lastBefore(x, position); f >= 0; f = previous[f]) {
      if (kind[f] == NE && value[f] > lo && value[f] < hi) {
        out.add(f);
      }
    }
  }

  /**
   * Adds to {@code out} the reason of an entry: the constraint's own explanation when it is {@link
   * Explainable} and gives one, otherwise the generic reason.
   *
   * @param entry the entry, which must have a constraint as reason
   * @param out where the entries are added
   * @return true when the constraint explained it, false for the generic reason
   */
  public boolean explain(int entry, EntryList out) {
    int mark = out.size();
    replayed = false;
    if (reason[entry] instanceof Explainable c && c.explain(this, entry, out)) {
      return true;
    }
    out.truncate(mark);
    if (replay(reason[entry], entry, out)) {
      return true;
    }
    out.truncate(mark);
    genericReason(entry, out);
    return false;
  }

  /**
   * Whether the last {@link #explain} or {@link #explainFailure} that gave an explanation of the
   * constraint's own found it by replaying the constraint ({@link ReplayExplanation}) rather than
   * by the constraint's explanation.
   *
   * @return true for a replayed explanation
   */
  public boolean replayed() {
    return replayed;
  }

  private boolean replayed;

  // the replay of each constraint asked for one, or null when it cannot be replayed
  private final Map<Constraint, ReplayExplanation> replays = new IdentityHashMap<>();

  private boolean replay(Constraint c, int entry, EntryList out) {
    if (!ReplayExplanation.ENABLED || c == null) {
      return false;
    }
    long now = System.nanoTime();
    if (replayStart == 0) {
      replayStart = now;
    }
    if (replayNanos > ReplayExplanation.SHARE * (now - replayStart) + REPLAY_GRACE) {
      return false;
    }
    ReplayExplanation r = replays.computeIfAbsent(c, k -> ReplayExplanation.of(this, k));
    replayed = r != null && r.explain(entry, out, now - replayStart);
    replayNanos += System.nanoTime() - now;
    return replayed;
  }

  // the time spent replaying, and when the first replay started
  private long replayNanos;
  private long replayStart;

  // replaying may take this long before its share of the time applies
  private static final long REPLAY_GRACE = 200_000_000L;

  /**
   * Adds to {@code out} the reason of a failure of a constraint now: its own explanation when it is
   * {@link Explainable} and gives one, otherwise the atoms of all its variables.
   *
   * @param failed the constraint that failed
   * @param out where the entries are added
   * @return true when the constraint explained it, false for the generic reason
   */
  public boolean explainFailure(Constraint failed, EntryList out) {
    int mark = out.size();
    replayed = false;
    if (failed instanceof Explainable c && c.explainFailure(this, out)) {
      return true;
    }
    out.truncate(mark);
    if (replay(failed, -1, out)) {
      return true;
    }
    out.truncate(mark);
    for (Var v : failed.arguments()) {
      atomsBefore(v, size, out);
    }
    return false;
  }

  /**
   * Adds to {@code out} the generic reason of an entry: the atoms of every variable of its
   * constraint just before it. It is valid for any propagator whose pruning depends only on the
   * current domains of its variables.
   *
   * @param entry the entry, which must have a constraint as reason
   * @param out where the entries are added
   */
  public void genericReason(int entry, EntryList out) {
    Constraint c = reason[entry];
    for (Var v : c.arguments()) {
      atomsBefore(v, entry, out);
    }
  }

  /**
   * Adds to {@code out} the entries that describe a variable's domain just before a trail position:
   * those of an integer variable, or of the integer variables mirroring a {@link Mirrored} one.
   * Other variables have none.
   *
   * @param v the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param out where the entries are added
   */
  public void atomsBefore(Var v, int position, EntryList out) {
    if (v instanceof IntVar x) {
      atomsBefore(x, position, out);
    } else if (v instanceof Mirrored m && m.mirror() != null) {
      for (IntVar x : m.mirror()) {
        atomsBefore(x, position, out);
      }
    }
  }

  /**
   * Returns a readable form of an entry's atom.
   *
   * @param entry the entry
   * @return for example {@code [x >= 3]}
   */
  public String atomString(int entry) {
    String op =
        switch (kind[entry]) {
          case GE -> ">=";
          case LE -> "<=";
          default -> "!=";
        };
    return "[" + entryVar[entry].id() + " " + op + " " + value[entry] + "]";
  }
}
