/*
 * Assignment.java
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

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.util.VarIntMap;

/**
 * Assignment constraint implements facility to improve channeling constraints between dual
 * viewpoints of permutation models. It enforces the relationship x[d[i]-shiftX]=i+shiftD and
 * d[x[i]-shiftD]=i+shiftX.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class Assignment extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent, Copyable<Assignment>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies a list of variables d. */
  private final IntVar[] d;

  /** It specifies a list of variables x. */
  private final IntVar[] x;

  /** It specifies a shift applied to variables d. */
  private final int shiftD;

  /** It specifies a shift applied to variables x. */
  private final int shiftX;

  final Map<IntVar, Integer> ds;
  final Map<IntVar, Integer> xs;

  /*
   * The changed variables, as slots of the distinct variables of xs and ds, in the order of their
   * first change: a round of consistency takes the variables queued so far (current) and the
   * changes it makes are queued for the next round, as with the LinkedHashSet swapped per round
   * that this replaces. queueVariable runs for every change of every variable, and hashing the
   * variable into a set and looking it up in xs and ds cost about a tenth of the time of the
   * constraint on black-hole; the order, and so the pruning and its explanations, is the same.
   */
  private final VarIntMap slotOf = new VarIntMap();

  private final IntVar[] slotVar;

  // the value of xs (and ds) for the variable of a slot, valid where inX (inD) is set
  private final int[] slotX;

  private final int[] slotD;

  private final boolean[] inX;

  private final boolean[] inD;

  private int[] queued;

  private int queuedSize;

  private final boolean[] isQueued;

  private int[] current;

  /** One-time work of the first consistency call. */
  final InitOnce init = new InitOnce();

  /**
   * The lowest level of the queued changes. The store may raise its level before consistency
   * (Store.raiseLevelBeforeConsistency, set by Alldistinct and others when imposed), so changes of
   * level l can reach the constraint first at level l + 1, where recentDomainPruning does not show
   * them; the domains are then scanned in full, as by the first consistency.
   */
  private int pendingLevel = Integer.MAX_VALUE;

  IntervalDomain rangeX;
  IntervalDomain rangeD;

  /**
   * It enforces the relationship x[d[i]-shiftX]=i+shiftD and d[x[i]-shiftD]=i+shiftX.
   *
   * @param xs array of variables x
   * @param ds array of variables d
   * @param shiftX a shift of indexes in X array.
   * @param shiftD a shift of indexes in D array.
   */
  public Assignment(IntVar[] xs, IntVar[] ds, int shiftX, int shiftD) {

    checkInputForNullness(new String[] {"xs", "ds"}, xs, ds);
    if (xs.length != ds.length) {
      throw new IllegalArgumentException(
          "Constraint Assignment has lists xs and ds of different lengths "
              + xs.length
              + " and "
              + ds.length
              + ".");
    }

    numberId = idNumber.incrementAndGet();

    this.shiftX = shiftX;
    this.shiftD = shiftD;
    this.x = Arrays.copyOf(xs, xs.length);
    this.d = Arrays.copyOf(ds, ds.length);
    this.queueIndex = 1;

    this.xs = Var.createEmptyPositioning();
    this.ds = Var.createEmptyPositioning();

    for (int i = 0; i < xs.length; i++) {
      this.xs.put(x[i], i + shiftX);
      this.ds.put(d[i], i + shiftD);
    }

    int slots = 0;
    IntVar[] vars = new IntVar[2 * x.length];
    for (IntVar v : Stream.concat(Arrays.stream(x), Arrays.stream(d)).toList()) {
      if (slotOf.get(v) == VarIntMap.ABSENT) {
        slotOf.put(v, slots);
        vars[slots++] = v;
      }
    }
    slotVar = Arrays.copyOf(vars, slots);
    slotX = new int[slots];
    slotD = new int[slots];
    inX = new boolean[slots];
    inD = new boolean[slots];
    for (int k = 0; k < slots; k++) {
      Integer px = this.xs.get(slotVar[k]);
      if (px != null) {
        inX[k] = true;
        slotX[k] = px;
      }
      Integer pd = this.ds.get(slotVar[k]);
      if (pd != null) {
        inD[k] = true;
        slotD[k] = pd;
      }
    }
    queued = new int[slots];
    current = new int[slots];
    isQueued = new boolean[slots];

    setScope(Stream.concat(Arrays.stream(xs), Arrays.stream(ds)));
  }

  /**
   * It enforces the relationship x[d[i]-shiftX]=i+shiftD and d[x[i]-shiftD]=i+shiftX.
   *
   * @param xs arraylist of variables x
   * @param ds arraylist of variables d
   * @param shiftX shift for parameter xs
   * @param shiftD shift for parameter ds
   */
  public Assignment(List<? extends IntVar> xs, List<? extends IntVar> ds, int shiftX, int shiftD) {
    this(xs.toArray(new IntVar[0]), ds.toArray(new IntVar[0]), shiftX, shiftD);
  }

  /**
   * It constructs an Assignment constraint with shift equal 0. It enforces relation - d[x[j]] = i
   * and x[d[i]] = j.
   *
   * @param xs arraylist of x variables
   * @param ds arraylist of d variables
   */
  public Assignment(List<? extends IntVar> xs, List<? extends IntVar> ds) {
    this(xs.toArray(new IntVar[0]), ds.toArray(new IntVar[0]), 0, 0);
  }

  /**
   * It constructs an Assignment constraint with shift equal 0. It enforces relation - d[x[i]] = i
   * and x[d[i]] = i.
   *
   * @param xs array of x variables
   * @param ds array of d variables
   */
  public Assignment(IntVar[] xs, IntVar[] ds) {
    this(xs, ds, 0, 0);
  }

  /**
   * It enforces the relationship x[d[i]-min]=i+min and d[x[i]-min]=i+min.
   *
   * @param xs array of variables x
   * @param ds array of variables d
   * @param min shift
   */
  public Assignment(IntVar[] xs, IntVar[] ds, int min) {
    this(xs, ds, min, min);
  }

  @Override
  public void removeLevel(int level) {
    clearQueue();
  }

  private void clearQueue() {
    for (int k = 0; k < queuedSize; k++) {
      isQueued[queued[k]] = false;
    }
    queuedSize = 0;
    pendingLevel = Integer.MAX_VALUE;
  }

  @Override
  public void consistency(Store store) {

    if (init.begin(store)) {
      initRangesAndPropagateInitial(store);
    } else if (pendingLevel < store.level) {
      pendingLevel = Integer.MAX_VALUE;
      propagateInitialFromX(store);
      propagateInitialFromD(store);
    }

    while (queuedSize > 0) {

      int[] round = queued;
      int roundSize = queuedSize;
      queued = current;
      current = round;
      for (int k = 0; k < roundSize; k++) {
        isQueued[round[k]] = false;
      }
      queuedSize = 0;

      for (int k = 0; k < roundSize; k++) {
        propagateFromPrunedVariable(store, round[k]);
      }
    }
    pendingLevel = Integer.MAX_VALUE;
  }

  private void initRangesAndPropagateInitial(Store store) {
    rangeX = new IntervalDomain(shiftX, x.length - 1 + shiftX);
    rangeD = new IntervalDomain(shiftD, x.length - 1 + shiftD);

    propagateInitialFromX(store);
    propagateInitialFromD(store);
  }

  private void propagateInitialFromX(Store store) {
    for (int i = 0; i < x.length; i++) {
      IntDomain alreadyRemoved = rangeD.subtract(x[i].domain);
      x[i].domain.in(store.level, x[i], shiftD, x.length - 1 + shiftD);
      propagateComplementFromRemoved(store, alreadyRemoved, i, true);
      if (x[i].singleton()) {
        int position = x[i].value() - shiftD;
        d[position].domain.in(store.level, d[position], i + shiftX, i + shiftX);
      }
    }
  }

  private void propagateInitialFromD(Store store) {
    for (int i = 0; i < d.length; i++) {
      IntDomain alreadyRemoved = rangeX.subtract(d[i].domain);
      d[i].domain.in(store.level, d[i], shiftX, x.length - 1 + shiftX);
      propagateComplementFromRemoved(store, alreadyRemoved, i, false);
      if (d[i].singleton()) {
        x[d[i].value() - shiftX].domain.in(
            store.level, x[d[i].value() - shiftX], i + shiftD, i + shiftD);
      }
    }
  }

  private void propagateComplementFromRemoved(
      Store store, IntDomain alreadyRemoved, int index, boolean fromX) {
    if (alreadyRemoved.isEmpty()) {
      return;
    }
    for (ValueEnumeration enumer = alreadyRemoved.valueEnumeration(); enumer.hasMoreElements(); ) {
      int value = enumer.nextElement();
      if (fromX) {
        d[value - shiftD].domain.inComplement(store.level, d[value - shiftD], index + shiftX);
      } else {
        x[value - shiftX].domain.inComplement(store.level, x[value - shiftX], index + shiftD);
      }
    }
  }

  private void propagateFromPrunedVariable(Store store, int slot) {
    IntVar v = slotVar[slot];
    IntDomain vPrunedDomain = v.recentDomainPruning();
    if (vPrunedDomain.isEmpty()) {
      return;
    }
    // a variable may occur in both xs and ds (e.g. inverse(x, x)); it is then propagated in both
    // roles
    if (inX[slot]) {
      propagateFromPruned(store, v, vPrunedDomain, slotX[slot], shiftD, d);
    }
    if (inD[slot]) {
      propagateFromPruned(store, v, vPrunedDomain, slotD[slot], shiftX, x);
    }
  }

  /**
   * Removes the position of v from the variables of the other list indexed by the values pruned
   * from v, and fixes the one indexed by v once v is fixed. The pruned values are intersected with
   * the index range of the other list first; when there is none inside it, nothing is done.
   */
  private static void propagateFromPruned(
      Store store, IntVar v, IntDomain pruned, int position, int shift, IntVar[] other) {
    int low = shift;
    int high = shift + other.length - 1;
    if (pruned.max() < low || pruned.min() > high) {
      return;
    }
    // narrowing an unbounded variable to the index range prunes about 10^9 values
    if (pruned.min() < low || pruned.max() > high) {
      pruned = pruned.intersect(low, high);
    }
    boolean any = false;
    for (ValueEnumeration enumer = pruned.valueEnumeration(); enumer.hasMoreElements(); ) {
      int index = enumer.nextElement() - shift;
      if (index >= 0 && index < other.length) {
        any = true;
        other[index].domain.inComplement(store.level, other[index], position);
      }
    }
    if (!any) {
      return;
    }
    if (v.singleton()) {
      other[v.value() - shift].domain.in(store.level, other[v.value() - shift], position, position);
    }
  }

  @Override
  public boolean satisfied() {

    if (!grounded()) {
      return false;
    }

    for (int i = 0; i < x.length; i++) {
      int position = x[i].value() - shiftD;
      if (d[position].value() != i + shiftX) {
        return false;
      }
    }

    for (int i = 0; i < d.length; i++) {
      if (x[d[i].value() - shiftX].value() != i + shiftD) {
        return false;
      }
    }

    return true;
  }

  // registers the constraint in the constraint store
  @Override
  public void impose(Store store) {

    super.impose(store);

    store.raiseLevelBeforeConsistency = true;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (level < pendingLevel) {
      pendingLevel = level;
    }
    int slot = slotOf.get(v);
    if (slot != VarIntMap.ABSENT && !isQueued[slot]) {
      isQueued[slot] = true;
      queued[queuedSize++] = slot;
    }
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : assignment([");

    for (int i = 0; i < x.length; i++) {
      result.append(x[i]);
      if (i < x.length - 1) {
        result.append(", ");
      }
    }
    result.append("], [");

    for (int i = 0; i < d.length; i++) {
      result.append(d[i]);
      if (i < d.length - 1) {
        result.append(", ");
      }
    }
    result.append("], ");
    result.append(shiftX).append(", ").append(shiftD).append(")");

    return result.toString();
  }

  /**
   * Explains an atom of a variable of xs or ds: each value it removes was out of the variable's
   * domain, is not an index of the other list, or the other list's variable at that index had
   * already lost this variable's index.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != Assignment.class) {
      return false;
    }
    IntVar v = trail.variable(entry);
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    int mark = out.size();
    Integer position = xs.get(v);
    if (position != null
        && removedSupported(trail, entry, v, position - shiftX, true, lo, hi, out)) {
      return true;
    }
    out.truncate(mark);
    position = ds.get(v);
    if (position != null
        && removedSupported(trail, entry, v, position - shiftD, false, lo, hi, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  /** Explains a failure: some variable of xs or ds has every value removed as for an atom. */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != Assignment.class) {
      return false;
    }
    int now = trail.size();
    int mark = out.size();
    for (int k = 0; k < 2 * x.length; k++) {
      boolean fromX = k < x.length;
      IntVar v = fromX ? x[k] : d[k - x.length];
      int index = fromX ? k : k - x.length;
      IntDomain root = trail.rootDomain(v);
      if (removedSupported(trail, now, v, index, fromX, root.min(), root.max(), out)) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  /**
   * Whether every value of v's root domain in [lo, hi] was removed before the position from v, in
   * its role at index of xs (fromX) or ds, or is ruled out by the other list; the entries that
   * removed them go to out.
   */
  private boolean removedSupported(
      AtomicTrail trail,
      int position,
      IntVar v,
      int index,
      boolean fromX,
      int lo,
      int hi,
      EntryList out) {
    int shiftOther = fromX ? shiftD : shiftX;
    int channel = index + (fromX ? shiftX : shiftD);
    IntVar[] other = fromX ? d : x;
    // values outside the other list's indexes are ruled out by the constraint alone
    lo = Math.max(lo, shiftOther);
    hi = Math.min(hi, other.length - 1 + shiftOther);
    int min = trail.minBefore(v, position);
    if (lo < min) {
      trail.addLowerBound(v, position, out);
      lo = min;
    }
    int max = trail.maxBefore(v, position);
    if (hi > max) {
      trail.addUpperBound(v, position, out);
      hi = max;
    }
    // a variable of the other list fixed to this index leaves v only its own index
    int forced = -1;
    for (int j = 0; j < other.length && forced < 0; j++) {
      if (trail.minBefore(other[j], position) == channel
          && trail.maxBefore(other[j], position) == channel) {
        forced = j;
      }
    }
    boolean forcedUsed = false;
    IntDomain root = trail.rootDomain(v);
    for (int w = lo; w <= hi; w++) {
      if (!root.contains(w) || trail.excludedBefore(v, w, position, out)) {
        continue;
      }
      if (forced >= 0 && w != forced + shiftOther) {
        forcedUsed = true;
      } else if (!trail.excludedBefore(other[w - shiftOther], channel, position, out)) {
        return false;
      }
    }
    if (forcedUsed) {
      trail.addLowerBound(other[forced], position, out);
      trail.addUpperBound(other[forced], position, out);
    }
    return true;
  }

  @Override
  public Assignment copy(VarMap map) {
    return new Assignment(map.get(x), map.get(d), shiftX, shiftD);
  }
}
