/*
 * ElementVariableFast.java
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
import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.ToIntFunction;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.Functional;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.SelectingViolation;
import org.jacop.api.Simplifiable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.ElementVariableExplanation;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * ElementVariableFast constraint defines a relation list[index - indexOffset] = value. This version
 * uses bounds consistency.
 *
 * <p>The first element of the list corresponds to index - indexOffset = 1. By default indexOffset
 * is equal 0 so first value within a list corresponds to index equal 1.
 *
 * <p>If index has a domain from 0 to list.length-1 then indexOffset has to be equal -1 to make
 * addressing of list array starting from 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ElementVariableFast extends AbstractElement
    implements Functional,
        SelectingViolation,
        Simplifiable,
        SatisfiedPresent,
        Copyable<ElementVariableFast>,
        Explainable,
        PbEncodable {

  /** Whether a fixed index rewrites the constraint to an equality (org.jacop.rewrite.element). */
  static final boolean REWRITE_FIXED_INDEX =
      Boolean.parseBoolean(System.getProperty("org.jacop.rewrite.element", "true"));

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The most values of the list variables and the value an encoding enumerates. */
  private static final int ENCODED_VALUES = 1 << 18;

  /** It specifies variable value within an element constraint list[index - indexOffset] = value. */
  private final IntVar value;

  /**
   * It specifies list of variables within an element constraint list[index - indexOffset] = value.
   * The list is addressed by positive integers ({@code >=1}) if indexOffset is equal to 0.
   */
  private final IntVar[] list;

  /**
   * A value that list[p] and the value shared when position p was last checked (residual support,
   * Lecoutre and Hemery, IJCAI 2007), or {@link #NO_SUPPORT}. It is only a hint, checked again at
   * every use, so it is not trailed. On XCSP3 RollerSplat, 160 element constraints over one list of
   * 71 plan variables spent most of their time intersecting the domains of every selectable
   * position, although the same common value nearly always remained.
   */
  private final int[] residue;

  /** No common value is known for the position. */
  private static final int NO_SUPPORT = Integer.MIN_VALUE;

  /**
   * The store indices of the list variables that are neither the index nor the value, sorted, made
   * at the first wake; {@link #wakePositions} holds their positions in the same order. {@link
   * #queueVariable} finds a changed variable there by binary search, without hashing it (identity
   * hash codes would change the search order of other parts).
   */
  private int[] wakeKeys;

  private int[] wakePositions;

  /**
   * For store indexes that span few values, the first entry of {@link #wakeKeys} with key {@code
   * wakeBase + d} at {@code wakeFirst[d]}, or -1: a wake then finds its positions without a binary
   * search. On MiniZinc Challenge multi-agent-graph-coverage 1086 elements share two lists of 543
   * variables, so each change of a variable wakes 543 elements, and their binary searches took 16 %
   * of the solving time.
   */
  private int[] wakeFirst;

  private int wakeBase;

  /** No wake since the last consistency call: the call was queued for another reason. */
  private static final int WAKE_NONE = 0;

  /** Only list variables at positions the index can no longer select changed. */
  private static final int WAKE_IDLE = 1;

  /** List variables changed, the selectable positions among them are in {@link #changed}. */
  private static final int WAKE_LIST = 2;

  /** The index or the value changed, or too many positions to list. */
  private static final int WAKE_FULL = 3;

  /** Selectable changed positions a wake of {@link #WAKE_LIST} lists. */
  private static final int CHANGED_CAP = 16;

  /**
   * The wakes since the last consistency call, the largest of the WAKE_ constants. Not trailed: a
   * wake lost to a failure leaves it larger than needed, which costs one more full call, since
   * every change of a domain after the last call is reported by a wake.
   *
   * <p>On XCSP 2026 TelecomScheduling the lists are an agent's teams on every day (x[agent][day])
   * and each task selects the day of every agent: a change of one team woke every element of that
   * agent, and each scanned the whole index domain of 100-200 days, 85 % of the solving time. A
   * wake from a position the index cannot select changes nothing, and one from a few selectable
   * positions changes nothing when those positions keep a common value with the value and the
   * value's bounds and values keep their supports ({@link #listChangeKeepsFixpoint}).
   */
  private int wake;

  /**
   * The selectable positions of the list variables that woke the constraint since its last call.
   */
  private final int[] changed = new int[CHANGED_CAP];

  private int changedCount;

  /** A position whose minimum supported the value's minimum at the last full call, or -1. */
  private int minSupport = -1;

  /** A position whose maximum supported the value's maximum at the last full call, or -1. */
  private int maxSupport = -1;

  /**
   * For a value of the value of at most 64 values, a position whose variable had it, at index value
   * - {@link #valueSupportBase}, or -1; residues checked again at every use.
   */
  private int[] valueSupport;

  private int valueSupportBase;

  /**
   * For each position, the values (as bits from {@link #valueSupportBase}) whose residue in {@link
   * #valueSupport} may be that position; a superset, so a change of the position rechecks them.
   */
  private long[] supportsOf;

  /** The values (as bits from {@link #valueSupportBase}) that have a residue. */
  private long coveredValues;

  /** A selectable position whose variable is not fixed to the fixed value, or -1; a residue. */
  private int openPosition = -1;

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   */
  public ElementVariableFast(IntVar index, IntVar[] list, IntVar value, int indexOffset) {

    super(index, indexOffset);
    checkInputForNullness(new String[] {"index", "value"}, new Object[] {index, value});
    checkInputForNullness("list", list);

    queueIndex = 1;

    this.numberId = idNumber.incrementAndGet();
    this.value = value;
    this.list = Arrays.copyOf(list, list.length);
    this.residue = new int[list.length];
    Arrays.fill(residue, NO_SUPPORT);

    setScope(Stream.concat(Stream.concat(Stream.of(index), Arrays.stream(list)), Stream.of(value)));
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   */
  public ElementVariableFast(IntVar index, List<? extends IntVar> list, IntVar value) {

    this(index, list.toArray(new IntVar[0]), value, 0);
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   */
  public ElementVariableFast(
      IntVar index, List<? extends IntVar> list, IntVar value, int indexOffset) {

    this(index, list.toArray(new IntVar[0]), value, indexOffset);
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   */
  public ElementVariableFast(IntVar index, IntVar[] list, IntVar value) {

    this(index, list, value, 0);
  }

  /**
   * Returns the variable that equals the list variable the index selects.
   *
   * @return the value variable.
   */
  public IntVar value() {
    return value;
  }

  /**
   * Returns a copy of the list variables; index - indexOffset = 1 selects the first one.
   *
   * @return the list.
   */
  public IntVar[] variables() {
    return list.clone();
  }

  @Override
  protected int listLength() {
    return list.length;
  }

  @Override
  public void impose(Store store) {
    imposeInit(store);
  }

  @Override
  public void queueVariable(int level, Var var) {
    if (wake == WAKE_FULL) {
      return;
    }
    if (var == index || var == value) {
      wake = WAKE_FULL;
      return;
    }
    if (wakeKeys == null) {
      indexWakePositions();
    }
    int key = var.index();
    int k;
    if (wakeFirst != null) {
      int d = key - wakeBase;
      k = d >= 0 && d < wakeFirst.length ? wakeFirst[d] : -1;
    } else {
      k = Arrays.binarySearch(wakeKeys, key);
      while (k > 0 && wakeKeys[k - 1] == key) {
        k--;
      }
    }
    if (k < 0) {
      wake = WAKE_FULL;
      return;
    }
    int kind = WAKE_IDLE;
    for (; k < wakeKeys.length && wakeKeys[k] == key; k++) {
      int p = wakePositions[k];
      if (index.domain.contains(p + 1 + indexOffset)) {
        if (changedCount == CHANGED_CAP) {
          wake = WAKE_FULL;
          return;
        }
        changed[changedCount++] = p;
        kind = WAKE_LIST;
      }
    }
    wake = Math.max(wake, kind);
  }

  /**
   * A change of list variables only at positions the index cannot select ({@code WAKE_IDLE}) is not
   * queued. In the giant-tour model of CVRP (MiniZinc Challenge 2015) each arrival time, load and
   * vehicle variable is in the list of about 330 elements {@code a[successor[i]]}, and once the
   * successors are fixed nearly all of them are idle for any change.
   */
  @Override
  public boolean wakeNeeded() {
    return wake != WAKE_IDLE;
  }

  private void indexWakePositions() {
    long[] packed = new long[list.length];
    int n = 0;
    for (int p = 0; p < list.length; p++) {
      IntVar x = list[p];
      if (x != index && x != value) {
        packed[n++] = ((long) x.index() << 32) | p;
      }
    }
    Arrays.sort(packed, 0, n);
    int[] keys = new int[n];
    int[] at = new int[n];
    for (int k = 0; k < n; k++) {
      keys[k] = (int) (packed[k] >> 32);
      at[k] = (int) packed[k];
    }
    wakePositions = at;
    wakeKeys = keys;
    if (n > 0 && keys[0] >= 0 && (long) keys[n - 1] - keys[0] < 4L * n + 64) {
      int[] first = new int[keys[n - 1] - keys[0] + 1];
      Arrays.fill(first, -1);
      for (int k = n - 1; k >= 0; k--) {
        first[keys[k] - keys[0]] = k;
      }
      wakeBase = keys[0];
      wakeFirst = first;
    }
  }

  /**
   * Whether the last call's pruning still holds after the list variables at the first n positions
   * of {@link #changed} changed and nothing else did: each of those positions still shares a value
   * with the value, and the value's bounds and, for a value of at most 64 values, each of its
   * values keeps a selectable supporting position. When it does not, the full scan prunes; this
   * only spares the scan when it would prune nothing, without its entailment test.
   */
  private boolean listChangeKeepsFixpoint(int n) {
    for (int k = 0; k < n; k++) {
      int p = changed[k];
      if (index.domain.contains(p + 1 + indexOffset) && !supported(p)) {
        return false;
      }
    }
    if (value.singleton()) {
      // every supported position has the value, so its bounds hold and it has no other values.
      // When no selectable position is left open, the full scan finds the constraint entailed and
      // removes it, which spares the later wakes: a residue keeps an open position
      int v = value.value();
      if (!open(openPosition, v)) {
        // the search goes on after the last open position, round to the start: the positions
        // before it are mostly the ones fixed since
        int from = Math.max(openPosition, 0) + 1 + indexOffset;
        openPosition = nextOpen(from, index.max(), v);
        if (openPosition < 0) {
          openPosition = nextOpen(index.min(), from - 1, v);
        }
        if (openPosition < 0) {
          return false;
        }
      }
      return true;
    }
    int min = value.min();
    int max = value.max();
    if (!keepsSupport(minSupport, min, true)) {
      int q = findSupport(min, true);
      if (q < 0) {
        return false;
      }
      minSupport = q;
    }
    if (!keepsSupport(maxSupport, max, false)) {
      int q = findSupport(max, false);
      if (q < 0) {
        return false;
      }
      maxSupport = q;
    }
    if ((long) max - min >= 64) {
      return true; // the full scan prunes only the bounds of a value of 64 values or more
    }
    if (valueSupport == null || min < valueSupportBase || (long) max - valueSupportBase >= 64) {
      return false;
    }
    // a residue stays valid until its position changes: the index did not change since the last
    // full call, which rebuilt the residues, and a position that changed since is in changed or
    // made that call full; after backtracking the domains are larger, so the residues still hold.
    // Only the values supported by a changed position and those without a residue are checked
    long touched = ~coveredValues;
    for (int k = 0; k < n; k++) {
      touched |= supportsOf[changed[k]];
    }
    int from = min - valueSupportBase;
    long span = (1L << (max - min)) * 2 - 1; // max - min < 64, so 2^64 - 1 wraps to every bit
    for (long check = touched & (span << from); check != 0; check &= check - 1) {
      int bit = Long.numberOfTrailingZeros(check);
      int v = valueSupportBase + bit;
      if (!value.domain.contains(v)) {
        continue;
      }
      int q = valueSupport[bit];
      if (q < 0 || !index.domain.contains(q + 1 + indexOffset) || !list[q].domain.contains(v)) {
        q = findValue(v);
        if (q < 0) {
          return false;
        }
        valueSupport[bit] = q;
        supportsOf[q] |= 1L << bit;
        coveredValues |= 1L << bit;
      }
    }
    return true;
  }

  /** The first open position whose index value is in lo..hi, or -1. */
  private int nextOpen(int lo, int hi, int v) {
    IntDomain d = index.domain;
    for (int i = d.contains(lo) ? lo : d.nextValue(lo); i <= hi && i >= lo; ) {
      int q = i - 1 - indexOffset;
      if (open(q, v)) {
        return q;
      }
      int next = d.nextValue(i);
      if (next <= i) {
        break;
      }
      i = next;
    }
    return -1;
  }

  /** Whether position q is selectable and its variable is not fixed to v. */
  private boolean open(int q, int v) {
    return q >= 0
        && index.domain.contains(q + 1 + indexOffset)
        && !(list[q].singleton() && list[q].value() == v);
  }

  /** Whether selectable position q has a common value with the value and reaches bound v. */
  private boolean keepsSupport(int q, int v, boolean lower) {
    return q >= 0
        && index.domain.contains(q + 1 + indexOffset)
        && (lower ? list[q].min() <= v : list[q].max() >= v)
        && supported(q);
  }

  private int findSupport(int v, boolean lower) {
    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int q = e.nextElement() - 1 - indexOffset;
      if ((lower ? list[q].min() <= v : list[q].max() >= v) && supported(q)) {
        return q;
      }
    }
    return -1;
  }

  /** A selectable position whose variable has value v, which the value has too, or -1. */
  private int findValue(int v) {
    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int q = e.nextElement() - 1 - indexOffset;
      if (list[q].domain.contains(v)) {
        return q;
      }
    }
    return -1;
  }

  @Override
  public void consistency(Store store) {

    boolean first = init.begin(store);
    int woken = wake;
    int n = changedCount;
    wake = WAKE_NONE;
    changedCount = 0;
    if (first) {
      initFirstConsistencyCheck(store);
    } else if (woken == WAKE_IDLE) {
      // only positions the index cannot select changed: the last call's result still holds
      return;
    } else if (woken == WAKE_LIST && !index.singleton() && listChangeKeepsFixpoint(n)) {
      return;
    }
    // changes seen by a full call are not checked against the value residues: drop them unless
    // the scan below rebuilds them
    valueSupportBase = Integer.MAX_VALUE;

    if (value.singleton() && index.singleton()) {
      IntVar v = list[index.value() - 1 - indexOffset];
      v.domain.inValue(store.level, v, value.value());
      removeConstraint();
      return;
    }
    if (index.singleton()) {
      int position = index.value() - 1 - indexOffset;
      if (REWRITE_FIXED_INDEX && list[position] != value && canRewrite(store)) {
        // the other positions can no longer matter: an equality stops their wake-ups
        rewriteTo(store, new XeqY(list[position], value));
        return;
      }
      value.domain.in(store.level, value, list[position].domain);
      list[position].domain.in(store.level, list[position], value.domain);
      if (value.singleton()) {
        removeConstraint();
      }
      return;
    }

    int min = IntDomain.MAX_INT;
    int max = IntDomain.MIN_INT;
    int valueMin = value.min();
    // the values of the selectable positions, as bits from valueMin, when the value spans 64 values
    boolean smallValue = !value.singleton() && (long) value.max() - valueMin < 64;
    long supportBits = 0;
    if (smallValue) {
      if (valueSupport == null) {
        valueSupport = new int[64];
        supportsOf = new long[list.length];
      }
      Arrays.fill(valueSupport, -1);
      Arrays.fill(supportsOf, 0L);
      valueSupportBase = valueMin;
    }
    int lowest = -1;
    int highest = -1;
    IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)
    boolean indexDomNonEmpty = false;
    // whether every selectable position is fixed to the fixed value: then the constraint holds
    boolean entailed = value.singleton();
    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int position = e.nextElement() - 1 - indexOffset;

      if (!supported(position)) {
        indexDomNonEmpty = true;
        if (indexDom.size == 0) {
          indexDom.unionAdapt(position + 1 + indexOffset);
        } else {
          indexDom.addLastElement(position + 1 + indexOffset);
        }
      } else {
        int lo = list[position].min();
        int hi = list[position].max();
        if (lo < min) {
          min = lo;
          lowest = position;
        }
        if (hi > max) {
          max = hi;
          highest = position;
        }
        entailed = entailed && list[position].singleton() && list[position].value() == valueMin;
        if (smallValue) {
          long bits = list[position].domain.bitsFrom(valueMin);
          for (long added = bits & ~supportBits; added != 0; added &= added - 1) {
            valueSupport[Long.numberOfTrailingZeros(added)] = position;
          }
          supportsOf[position] |= bits & ~supportBits;
          supportBits |= bits;
        }
      }
    }
    minSupport = lowest;
    maxSupport = highest;
    coveredValues = supportBits;

    if (indexDomNonEmpty) {
      index.domain.in(store.level, index, indexDom.complement());
    }
    value.domain.in(store.level, value, min, max);
    if (smallValue && (value.domain.bitsFrom(valueMin) & ~supportBits) != 0) {
      // a value inside the bounds that no selectable position can take; kept to small value
      // domains, where the union is a few word operations
      value.domain.in(
          store.level, value, new SmallDenseDomain(valueMin, Long.reverse(supportBits)));
    }

    if (index.singleton()) {
      // index is singleton; value == list[index - 1 - offset]
      IntVar lp = list[index.value() - 1 - indexOffset];
      value.domain.in(store.level, value, lp.domain);
      lp.domain.in(store.level, lp, value.domain);
      if (value.singleton()) {
        removeConstraint();
      }
    } else if (entailed) {
      // the positions not removed from the index all hold the value, so no change can prune
      removeConstraint();
    }
  }

  /**
   * Checks whether list[position] and the value share a value, first at the residue of the
   * position, and records the common value found.
   */
  private boolean supported(int position) {
    IntDomain x = list[position].domain;
    IntDomain v = value.domain;
    int r = residue[position];
    if (r != NO_SUPPORT && x.contains(r) && v.contains(r)) {
      return true;
    }
    r = commonValue(x, v);
    residue[position] = r;
    return r != NO_SUPPORT;
  }

  /**
   * The smallest value of both domains, or {@link #NO_SUPPORT}: each domain in turn jumps to its
   * next value at or after the current candidate.
   */
  static int commonValue(IntDomain a, IntDomain b) {
    if (a.isEmpty() || b.isEmpty()) {
      return NO_SUPPORT;
    }
    int hi = Math.min(a.max(), b.max());
    int v = Math.max(a.min(), b.min());
    while (v <= hi) {
      if (!a.contains(v)) {
        int next = a.nextValue(v);
        if (next <= v) {
          return NO_SUPPORT;
        }
        v = next;
      } else if (!b.contains(v)) {
        int next = b.nextValue(v);
        if (next <= v) {
          return NO_SUPPORT;
        }
        v = next;
      } else {
        return v;
      }
    }
    return NO_SUPPORT;
  }

  @Override
  public boolean satisfied() {
    return satisfiedForVariableList(list, value);
  }

  @Override
  public String toString() {
    return buildToString("elementVariableFast", list, value, true);
  }

  @Override
  public Optional<List<Constraint>> simplify() {
    if (getClass() != ElementVariableFast.class) {
      return Optional.empty();
    }
    return ElementSimplification.variables(
        index,
        list,
        value,
        indexOffset,
        (i, l, offset) -> new ElementVariableFast(i, l, value, offset),
        (i, l, offset) -> new ElementIntegerFast(i, l, value, offset));
  }

  @Override
  public ElementVariableFast copy(VarMap map) {
    return new ElementVariableFast(map.get(index), map.get(list), map.get(value), indexOffset);
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == ElementVariableFast.class
        && ElementVariableExplanation.explain(trail, entry, index, list, value, indexOffset, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == ElementVariableFast.class
        && ElementVariableExplanation.explainFailure(trail, index, list, value, indexOffset, out);
  }

  /**
   * Writes list[index - indexOffset] = value as clauses: the index is one of the positions, and a
   * position makes its variable and the value agree on every order literal and value literal of
   * either; each value of the value is supported by an auxiliary literal per position whose
   * variable has it, true exactly when the index is at that position and the variable takes the
   * value. Unit propagation on them prunes the index, the bounds and the holes of the value, and,
   * once the index is fixed, the domains of both, as consistency does.
   */
  @Override
  public boolean encode(PbModel model) {
    if (getClass() != ElementVariableFast.class
        || index == value
        || Arrays.asList(list).contains(index)) {
      return false;
    }
    IntDomain valueDomain = model.domain(value);
    IntDomain indexDomain = model.domain(index);
    long size = 0;
    for (ValueEnumeration e = indexDomain.valueEnumeration(); e.hasMoreElements(); ) {
      int p = e.nextElement() - 1 - indexOffset;
      if (p >= 0 && p < list.length) {
        size += model.domain(list[p]).getSize() + valueDomain.getSize();
      }
    }
    if (size > ENCODED_VALUES) {
      return false;
    }
    List<String> positions = new ArrayList<>();
    for (ValueEnumeration e = indexDomain.valueEnumeration(); e.hasMoreElements(); ) {
      int i = e.nextElement();
      int p = i - 1 - indexOffset;
      String at = model.equalTo(index, i);
      if (p < 0 || p >= list.length) {
        model.clause(PbModel.not(at));
        continue;
      }
      positions.add(at);
      IntVar x = list[p];
      if (x == value) {
        continue;
      }
      String elsewhere = PbModel.not(at);
      IntDomain values = model.domain(x).union(valueDomain);
      for (ValueEnumeration v = values.valueEnumeration(); v.hasMoreElements(); ) {
        int u = v.nextElement();
        model.clause(elsewhere, PbModel.not(model.atLeast(x, u)), model.atLeast(value, u));
        model.clause(elsewhere, PbModel.not(model.atLeast(value, u)), model.atLeast(x, u));
        model.clause(elsewhere, PbModel.not(model.equalTo(x, u)), model.equalTo(value, u));
        model.clause(elsewhere, PbModel.not(model.equalTo(value, u)), model.equalTo(x, u));
      }
    }
    model.clause(positions.toArray(new String[0]));
    // a value of the value is taken at some position whose variable has it
    for (ValueEnumeration v = valueDomain.valueEnumeration(); v.hasMoreElements(); ) {
      int u = v.nextElement();
      List<String> support = new ArrayList<>();
      support.add(PbModel.not(model.equalTo(value, u)));
      for (ValueEnumeration e = indexDomain.valueEnumeration(); e.hasMoreElements(); ) {
        int i = e.nextElement();
        int p = i - 1 - indexOffset;
        if (p < 0 || p >= list.length || !(list[p] == value || model.domain(list[p]).contains(u))) {
          continue;
        }
        String at = model.equalTo(index, i);
        if (list[p] == value) {
          support.add(at);
          continue;
        }
        String takes = model.equalTo(list[p], u);
        String y = model.auxiliary();
        model.clause(PbModel.not(y), at);
        model.clause(PbModel.not(y), takes);
        model.clause(y, PbModel.not(at), PbModel.not(takes));
        support.add(y);
      }
      model.clause(support.toArray(new String[0]));
    }
    return true;
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    int i = value.applyAsInt(index) - indexOffset - 1;
    if (i < 0 || i >= list.length) {
      return 1;
    }
    return value.applyAsInt(list[i]) == value.applyAsInt(this.value) ? 0 : 1;
  }

  @Override
  public IntVar selector() {
    return index;
  }

  @Override
  public IntVar[] selectable() {
    return list.clone();
  }

  @Override
  public int firstSelector() {
    return indexOffset + 1;
  }

  @Override
  public IntVar[] alwaysRead() {
    return new IntVar[] {value};
  }

  @Override
  public IntVar selectedEquals() {
    return value;
  }

  @Override
  public IntVar functionalResult() {
    return value;
  }

  @Override
  public int functionalValue(ToIntFunction<IntVar> value) {
    int i = value.applyAsInt(index) - indexOffset - 1;
    if (i < 0 || i >= list.length) {
      // The constraint is violated whatever the result, so the result keeps its value.
      return value.applyAsInt(this.value);
    }
    return value.applyAsInt(list[i]);
  }

  /**
   * A failure weighs the index, the value and the list variables the index can still select, not
   * the whole list: on XCSP3 LangfordBin, where every cell of the sequence is in the list of every
   * element, weighing the whole list made dom/wdeg branch on the cells instead of the positions.
   */
  @Override
  public void increaseWeight() {
    if (!IS_INCREASE_WEIGHT_ENABLED) {
      return;
    }
    index.weight++;
    value.weight++;
    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      long p = (long) e.nextElement() - 1 - indexOffset;
      if (p >= 0 && p < list.length) {
        list[(int) p].weight++;
      }
    }
  }
}
