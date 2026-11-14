/*
 * CountVar.java
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
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.ToIntFunction;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * CountVar constraint implements the counting over number of occurrences of a given value in a list
 * of variables. The number of occurrences is specified by variable counter.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CountVar extends AbstractCount implements Violation, Copyable<CountVar>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable to count the number of occurences of the specified value in a list. */
  private final IntVar counter;

  /** The value to which is any variable is equal to makes the constraint count it. */
  private final IntVar value;

  /**
   * It constructs a CountVar constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public CountVar(IntVar[] list, IntVar counter, IntVar value) {

    super(idNumber, list);

    checkInputForNullness(
        new String[] {"list", "counter", "value"},
        list,
        new Object[] {counter},
        new Object[] {value});

    this.counter = counter;
    this.value = value;

    setScope(
        Stream.concat(
            Stream.of(value), Stream.concat(Arrays.stream(this.list), Stream.of(counter))));
  }

  /**
   * It constructs a CountVar constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public CountVar(List<? extends IntVar> list, IntVar counter, IntVar value) {
    this(list.toArray(new IntVar[0]), counter, value);
  }

  @Override
  public void consistency(final Store store) {

    // Pruning the value, or a variable that is also the counter or the value, changes the counts,
    // so propagate until nothing changes.
    do {

      store.propagationHasOccurred = false;

      countEqualAndMaybe();
      int numberEq = countEq;
      int numberMayBe = countMayBe;
      int start = countStart;

      if (numberEq + numberMayBe == counter.min()) {
        // every undecided variable equals the value: first narrow the value to all of them, then
        // each of them to the value
        for (int i = start; i < list.length; i++) {
          IntVar v = list[i];
          value.domain.in(store.level, value, v.domain);
        }
        for (int i = start; i < list.length; i++) {
          IntVar v = list[i];
          v.domain.in(store.level, v, value.domain);
        }
        if (value.singleton()) {
          counter.domain.inValue(store.level, counter, numberEq + numberMayBe);
          removeConstraint();
          return;
        }
      } else if (numberEq == counter.max()) {
        // no undecided variable equals the value
        if (value.singleton()) {
          for (int i = start; i < list.length; i++) {
            IntVar v = list[i];
            v.domain.inComplement(store.level, v, value.value());
          }
          counter.domain.inValue(store.level, counter, numberEq);
          removeConstraint();
          return;
        }
        for (int i = start; i < list.length; i++) {
          IntVar v = list[i];
          if (v.singleton()) {
            value.domain.inComplement(store.level, value, v.value());
          }
        }
      }

      updateState(numberEq, start);

      counter.domain.in(store.level, counter, numberEq, numberEq + numberMayBe);

      if (!value.singleton() && value.getSize() <= SMALL_VALUE_DOMAIN) {
        pruneByValueCounts(store, start);
      }

    } while (store.propagationHasOccurred);
  }

  /** The value domains up to this size are checked value by value against the counter. */
  private static final int SMALL_VALUE_DOMAIN = 64;

  /** The values of the value variable, and for each the undecided variables fixed to it. */
  private final int[] values = new int[SMALL_VALUE_DOMAIN];

  private final int[] valueEq = new int[SMALL_VALUE_DOMAIN];

  /** For each value, the undecided variables that are not fixed but contain it. */
  private final int[] valueMayBe = new int[SMALL_VALUE_DOMAIN];

  /**
   * Prunes value by value, for a value variable that is not fixed: the value variable keeps the
   * values w whose possible numbers of occurrences meet the counter, the counter keeps those
   * numbers, and a variable of the list keeps a value if some w still meets the counter with it.
   * The decided variables do not intersect the value variable, so only the undecided ones count.
   *
   * @param store the constraint store.
   * @param start the first undecided variable.
   */
  private void pruneByValueCounts(Store store, int start) {
    int candidates = 0;
    for (ValueEnumeration e = value.domain.valueEnumeration(); e.hasMoreElements(); ) {
      values[candidates++] = e.nextElement();
    }
    int size = 0;
    IntervalDomain numbers = new IntervalDomain();
    for (int k = 0; k < candidates; k++) {
      int w = values[k];
      int numberEq = 0;
      int numberMayBe = 0;
      for (int i = start; i < list.length; i++) {
        IntVar v = list[i];
        if (v.domain.contains(w)) {
          if (v.singleton()) {
            numberEq++;
          } else {
            numberMayBe++;
          }
        }
      }
      if (counter.domain.isIntersecting(numberEq, numberEq + numberMayBe)) {
        values[size] = w;
        valueEq[size] = numberEq;
        valueMayBe[size] = numberMayBe;
        size++;
        numbers.unionAdapt(numberEq, numberEq + numberMayBe);
      } else {
        value.domain.inComplement(store.level, value, w);
      }
    }
    counter.domain.in(store.level, counter, numbers);

    for (int i = start; i < list.length; i++) {
      IntVar v = list[i];
      if (!v.singleton()) {
        pruneListVariable(store, v, size);
      }
    }
  }

  /**
   * Keeps a value of an unfixed list variable only if some remaining value w of the value variable
   * still meets the counter with it.
   *
   * @param store the constraint store.
   * @param v the list variable.
   * @param size the number of remaining values in {@link #values}.
   */
  private void pruneListVariable(Store store, IntVar v, int size) {
    // the values w that meet the counter when v differs from w; two of them support every value
    int supports = 0;
    int support = 0;
    for (int j = 0; j < size && supports < 2; j++) {
      int w = values[j];
      int max = valueEq[j] + valueMayBe[j] - (v.domain.contains(w) ? 1 : 0);
      if (counter.domain.isIntersecting(valueEq[j], max)) {
        supports++;
        support = w;
      }
    }
    if (supports == 2) {
      return;
    }
    // a value a not supported that way needs w = a, with v counted
    IntervalDomain kept = new IntervalDomain();
    for (int j = 0; j < size; j++) {
      int w = values[j];
      if (v.domain.contains(w)
          && counter.domain.isIntersecting(valueEq[j] + 1, valueEq[j] + valueMayBe[j])) {
        kept.unionAdapt(w, w);
      }
    }
    if (supports == 1) {
      if (!kept.contains(support)) {
        v.domain.inComplement(store.level, v, support);
      }
    } else {
      v.domain.in(store.level, v, kept);
    }
  }

  private void countEqualAndMaybe() {
    int numberEq = numberEqual();
    int numberMayBe = 0;
    int start = position();
    for (int i = start; i < list.length; i++) {
      IntVar v = list[i];
      if (v.domain.isIntersecting(value.domain)) {
        if (v.singleton() && value.singleton() && v.value() == value.value()) {
          numberEq++;
          swap(start, i);
          start++;
        } else {
          numberMayBe++;
        }
      } else {
        swap(start, i);
        start++;
      }
    }
    countEq = numberEq;
    countMayBe = numberMayBe;
    countStart = start;
  }

  @Override
  public void notConsistency(final Store store) {

    int numberEq = numberEqual();
    int numberMayBe = 0;
    int start = position();
    for (int i = start; i < list.length; i++) {
      IntVar v = list[i];
      if (v.domain.isIntersecting(value.domain)) {
        if (v.singleton() && value.singleton() && v.value() == value.value()) {
          numberEq++;
          swap(start, i);
          start++;
        } else {
          numberMayBe++;
        }
      } else { // does not have the value in its domain
        swap(start, i);
        start++;
      }
    }

    if (numberEq > counter.max() || numberEq + numberMayBe < counter.min()) {
      removeConstraint();
      return;
    }

    if (start == list.length) {
      counter.domain.inComplement(store.level, counter, numberEq);
    }

    updateState(numberEq, start);
  }

  @Override
  public boolean satisfied() {

    int eq = 0;
    int notEq = 0;

    for (IntVar v : list) {
      if (v.singleton() && value.singleton() && v.value() == value.value()) {
        eq++;
      } else if (!v.domain.isIntersecting(value.domain)) {
        notEq++;
      }
    }

    return eq + notEq == list.length && counter.singleton(eq);
  }

  @Override
  public boolean notSatisfied() {

    int eq = 0;
    int notEq = 0;

    for (IntVar v : list) {
      if (v.singleton() && value.singleton() && v.value() == value.value()) {
        eq++;
      } else if (!v.domain.isIntersecting(value.domain)) {
        notEq++;
      }
    }

    // the count lies between the fixed occurrences and those still possible
    return !counter.domain.isIntersecting(eq, list.length - notEq);
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : countVar(").append(value).append(",[");
    appendArrayToString(result, list);
    result.append("], ").append(counter).append(" )");

    return result.toString();
  }

  /*
   * Explanations for lazy clause generation. A list variable is ruled out when its domain misses
   * the value's, and counted when it and the value are fixed to the same w. The counter is at
   * least the number counted and at most the number not ruled out. When the counter needs every
   * variable not ruled out, each of them equals the value, so it is within the value's domain and
   * the value within its domain; when the counter allows no more than those counted and the value
   * is fixed to w, the others lose w. The pruning of the value by counts per value is left to the
   * generic reason.
   */

  /** A list variable and the value are compared value by value over at most this many values. */
  private static final int OVERLAP_WIDTH = 256;

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar v = trail.variable(entry);
    int kind = trail.kind(entry);
    int mark = out.size();
    if (v == counter) {
      if (kind == AtomicTrail.NE) {
        return false;
      }
      int bound = trail.skippedBound(entry);
      if (kind == AtomicTrail.GE) {
        int w = fixedValue(trail, entry);
        if (w != Integer.MIN_VALUE && addCounted(trail, entry, w, bound, -1, out)) {
          trail.addSkippedHoles(entry, bound, out);
          citeValue(trail, entry, w, out);
          return true;
        }
      } else if (addRuledOut(trail, entry, list.length - bound, -1, out)) {
        trail.addSkippedHoles(entry, bound, out);
        return true;
      }
      out.truncate(mark);
      return false;
    }
    int least = trail.minBefore(counter, entry);
    if (v == value) {
      if (kind == AtomicTrail.NE && explainValueOut(trail, entry, trail.value(entry), out)) {
        return true;
      }
      out.truncate(mark);
      // every list variable not ruled out equals the value, and one of them misses the atom's
      // values
      if (least < 1) {
        return false;
      }
      for (int i = 0; i < list.length; i++) {
        if (list[i] != value
            && list[i] != counter
            && within(trail, entry, list[i], out)
            && addRuledOut(trail, entry, list.length - least, i, out)) {
          trail.addBoundReaching(counter, entry, true, least, out);
          return true;
        }
        out.truncate(mark);
      }
      return false;
    }
    for (int i = 0; i < list.length; i++) {
      if (list[i] != v || v == counter) {
        continue;
      }
      int w = fixedValue(trail, entry);
      if (w != Integer.MIN_VALUE && removesOnly(trail, entry, w)) {
        // the counter allows no more than the others counted
        int most = trail.maxBefore(counter, entry);
        if (addCounted(trail, entry, w, most, i, out)) {
          trail.addBoundReaching(counter, entry, false, most, out);
          if (kind != AtomicTrail.NE) {
            // a bound that steps over w and the holes behind it
            boolean ge = kind == AtomicTrail.GE;
            trail.addBoundReaching(v, entry, ge, w, out);
            trail.addSkippedHoles(entry, ge ? w + 1 : w - 1, out);
          }
          citeValue(trail, entry, w, out);
          return true;
        }
        out.truncate(mark);
      }
      // the counter needs every other variable not ruled out, and this one, which equals the value
      if (within(trail, entry, value, out)
          && addRuledOut(trail, entry, list.length - least, i, out)) {
        trail.addBoundReaching(counter, entry, true, least, out);
        return true;
      }
      out.truncate(mark);
      return false;
    }
    return false;
  }

  // the value cannot be a: more list variables are fixed to a than the counter allows, or fewer
  // can take a than it needs
  private boolean explainValueOut(AtomicTrail trail, int entry, int a, EntryList out) {
    int most = trail.maxBefore(counter, entry);
    if (most < list.length && addCounted(trail, entry, a, most + 1, -1, out)) {
      trail.addBoundReaching(counter, entry, false, most, out);
      return true;
    }
    int least = trail.minBefore(counter, entry);
    int found = 0;
    for (int i = 0; i < list.length && found <= list.length - least; i++) {
      if (list[i] != value && excludes(trail, list[i], entry, a, out)) {
        found++;
      }
    }
    if (found > list.length - least) {
      trail.addBoundReaching(counter, entry, true, least, out);
      return true;
    }
    return false;
  }

  // cites why the entry's atom (on another variable) holds for every value of x before it
  private static boolean within(AtomicTrail trail, int entry, IntVar x, EntryList out) {
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return excludes(trail, x, entry, trail.value(entry), out);
    }
    int bound = trail.skippedBound(entry);
    boolean ge = kind == AtomicTrail.GE;
    if (ge ? trail.minBefore(x, entry) < bound : trail.maxBefore(x, entry) > bound) {
      return false;
    }
    trail.addBoundReaching(x, entry, ge, bound, out);
    trail.addSkippedHoles(entry, bound, out);
    return true;
  }

  @Override
  public boolean explainEntailment(
      AtomicTrail trail, int position, boolean entailed, EntryList out) {
    int mark = out.size();
    int cmin = trail.minBefore(counter, position);
    int cmax = trail.maxBefore(counter, position);
    int w = fixedValue(trail, position);
    if (entailed) {
      if (w != Integer.MIN_VALUE
          && cmin == cmax
          && addCounted(trail, position, w, cmin, -1, out)
          && addRuledOut(trail, position, list.length - cmin, -1, out)) {
        trail.addBoundReaching(counter, position, true, cmin, out);
        trail.addBoundReaching(counter, position, false, cmin, out);
        citeValue(trail, position, w, out);
        return true;
      }
    } else {
      if (w != Integer.MIN_VALUE && addCounted(trail, position, w, cmax + 1, -1, out)) {
        trail.addBoundReaching(counter, position, false, cmax, out);
        citeValue(trail, position, w, out);
        return true;
      }
      out.truncate(mark);
      if (addRuledOut(trail, position, list.length - cmin + 1, -1, out)) {
        trail.addBoundReaching(counter, position, true, cmin, out);
        return true;
      }
    }
    out.truncate(mark);
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return explainEntailment(trail, trail.size(), false, out);
  }

  @Override
  public boolean explainNegated(AtomicTrail trail, int entry, EntryList out) {
    // the counter differs from the count once every variable is counted or ruled out
    if (trail.variable(entry) != counter || trail.kind(entry) != AtomicTrail.NE) {
      return false;
    }
    int w = fixedValue(trail, entry);
    int c = trail.value(entry);
    int mark = out.size();
    if (w != Integer.MIN_VALUE
        && addCounted(trail, entry, w, c, -1, out)
        && addRuledOut(trail, entry, list.length - c, -1, out)) {
      citeValue(trail, entry, w, out);
      return true;
    }
    out.truncate(mark);
    return false;
  }

  @Override
  public boolean explainNegatedFailure(AtomicTrail trail, EntryList out) {
    return explainEntailment(trail, trail.size(), true, out);
  }

  // the value fixed before the position, or Integer.MIN_VALUE
  private int fixedValue(AtomicTrail trail, int position) {
    int w = trail.minBefore(value, position);
    return w == trail.maxBefore(value, position) ? w : Integer.MIN_VALUE;
  }

  private void citeValue(AtomicTrail trail, int position, int w, EntryList out) {
    trail.addBoundReaching(value, position, true, w, out);
    trail.addBoundReaching(value, position, false, w, out);
  }

  // cites k list variables other than skip fixed to w
  private boolean addCounted(
      AtomicTrail trail, int position, int w, int k, int skip, EntryList out) {
    int found = 0;
    for (int i = 0; i < list.length && found < k; i++) {
      IntVar x = list[i];
      if (i != skip
          && x != value
          && trail.minBefore(x, position) == w
          && trail.maxBefore(x, position) == w) {
        trail.addBoundReaching(x, position, true, w, out);
        trail.addBoundReaching(x, position, false, w, out);
        found++;
      }
    }
    return found >= k;
  }

  // cites k list variables other than skip whose domains miss the value's
  private boolean addRuledOut(AtomicTrail trail, int position, int k, int skip, EntryList out) {
    int found = 0;
    for (int i = 0; i < list.length && found < k; i++) {
      IntVar x = list[i];
      int mark = out.size();
      if (i != skip && x != value && x != counter) {
        if (disjoint(trail, x, position, out)) {
          found++;
        } else {
          out.truncate(mark);
        }
      }
    }
    return found >= k;
  }

  // cites why x and the value have no common value before the position
  private boolean disjoint(AtomicTrail trail, IntVar x, int position, EntryList out) {
    int xMin = trail.minBefore(x, position);
    int xMax = trail.maxBefore(x, position);
    int yMin = trail.minBefore(value, position);
    int yMax = trail.maxBefore(value, position);
    if (xMax < yMin) {
      trail.addBoundReaching(x, position, false, xMax, out);
      trail.addBoundReaching(value, position, true, xMax + 1L, out);
      return true;
    }
    if (yMax < xMin) {
      trail.addBoundReaching(value, position, false, yMax, out);
      trail.addBoundReaching(x, position, true, yMax + 1L, out);
      return true;
    }
    int lo = Math.max(xMin, yMin);
    int hi = Math.min(xMax, yMax);
    if ((long) hi - lo >= OVERLAP_WIDTH) {
      return false;
    }
    trail.addBoundReaching(xMin >= yMin ? x : value, position, true, lo, out);
    trail.addBoundReaching(xMax <= yMax ? x : value, position, false, hi, out);
    for (int a = lo; a <= hi; a++) {
      if (!trail.excludedBefore(x, a, position, out)
          && !trail.excludedBefore(value, a, position, out)) {
        return false;
      }
      if (a == hi) {
        break;
      }
    }
    return true;
  }

  // cites why x cannot take a before the position
  private static boolean excludes(AtomicTrail trail, IntVar x, int position, int a, EntryList out) {
    if (trail.minBefore(x, position) > a) {
      trail.addBoundReaching(x, position, true, a + 1L, out);
      return true;
    }
    if (trail.maxBefore(x, position) < a) {
      trail.addBoundReaching(x, position, false, a - 1L, out);
      return true;
    }
    return trail.excludedBefore(x, a, position, out);
  }

  // whether the entry removes w and nothing else that its variable had before it
  private static boolean removesOnly(AtomicTrail trail, int entry, int w) {
    if (trail.kind(entry) == AtomicTrail.NE) {
      return trail.value(entry) == w;
    }
    IntVar x = trail.variable(entry);
    int bound = trail.skippedBound(entry);
    return trail.kind(entry) == AtomicTrail.GE
        ? trail.minBefore(x, entry) == w && bound == w + 1
        : trail.maxBefore(x, entry) == w && bound == w - 1;
  }

  @Override
  public CountVar copy(VarMap map) {
    return new CountVar(map.get(list), map.get(counter), map.get(value));
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    return Math.abs(
        Violations.count(list, value.applyAsInt(this.value), value) - value.applyAsInt(counter));
  }
}
