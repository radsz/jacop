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
import java.util.stream.Stream;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * CountVar constraint implements the counting over number of occurrences of a given value in a list
 * of variables. The number of occurrences is specified by variable counter.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CountVar extends AbstractCount {

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

    return eq > counter.max() // equal values is more than allowed
        || list.length - notEq < counter.min() // possibly equal values is too low
        || (eq + notEq == list.length && !counter.domain.contains(eq)); // final check
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : countVar(").append(value).append(",[");
    appendArrayToString(result, list);
    result.append("], ").append(counter).append(" )");

    return result.toString();
  }
}
