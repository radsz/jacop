/*
 * Count.java
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
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Count constraint implements the counting over number of occurrences of a given value in a list of
 * variables. The number of occurrences is specified by variable counter.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Count extends AbstractCount implements Copyable<Count>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It specifies variable idNumber to count the number of occurences of the specified value in a
   * list.
   */
  private final IntVar counter;

  /** Whether the counter also occurs in the list. */
  private final boolean counterInList;

  /** The value to which is any variable is equal to makes the constraint count it. */
  private final int value;

  /**
   * It constructs a Count constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public Count(IntVar[] list, IntVar counter, int value) {

    super(idNumber, list);

    checkInputForNullness(new String[] {"list", "counter"}, list, new Object[] {counter});

    this.counter = counter;
    this.value = value;
    this.counterInList = Arrays.asList(list).contains(counter);

    setScope(Stream.concat(Arrays.stream(this.list), Stream.of(counter)));
  }

  /**
   * It constructs a Count constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public Count(List<? extends IntVar> list, IntVar counter, int value) {
    this(list.toArray(new IntVar[0]), counter, value);
  }

  @Override
  public void consistency(final Store store) {

    while (true) {

      countOccurrences(value);
      int numberEq = countEq;
      int numberMayBe = countMayBe;
      int start = countStart;

      int counterMin = counter.min();
      int counterMax = counter.max();

      counter.domain.in(store.level, counter, numberEq, numberEq + numberMayBe);

      // When the counter also occurs in the list, narrowing it can change the counts themselves,
      // so count again until the counter bounds are stable.
      if (counterInList && (counter.min() != counterMin || counter.max() != counterMax)) {
        continue;
      }

      // The narrowing above fixes the counter in both cases below.
      if (numberEq + numberMayBe == counter.min()) {
        for (int i = start; i < list.length; i++) {
          IntVar v = list[i];
          v.domain.inValue(store.level, v, value);
        }

        removeConstraint();
        return;

      } else if (numberEq == counter.max()) {
        for (int i = start; i < list.length; i++) {
          IntVar v = list[i];
          v.domain.inComplement(store.level, v, value);
        }

        removeConstraint();
        return;
      }

      updateState(numberEq, start);
      return;
    }
  }

  @Override
  public void notConsistency(final Store store) {

    countOccurrences(value);
    int numberEq = countEq;
    int numberMayBe = countMayBe;
    int start = countStart;

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
    SatisfactionCounts sc = countSatisfaction(value);
    return sc.eq() + sc.notEq() == list.length && counter.singleton(sc.eq());
  }

  @Override
  public boolean notSatisfied() {
    SatisfactionCounts sc = countSatisfaction(value);
    return sc.eq() + sc.notEq() == list.length && !counter.domain.contains(sc.eq());
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : count(").append(value).append(",[");
    appendArrayToString(result, list);
    result.append("], ").append(counter).append(" )");

    return result.toString();
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == Count.class
        && new CountExplanation(trail, list, value, counter, 0, 0, entry).explain(entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == Count.class
        && new CountExplanation(trail, list, value, counter, 0, 0, trail.size())
            .explainFailure(out);
  }

  @Override
  public Count copy(VarMap map) {
    return new Count(map.get(list), map.get(counter), value);
  }
}
