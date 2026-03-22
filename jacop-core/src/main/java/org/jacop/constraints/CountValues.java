/*
 * CountValues.java
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
import org.jacop.core.Store;

/**
 * CountValues constraint implements the counting over numbers of occurrences of a given vector of
 * values in a list of variables. The number of occurrences is specified by variable counter.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CountValues extends AbstractCountValues {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It counts the number of occurences of the specified value in a list. */
  private final IntVar[] counter;

  private final IntVar counterRest;
  private final IntVar[] extendedCounter;

  /**
   * It constructs a CountValues constraint.
   *
   * @param values values that are counted
   * @param list variables which equality to values is counted.
   * @param counter number of variables equal to a value.
   */
  public CountValues(IntVar[] list, IntVar[] counter, int[] values) {

    super(idNumber, list, values);

    checkInputForNullness(new String[] {"list", "counter"}, list, new Object[] {counter});

    this.counter = counter;
    this.counterRest = new IntVar(counter[0].getStore(), 0, n);

    extendedCounter = new IntVar[counter.length + 1];
    System.arraycopy(counter, 0, extendedCounter, 0, counter.length);
    extendedCounter[counter.length] = counterRest;

    setScope(Stream.concat(Arrays.stream(this.list), Arrays.stream(counter)));
  }

  /**
   * It constructs a CountValues constraint.
   *
   * @param values value taht are counted
   * @param list variables which equality to values is counted.
   * @param counter number of variables equal to values.
   */
  public CountValues(List<? extends IntVar> list, IntVar[] counter, int[] values) {
    this(list.toArray(new IntVar[0]), counter, values);
  }

  @Override
  protected void updateCounterRest(Store store, int restEq, int restMayBe) {
    counterRest.domain.in(store.level, counterRest, restEq, restEq + restMayBe);
  }

  @Override
  protected void updateCounter(Store store, int i, int numberEq, int numberMayBe) {
    counter[i].domain.in(store.level, counter[i], numberEq, numberEq + numberMayBe);
  }

  @Override
  protected int getCounterMin(int i) {
    return counter[i].min();
  }

  @Override
  protected int getCounterMax(int i) {
    return counter[i].max();
  }

  @Override
  protected int getCounterRestMin() {
    return counterRest.min();
  }

  @Override
  protected int getCounterRestMax() {
    return counterRest.max();
  }

  @Override
  protected int getExtendedCounterLength() {
    return extendedCounter.length;
  }

  @Override
  protected int getExtendedCounterMin(int i) {
    return extendedCounter[i].min();
  }

  @Override
  protected int getExtendedCounterMax(int i) {
    return extendedCounter[i].max();
  }

  @Override
  protected void updateExtendedCounter(Store store, int i, int newMin, int newMax) {
    extendedCounter[i].domain.in(store.level, extendedCounter[i], newMin, newMax);
  }

  @Override
  protected void assignValue(Store store, IntVar v, int value) {
    v.domain.in(store.level, v, value, value);
  }

  /**
   * Checks if the constraint is satisfied.
   *
   * @return true if the constraint is satisfied, false otherwise.
   */
  public boolean satisfied() {

    for (int i = 0; i < counter.length; i++) {
      int v = values[i];
      if (counter[i].singleton()) {
        counter[i].value();
      } else {
        return false;
      }

      int cc = countOccurrences(v);
      if (cc != counter[i].value()) {
        return false;
      }
    }

    return true;
  }

  @Override
  public String toString() {

    return id()
        + " : CountValues("
        + Arrays.asList(list)
        + ", "
        + Arrays.asList(counter)
        + ", "
        + Arrays.toString(values);
  }
}
