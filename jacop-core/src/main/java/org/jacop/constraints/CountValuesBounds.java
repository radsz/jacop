/*
 * CountValuesBounds.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * CountValuesBounds constraint implements the counting over numbers of occurrences of a given
 * vector of values in a list of variables. The number of occurrences is specified by lower and
 * upper bounds.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CountValuesBounds extends AbstractCountValues {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It counts the number of occurences of the specified value in a list. */
  private final Bounds[] counter;

  private final Bounds counterRest;
  private final Bounds[] extendedCounter;

  /** Lower and upper bounds on values occurence. */
  final int[] lb;

  final int[] ub;

  /**
   * It constructs a CountValuesBounds constraint.
   *
   * @param values values that are counted
   * @param list variables which equality to values is counted.
   * @param lb minimal number of variables equal to a value.
   * @param ub maximal number of variables equal to a value.
   */
  public CountValuesBounds(IntVar[] list, int[] lb, int[] ub, int[] values) {

    super(idNumber, list, values);

    checkInputForNullness("list", list);

    this.lb = lb;
    this.ub = ub;
    this.counter = new Bounds[values.length];
    this.counterRest = new Bounds(0, n);

    for (int i = 0; i < values.length; i++) {
      counter[i] = new Bounds(lb[i], ub[i]);
    }

    extendedCounter = new Bounds[counter.length + 1];
    System.arraycopy(counter, 0, extendedCounter, 0, counter.length);
    extendedCounter[counter.length] = counterRest;

    setScope(Arrays.stream(this.list));
  }

  /**
   * It constructs a CountValuesBounds constraint.
   *
   * @param values values that are counted
   * @param list variables which equality to values is counted.
   * @param lb minimal number of variables equal to a value.
   * @param ub maximal number of variables equal to a value.
   */
  public CountValuesBounds(List<? extends IntVar> list, int[] lb, int[] ub, int[] values) {
    this(list.toArray(new IntVar[0]), lb, ub, values);
  }

  @Override
  protected void updateCounterRest(Store store, int restEq, int restMayBe) {
    counterRest.in(restEq, restEq + restMayBe);
  }

  @Override
  protected void updateCounter(Store store, int i, int numberEq, int numberMayBe) {
    counter[i].in(numberEq, numberEq + numberMayBe);
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
    extendedCounter[i].in(newMin, newMax);
  }

  @Override
  protected void assignValue(Store store, IntVar v, int value) {
    v.domain.inValue(store.level, v, value);
  }

  /**
   * Checks if the constraint is satisfied.
   *
   * @return true if the constraint is satisfied, false otherwise.
   */
  public boolean satisfied() {

    for (int i = 0; i < counter.length; i++) {
      int v = values[i];

      int cc = 0;
      for (int j = 0; j < n; j++) {
        if (list[j].singleton(v)) {
          cc++;
        }
      }
      if (cc < counter[i].lb || cc > counter[i].ub) {
        return false;
      }
    }

    return true;
  }

  @Override
  public String toString() {

    return id()
        + " : CountValuesBounds("
        + Arrays.asList(list)
        + ", "
        + Arrays.toString(lb)
        + ", "
        + Arrays.toString(ub)
        + ", "
        + Arrays.toString(values);
  }

  static class Bounds {

    final int lb;
    final int ub;
    int min;
    int max;

    Bounds(int min, int max) {
      this.min = min;
      this.max = max;
      this.lb = min;
      this.ub = max;
    }

    void in(int min, int max) {
      if (min > ub || max < lb) {
        throw Store.failException;
      } else {
        this.min = Math.max(min, lb);

        this.max = Math.min(max, ub);
      }
    }

    int min() {
      return min;
    }

    int max() {
      return max;
    }

    boolean singleton() {
      return min == max;
    }

    @Override
    public String toString() {

      return min + "(" + lb + ").." + max + "(" + ub + ")";
    }
  }
}
