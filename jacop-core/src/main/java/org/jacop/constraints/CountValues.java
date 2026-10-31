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
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.ToIntFunction;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * CountValues constraint implements the counting over numbers of occurrences of a given vector of
 * values in a list of variables. The number of occurrences is specified by variable counter.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CountValues extends AbstractCountValues
    implements Violation, Copyable<CountValues>, Explainable, PbEncodable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It counts the number of occurences of the specified value in a list. */
  private final IntVar[] counter;

  private final IntVar counterRest;
  // whether counterRest was given, rather than made by the constraint
  private final boolean restGiven;
  private final IntVar[] extendedCounter;

  /**
   * It constructs a CountValues constraint.
   *
   * @param values values that are counted, without repetitions
   * @param list variables which equality to values is counted.
   * @param counter number of variables equal to a value.
   */
  public CountValues(IntVar[] list, IntVar[] counter, int[] values) {
    this(list, counter, values, null);
  }

  /**
   * It constructs a CountValues constraint with the given variable for the number of variables not
   * equal to any value, or a new one when it is null.
   */
  private CountValues(IntVar[] list, IntVar[] counter, int[] values, IntVar rest) {

    super(idNumber, list, values);

    checkInputForNullness("counter", counter);
    if (counter.length != values.length) {
      throw new IllegalArgumentException(
          "Constraint CountValues has "
              + counter.length
              + " counters for "
              + values.length
              + " values.");
    }
    if (counter.length == 0 && list.length == 0) {
      throw new IllegalArgumentException(
          "Constraint CountValues needs at least one variable or one counter.");
    }

    this.counter = Arrays.copyOf(counter, counter.length);
    Store store = counter.length > 0 ? counter[0].getStore() : list[0].getStore();
    this.counterRest = rest != null ? rest : new IntVar(store, 0, n);
    this.restGiven = rest != null;

    extendedCounter = new IntVar[counter.length + 1];
    System.arraycopy(counter, 0, extendedCounter, 0, counter.length);
    extendedCounter[counter.length] = this.counterRest;

    // counterRest is in the scope: the constraint prunes with its domain, so an explanation made of
    // the constraint's arguments must cover it
    setScope(
        Stream.concat(
            Stream.concat(Arrays.stream(this.list), Arrays.stream(counter)),
            Stream.of(this.counterRest)));
  }

  /**
   * It constructs a CountValues constraint.
   *
   * @param values values that are counted, without repetitions
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

    // entailed only if no unassigned variable can change a count
    for (int i = 0; i < counter.length; i++) {
      int v = values[i];
      if (!counter[i].singleton()) {
        return false;
      }

      int c = counter[i].value();
      if (countOccurrences(v) != c || countPossible(v) != c) {
        return false;
      }
    }

    return true;
  }

  // the time spent in flow explanations of this constraint
  private final CardinalityExplanation.Budget budget = new CardinalityExplanation.Budget();

  // the flow network over the values in increasing order, the rest counted by counterRest
  private CardinalityExplanation.Network network() {
    IntVar[] sortedCounter = new IntVar[sortedValues.length];
    for (int k = 0; k < sortedValues.length; k++) {
      sortedCounter[k] = counter[indexOfSorted[k]];
    }
    return new CardinalityExplanation.Network(
        list, sortedValues, sortedCounter, null, null, true, counterRest, budget);
  }

  /**
   * Writes a count line per value; the solver derives the cuts its flow explanations need. The
   * variables taking no counted value are counted by the rest counter.
   */
  @Override
  public boolean encode(PbModel model) {
    Set<IntVar> distinct = new HashSet<>(Arrays.asList(list));
    if (getClass() != CountValues.class || distinct.size() != list.length) {
      return false;
    }
    for (IntVar c : extendedCounter) {
      // a counter among the variables, or two counters of one variable, would mix their bounds
      if (!model.domain(c).singleton() && !distinct.add(c)) {
        return false;
      }
    }
    model.cardinality(list, values, counter, null, null, false, counterRest);
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == CountValues.class && network().explain(trail, entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == CountValues.class && network().explainFailure(trail, out);
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

  @Override
  public CountValues copy(VarMap map) {
    return new CountValues(map.get(list), map.get(counter), values, map.get(counterRest));
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    long violated = 0;
    int counted = 0;
    for (int i = 0; i < values.length; i++) {
      int c = Violations.count(list, values[i], value);
      counted += c;
      violated += Math.abs(c - value.applyAsInt(counter[i]));
    }
    // a counter of the other values made by the constraint follows from the others
    return restGiven
        ? violated + Math.abs(list.length - counted - value.applyAsInt(counterRest))
        : violated;
  }
}
