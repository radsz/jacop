/*
 * AbstractBoolVector.java
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
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * Abstract base for vector boolean constraints (OrBoolVector, AndBoolVector). Provides shared
 * fields, constructor, swap, pruning events, include, and decomposition infrastructure.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractBoolVector extends PrimitiveConstraint {

  /** The list of boolean variables. */
  public final IntVar[] list;

  /** The result variable. */
  public final IntVar result;

  /** Length of the list after deduplication. */
  final int l;

  /** Decomposed constraints cache. */
  List<Constraint> constraints;

  /** Tracks first unprocessed position (backtrackable). */
  protected TimeStamp<Integer> position;

  /**
   * Constructs a vector boolean constraint.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param list boolean variable array.
   * @param result result variable.
   */
  protected AbstractBoolVector(AtomicInteger idNum, IntVar[] list, IntVar result) {

    checkInputForNullness("list", list);
    checkInputForNullness("result", new Object[] {result});

    this.numberId = idNum.incrementAndGet();

    Set<IntVar> varSet = new HashSet<>(Arrays.asList(list));
    this.l = varSet.size();
    this.list = varSet.toArray(new IntVar[0]);
    this.result = result;

    assert checkInvariants() == null : checkInvariants();

    if (l > 2) {
      queueIndex = 1;
    } else {
      queueIndex = 0;
    }

    setScope(Stream.concat(Arrays.stream(list), Stream.of(result)));
  }

  /**
   * Constructs a vector boolean constraint from a list.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param list boolean variable list.
   * @param result result variable.
   */
  protected AbstractBoolVector(AtomicInteger idNum, List<? extends IntVar> list, IntVar result) {
    this(idNum, list.toArray(new IntVar[0]), result);
  }

  /**
   * Checks that all boolean variables have valid boolean domains.
   *
   * @return null if invariants hold, error message otherwise.
   */
  public String checkInvariants() {
    return checkBooleanDomains(list);
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public void include(Store store) {
    position = new TimeStamp<>(store, 0);
  }

  /**
   * Swaps two elements in the list array.
   *
   * @param i first index.
   * @param j second index.
   */
  protected void swap(int i, int j) {
    if (i != j) {
      IntVar tmp = list[i];
      list[i] = list[j];
      list[j] = tmp;
    }
  }

  /**
   * Creates the combining constraint used in decomposition (Or or And).
   *
   * @param boolConstraints the array of XeqC constraints for each list variable.
   * @return the combining constraint.
   */
  protected abstract PrimitiveConstraint createCombiner(PrimitiveConstraint[] boolConstraints);

  @Override
  public List<Constraint> decompose(Store store) {

    constraints = new ArrayList<>();

    PrimitiveConstraint[] boolConstraints = new PrimitiveConstraint[l];

    IntervalDomain booleanDom = new IntervalDomain(0, 1);

    for (int i = 0; i < boolConstraints.length; i++) {
      boolConstraints[i] = new XeqC(list[i], 1);
      constraints.add(new In(list[i], booleanDom));
    }

    constraints.add(new In(result, booleanDom));

    constraints.add(new Eq(createCombiner(boolConstraints), new XeqC(result, 1)));

    return constraints;
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }
}
