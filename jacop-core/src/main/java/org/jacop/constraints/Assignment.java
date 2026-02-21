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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Assignment constraint implements facility to improve channeling constraints between dual
 * viewpoints of permutation models. It enforces the relationship x[d[i]-shiftX]=i+shiftD and
 * d[x[i]-shiftD]=i+shiftX.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class Assignment extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent {

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
  LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<>();
  boolean firstConsistencyCheck = true;
  int firstConsistencyLevel;
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
    variableQueue.clear();
    if (level == firstConsistencyLevel) {
      firstConsistencyCheck = true;
    }
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      initRangesAndPropagateInitial(store);
      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;
    }

    while (!variableQueue.isEmpty()) {

      LinkedHashSet<IntVar> fdvs = variableQueue;

      variableQueue = new LinkedHashSet<>();

      for (IntVar V : fdvs) {
        propagateFromPrunedVariable(store, V);
      }
    }
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

  private void propagateFromPrunedVariable(Store store, IntVar v) {
    IntDomain vPrunedDomain = v.recentDomainPruning();
    if (vPrunedDomain.isEmpty()) {
      return;
    }
    Integer position = xs.get(v);
    if (position == null) {
      propagateFromPrunedD(store, v, vPrunedDomain);
    } else {
      propagateFromPrunedX(store, v, vPrunedDomain, position);
    }
  }

  private void propagateFromPrunedD(Store store, IntVar v, IntDomain vPrunedDomain) {
    Integer position = ds.get(v);
    vPrunedDomain = vPrunedDomain.intersect(rangeX);
    if (vPrunedDomain.isEmpty()) {
      return;
    }
    for (ValueEnumeration enumer = vPrunedDomain.valueEnumeration(); enumer.hasMoreElements(); ) {
      int dValue = enumer.nextElement() - shiftX;
      if (dValue >= 0 && dValue < x.length) {
        x[dValue].domain.inComplement(store.level, x[dValue], position);
      }
    }
    if (v.singleton()) {
      x[v.value() - shiftX].domain.in(store.level, x[v.value() - shiftX], position, position);
    }
  }

  private void propagateFromPrunedX(
      Store store, IntVar v, IntDomain vPrunedDomain, Integer position) {
    vPrunedDomain = vPrunedDomain.intersect(rangeD);
    if (vPrunedDomain.isEmpty()) {
      return;
    }
    for (ValueEnumeration enumer = vPrunedDomain.valueEnumeration(); enumer.hasMoreElements(); ) {
      int xValue = enumer.nextElement() - shiftD;
      if (xValue >= 0 && xValue < d.length) {
        d[xValue].domain.inComplement(store.level, d[xValue], position);
      }
    }
    if (v.singleton()) {
      d[v.value() - shiftD].domain.in(store.level, d[v.value() - shiftD], position, position);
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
    variableQueue.add((IntVar) v);
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
}
