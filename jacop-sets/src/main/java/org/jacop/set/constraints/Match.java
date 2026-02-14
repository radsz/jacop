/*
 * Match.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.set.constraints;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * This constraint matches the elements of the given set variable onto a list of integer variables.
 *
 * @author Radoslaw Szymanek, Krzysztof Kuchcinski, and Robert Åkemalm
 * @version 5.0
 */
public class Match extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It specifies a set variable whose values are being matched against integer variables from the
   * list.
   */
  private final SetVar a;

  /**
   * It specifies the list of integer variables which value is being matched against elements from a
   * set variable a.
   */
  private final IntVar[] list;

  /**
   * It constructs a match constraint to connect the value of set variable a to the values of
   * integer variables provided in the list.
   *
   * @param a set variable that is restricted to be equal to a set created from values specified by
   *     integer variables form the list.
   * @param list of integer variables that is restricted to have the same elements as set variable
   *     a.
   */
  public Match(SetVar a, IntVar[] list) {

    checkInputForNullness(new String[] {"a", "list"}, new Object[][] {{a}, list});

    this.numberId = idNumber.incrementAndGet();
    this.a = a;
    this.list = Arrays.copyOf(list, list.length);

    setScope(Stream.concat(Stream.of(a), Arrays.stream(list)));
  }

  @Override
  public void consistency(Store store) {

    a.domain.inCardinality(store.level, a, list.length, list.length);

    if (a.domain.glb().getSize() == list.length) {

      ValueEnumeration ve = a.domain.glb().valueEnumeration();
      int el;
      for (IntVar intVar : list) {
        el = ve.nextElement();
        intVar.domain.in(store.level, intVar, el, el);
      }
      a.domain.inLub(store.level, a, a.domain.glb());

    } else if (a.domain.lub().getSize() == list.length) {

      ValueEnumeration ve = a.domain.lub().valueEnumeration();
      int el;
      for (IntVar intVar : list) {
        el = ve.nextElement();
        intVar.domain.in(store.level, intVar, el, el);
      }
      a.domain.inGlb(store.level, a, a.domain.lub());

    } else {

      IntDomain glbA = a.domain.glb();
      IntDomain lubA = a.domain.lub();

      int sizeOfaGlb = glbA.getSize();
      int sizeOfaLub = lubA.getSize();

      // glbA, lubA => list[i]
      for (int i = 0; i < list.length; i++) {

        list[i].domain.in(store.level, list[i], lubA);

        int minValue = lubA.getElementAt(i);

        if (i >= list.length - sizeOfaGlb) {
          // -1 since indexing of arrays starts from 0.
          int minValueFromGlb = glbA.getElementAt(sizeOfaGlb - list.length + i);
          if (minValueFromGlb > minValue) {
            minValue = minValueFromGlb;
          }
        }

        list[i].domain.inMin(store.level, list[i], minValue);

        int maxValue = lubA.getElementAt(sizeOfaLub - list.length + i);

        if (i < sizeOfaGlb) {
          int maxValueFromGlb = glbA.getElementAt(i);
          if (maxValueFromGlb < maxValue) {
            maxValue = maxValueFromGlb;
          }
        }

        list[i].domain.inMax(store.level, list[i], maxValue);
      }

      IntDomain lubFromList = list[0].domain.cloneLight();
      for (int i = 0; i < list.length; i++) {
        if (list[i].singleton()) {
          a.domain.inGlb(store.level, a, list[i].value());
        }
        if (i > 0) {
          lubFromList.unionAdapt(list[i].domain);
        }
      }
      a.domain.inLub(store.level, a, lubFromList);
    }
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {

    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }

    if (v == a) {
      return SetDomain.ANY;
    } else {
      return IntDomain.ANY;
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise version exist.");
  }

  @Override
  public boolean satisfied() {

    if (!grounded()) {
      return false;
    }

    if (a.domain.glb().getSize() == list.length) {

      ValueEnumeration ve = a.domain.glb().valueEnumeration();

      for (IntVar intVar : list) {
        if (ve.nextElement() != intVar.value()) {
          return false;
        }
      }

      return true;

    } else {
      return false;
    }
  }

  @Override
  public String toString() {

    StringBuilder ret = new StringBuilder(id());
    ret.append(" : Match(").append(a).append(", [ ");
    for (Var fdv : list) {
      ret.append(fdv).append(" ");
    }
    ret.append("] )");
    return ret.toString();
  }
}
