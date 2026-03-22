/*
 * ChannelIntSet.java
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * Channel constraint requires that array of int variables x and array of set variables y are
 * related such that (x[i] = j) {@literal <->} (i in s[j]). Indexes start form 0, both for integer
 * and set variables, by default. To define other starting index use offset definitions.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ChannelIntSet extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] x;
  final SetVar[] s;
  final int ni;
  final int ns;
  final int offsetInt;
  final int offsetSet;

  boolean firstConsistencyCheck = true;

  /**
   * It constructs a Channel constraint.
   *
   * @param x array of integer variables.
   * @param s array of set variables.
   * @param offsetInt offset for integer variables array.
   * @param offsetSet offset for set variables array.
   */
  public ChannelIntSet(IntVar[] x, SetVar[] s, int offsetInt, int offsetSet) {

    checkInputForNullness(new String[] {"x", "x"}, new Object[] {x, s});

    numberId = idNumber.incrementAndGet();

    this.x = x;
    ni = x.length;
    this.s = s;
    ns = s.length;
    this.offsetInt = offsetInt;
    this.offsetSet = offsetSet;

    setScope(Stream.concat(Arrays.stream(x), Arrays.stream(s)));
  }

  /**
   * It constructs a Channel constraint.
   *
   * @param x array of integer variables.
   * @param s array of set variables.
   */
  public ChannelIntSet(IntVar[] x, SetVar[] s) {
    this(x, s, 0, 0);
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      doFirstConsistencyCheck(store);
      firstConsistencyCheck = false;
    }

    propagateFromIntVariables(store);
    propagateFromSetVariables(store);
  }

  private void doFirstConsistencyCheck(Store store) {
    for (int i = 0; i < ni; i++) {
      x[i].domain.in(store.level, x[i], offsetInt, ns - 1 + offsetSet);
    }

    for (int i = 0; i < ns; i++) {
      s[i].domain.inLub(store.level, s[i], new IntervalDomain(offsetSet, ni - 1 + offsetInt));
    }
  }

  private void propagateFromIntVariables(Store store) {
    for (int i = 0; i < ni; i++) {
      IntDomain vs = new IntervalDomain(5);
      for (ValueEnumeration e = x[i].domain.valueEnumeration(); e.hasMoreElements(); ) {
        int xd = e.nextElement();
        if (s[xd - offsetInt].dom().lub().contains(i + offsetInt)) {
          vs.unionAdapt(xd);
        }
      }

      x[i].domain.in(store.level, x[i], vs);

      if (x[i].singleton()) {
        IntDomain glb = new IntervalDomain(i + offsetInt, i + offsetInt);
        s[x[i].value() - offsetInt].dom().inGlb(store.level, s[x[i].value() - offsetInt], glb);
      }
    }
  }

  private void propagateFromSetVariables(Store store) {
    for (int i = 0; i < ns; i++) {
      IntDomain lub = s[i].dom().lub();
      IntDomain vs = new IntervalDomain(5);
      for (ValueEnumeration e = lub.valueEnumeration(); e.hasMoreElements(); ) {
        int se = e.nextElement();
        if (se >= offsetSet
            && se <= ni + offsetInt
            && x[se - offsetSet].domain.contains(i + offsetSet)) {
          vs.unionAdapt(se);
        }
      }

      s[i].domain.inLub(store.level, s[i], vs);

      IntDomain glb = s[i].dom().glb();
      for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
        int se = e.nextElement();
        x[se - offsetSet].domain.in(store.level, x[se - offsetSet], i + offsetSet, i + offsetSet);
      }
    }
  }

  @Override
  public boolean satisfied() {

    for (int i = 0; i < ni; i++) {
      if (x[i].singleton()) {
        int v = x[i].value();
        if (v < offsetInt
            || v >= ns + offsetInt
            || !s[v - offsetInt].dom().lub().contains(i + offsetSet)) {
          return false;
        }
      }
    }
    for (int i = 0; i < ns; i++) {
      IntDomain glb = s[i].dom().glb();
      for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
        int se = e.nextElement();
        if (se < offsetSet
            || se >= ni + offsetSet
            || !x[se - offsetSet].domain.contains(i + offsetInt)) {
          return false;
        }
      }
    }

    return allGround();
  }

  boolean allGround() {
    for (int i = 0; i < ni; i++) {
      if (!x[i].singleton()) {
        return false;
      }
    }
    for (int i = 0; i < ns; i++) {
      if (!s[i].singleton()) {
        return false;
      }
    }

    return true;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    Integer possibleEvent = getConsistencyPruningEventFromMap(v);
    if (possibleEvent != null) {
      return possibleEvent;
    }

    if (v instanceof IntVar) {
      return IntDomain.ANY;
    } else {
      return SetDomain.ANY;
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise variant exists.");
  }

  @Override
  public String toString() {

    return id()
        + " : ChannelIntSet("
        + Arrays.asList(x)
        + ", "
        + Arrays.asList(s)
        + ", "
        + offsetInt
        + ", "
        + offsetSet
        + ")";
  }
}
