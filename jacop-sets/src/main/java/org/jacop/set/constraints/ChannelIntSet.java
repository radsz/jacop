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

  /**
   * It constructs a Channel constraint.
   *
   * @param x array of integer variables.
   * @param s array of set variables.
   * @param offsetInt the index of x[0]: the sets hold the indexes offsetInt..offsetInt + x.length -
   *     1.
   * @param offsetSet the index of s[0]: the integer variables take the values offsetSet..offsetSet
   *     + s.length - 1.
   */
  public ChannelIntSet(IntVar[] x, SetVar[] s, int offsetInt, int offsetSet) {

    checkInputForNullness(new String[] {"x", "s"}, new Object[] {x, s});
    checkInputForNullness("x", x);
    checkInputForNullness("s", s);

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

    // The store does not re-queue this constraint for its own changes, so iterate to a fixpoint.
    do {
      store.propagationHasOccurred = false;
      propagateFromIntVariables(store);
      propagateFromSetVariables(store);
    } while (store.propagationHasOccurred);
  }

  /** Keeps the values j of x[i] whose set s[j - offsetSet] can hold i + offsetInt. */
  private void propagateFromIntVariables(Store store) {
    for (int i = 0; i < ni; i++) {
      IntDomain vs = new IntervalDomain(5);
      for (ValueEnumeration e = x[i].domain.valueEnumeration(); e.hasMoreElements(); ) {
        int xd = e.nextElement();
        if (xd >= offsetSet
            && xd < ns + offsetSet
            && s[xd - offsetSet].dom().lub().contains(i + offsetInt)) {
          vs.unionAdapt(xd);
        }
      }

      x[i].domain.in(store.level, x[i], vs);

      if (x[i].singleton()) {
        SetVar set = s[x[i].value() - offsetSet];
        set.domain.inGlb(store.level, set, new IntervalDomain(i + offsetInt, i + offsetInt));
      }
    }
  }

  /** Keeps the elements e of s[j] whose variable x[e - offsetInt] can be j + offsetSet. */
  private void propagateFromSetVariables(Store store) {
    for (int j = 0; j < ns; j++) {
      IntDomain lub = s[j].dom().lub();
      IntDomain vs = new IntervalDomain(5);
      for (ValueEnumeration e = lub.valueEnumeration(); e.hasMoreElements(); ) {
        int se = e.nextElement();
        if (se >= offsetInt
            && se < ni + offsetInt
            && x[se - offsetInt].domain.contains(j + offsetSet)) {
          vs.unionAdapt(se);
        }
      }

      s[j].domain.inLub(store.level, s[j], vs);

      IntDomain glb = s[j].dom().glb();
      for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
        IntVar v = x[e.nextElement() - offsetInt];
        v.domain.in(store.level, v, j + offsetSet, j + offsetSet);
      }
    }
  }

  @Override
  public boolean satisfied() {

    for (int i = 0; i < ni; i++) {
      if (x[i].singleton()) {
        int v = x[i].value();
        if (v < offsetSet
            || v >= ns + offsetSet
            || !s[v - offsetSet].dom().lub().contains(i + offsetInt)) {
          return false;
        }
      }
    }
    for (int j = 0; j < ns; j++) {
      IntDomain glb = s[j].dom().glb();
      for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
        int se = e.nextElement();
        if (se < offsetInt
            || se >= ni + offsetInt
            || !x[se - offsetInt].domain.contains(j + offsetSet)) {
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
