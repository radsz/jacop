/*
 * IndomainMiddle.java
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

package org.jacop.search;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;

/**
 * IndomainMiddle - implements enumeration method based on the selection of the middle value in the
 * domain of FD variable and then right and left values.
 *
 * @param <T> type of variable being used in search.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class IndomainMiddle<T extends IntVar> implements Indomain<T> {

  /** It creates Indomain heuristic which chooses the middle value. */
  public IndomainMiddle() {
    // Intentionally empty: default constructor requires no initialization.
  }

  /** It requires IntVar variable. */
  public int indomain(IntVar v) {

    if (ASSERTS_ENABLED && !(!v.singleton())) {
      throw new IllegalStateException(
          String.valueOf("indomain does not work with singleton variables."));
    }

    if (ASSERTS_ENABLED && !(v.dom().domainId() != IntDomain.BOUND_DOMAIN_ID)) {
      throw new IllegalStateException(String.valueOf("It is not possible to use BoundDomain"));
    }

    if (v.domain.domainId() == IntDomain.INTERVAL_DOMAIN_ID) {
      return indomainIntervalDomain((IntervalDomain) v.domain);
    }
    return indomainGeneric(v.dom());
  }

  private int indomainIntervalDomain(IntervalDomain domain) {
    int dMin = domain.min();
    int dMax = domain.max();
    if (domain.singleton()) {
      return dMin;
    }
    int middle = dMin + ((dMax - dMin) >> 1);
    if (domain.contains(middle)) {
      return middle;
    }
    int iBefore = 0;
    int iAfter = domain.size - 1;
    while (iBefore < domain.size && domain.intervals[iBefore].max() < middle) {
      iBefore++;
    }
    while (iAfter >= 0 && domain.intervals[iAfter].min() > middle) {
      iAfter--;
    }
    if (iBefore > iAfter) {
      return middle - domain.intervals[iAfter].max() > domain.intervals[iBefore].min() - middle
          ? domain.intervals[iBefore].min()
          : domain.intervals[iAfter].max();
    }
    return middle - domain.intervals[iBefore].max() > domain.intervals[iAfter].min() - middle
        ? domain.intervals[iAfter].min()
        : domain.intervals[iBefore].max();
  }

  private int indomainGeneric(IntDomain dom) {
    int dMin = dom.min();
    int dMax = dom.max();
    if (dom.singleton()) {
      return dMin;
    }
    int middle = dMin + ((dMax - dMin) >> 1);
    if (dom.contains(middle)) {
      return middle;
    }
    int iBefore = 0;
    int iAfter = dom.noIntervals() - 1;
    while (iBefore < dom.noIntervals() && dom.getInterval(iBefore).max() < middle) {
      iBefore++;
    }
    while (iAfter >= 0 && dom.getInterval(iAfter).min() > middle) {
      iAfter--;
    }
    if (iBefore > iAfter) {
      return middle - dom.getInterval(iAfter).max() > dom.getInterval(iBefore).min() - middle
          ? dom.getInterval(iBefore).min()
          : dom.getInterval(iAfter).max();
    }
    return middle - dom.getInterval(iBefore).max() > dom.getInterval(iAfter).min() - middle
        ? dom.getInterval(iAfter).min()
        : dom.getInterval(iBefore).max();
  }
}
