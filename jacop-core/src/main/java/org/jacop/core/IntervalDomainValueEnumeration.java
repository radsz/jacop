/*
 * IntervalDomainValueEnumeration.java
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

package org.jacop.core;

import java.util.NoSuchElementException;

/**
 * Defines a methods for enumerating values contain in the domain.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class IntervalDomainValueEnumeration extends ValueEnumeration {

  final IntervalDomain domain;
  int current;

  /** The maximum of the current interval. */
  int currentMax;

  /** False once all values have been returned. */
  boolean more;

  int intervalNo;

  int maxIntervalNo;

  /**
   * It create an enumeration for a given domain.
   *
   * @param dom domain for which value enumeration is created.
   */
  public IntervalDomainValueEnumeration(IntervalDomain dom) {
    domain = dom;
    maxIntervalNo = domain.size - 1;
    if (maxIntervalNo >= 0) {
      current = domain.bounds[2 * intervalNo];
      currentMax = domain.bounds[2 * intervalNo + 1];
      more = true;
    }
  }

  @Override
  public boolean hasMoreElements() {
    return more;
  }

  @Override
  public int nextElement() {

    if (!more) {
      throw new NoSuchElementException("No more values in the domain.");
    }

    int v;

    if (current < currentMax) {
      v = current;
      current++;
      return v;
    } else {

      if (intervalNo < maxIntervalNo) {
        intervalNo++;
        v = current;
        current = domain.bounds[2 * intervalNo];
        currentMax = domain.bounds[2 * intervalNo + 1];
        return v;
      } else {
        more = false;
        return current;
      }
    }
  }

  @Override
  public void domainHasChanged() {
    intervalNo = domain.intervalNo(current);
    maxIntervalNo = domain.size - 1;
    if (intervalNo == -1) {

      for (int j = 0; j <= maxIntervalNo; j++) {
        if (domain.bounds[2 * j] > current) {
          current = domain.bounds[2 * j];
          currentMax = domain.bounds[2 * j + 1];
          intervalNo = j;
          more = true;
          return;
        }
      }

      more = false;
      return;
    }

    if (more) {
      currentMax = domain.bounds[2 * intervalNo + 1];
    }
  }
}
