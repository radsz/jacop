/*
 * ProgressionGapIndomain.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.fz;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Random;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.constraints.ProgressionTilingDetector.Tiling;
import org.jacop.search.Indomain;

/**
 * The value of a gap in the search of a tiling by arithmetic progressions: a random value among
 * those that place every term of the progression on a value its domain still has, once the start is
 * fixed. The linear definitions of the terms are bounds consistent, so the gap keeps values that
 * put a term on a covered cell, and each of them would cost a failed node (XCSP3
 * PerfectRythmicTiling: most random gaps). Without such a value, or with the start not fixed, a
 * random value of the domain.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ProgressionGapIndomain implements Indomain<IntVar> {

  private final Map<IntVar, IntVar[]> positions = new IdentityHashMap<>();

  private final Random random = Store.getRandom();

  private int[] candidates = new int[16];

  /**
   * It creates the value choice for the gaps of a tiling.
   *
   * @param tiling the tiling.
   */
  ProgressionGapIndomain(Tiling tiling) {
    for (int i = 0; i < tiling.gaps().length; i++) {
      positions.put(tiling.gaps()[i], tiling.positions()[i]);
    }
  }

  @Override
  public int indomain(IntVar gap) {
    IntDomain dom = gap.dom();
    IntVar[] p = positions.get(gap);
    int count = 0;
    if (p != null && p[0].singleton()) {
      int start = p[0].value();
      for (ValueEnumeration e = dom.valueEnumeration(); e.hasMoreElements(); ) {
        int d = e.nextElement();
        if (fits(p, start, d)) {
          if (count == candidates.length) {
            candidates = Arrays.copyOf(candidates, 2 * count);
          }
          candidates[count++] = d;
        }
      }
    }
    if (count > 0) {
      return candidates[random.nextInt(count)];
    }
    int value = random.nextInt(dom.getSize());
    for (ValueEnumeration e = dom.valueEnumeration(); ; ) {
      int d = e.nextElement();
      if (value-- == 0) {
        return d;
      }
    }
  }

  private static boolean fits(IntVar[] p, int start, int gap) {
    for (int j = 1; j < p.length; j++) {
      long v = start + (long) j * gap;
      if (v > Integer.MAX_VALUE || !p[j].domain.contains((int) v)) {
        return false;
      }
    }
    return true;
  }
}
