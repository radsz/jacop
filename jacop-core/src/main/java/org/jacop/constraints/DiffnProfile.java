/*
 * DiffnProfile.java
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

import java.io.Serial;
import java.util.List;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntDomain;

/**
 * Defines a basic data structure to keep the profile for the diff2/1 constraints. It consists of
 * ordered pair of time points and the current value.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
class DiffnProfile extends Profile {

  static final boolean TRACE = false;
  static boolean traceOn = TRACE;
  @Serial private static final long serialVersionUID = 8683452581100000011L;

  DiffnProfile() {}

  void make(int i, int j, Rectangle r, List<Rectangle> rs) {

    clear();
    maxProfileItemHeight = 0;
    IntDomain rOriginDom = r.origin[i].dom();
    IntDomain rLengthDom = r.length[i].dom();
    int rOriginMin = rOriginDom.min();
    int rOriginMax = rOriginDom.max();
    int rLengthMax = rLengthDom.max();
    IntRectangle iR = new IntRectangle(r.dim);

    for (Rectangle t : rs) {
      IntDomain tOriginDom = t.origin[i].dom();
      if (t != r
          && tOriginDom.min() >= rOriginMin
          && tOriginDom.max() + t.length[i].max() <= rOriginMax + rLengthMax) {
        iR.dim = 0;
        if (t.minUse(i, iR)) {
          if (traceOn) {
            log.debug(
                "Update profile [{}..{})={}",
                iR.origins[j],
                iR.origins[j] + iR.lengths[j],
                t.length(i).min());
          }
          addToProfile(iR.origins[j], iR.origins[j] + iR.lengths[j], t.length[i].min());
        }
      }
    }
  }
}
