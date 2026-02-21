/*
 * ProfileConditional.java
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
import java.util.ArrayList;
import java.util.Iterator;
import lombok.extern.slf4j.Slf4j;

/**
 * Defines a basic data structure to keep the profile for the disjointConditonal/2.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
class ProfileConditional extends ArrayList<ProfileItemCondition> {

  static final boolean TRACE_ENABLED = false;
  @Serial private static final long serialVersionUID = 8683452581100000010L;
  int maxProfile;

  ProfileConditional() {}

  void addToProfile(int index, int a, int b, int val, ExclusiveList exList) {
    if (TRACE_ENABLED) {
      log.debug("{}  --------------------------", index);
      log.debug("{}", exList);
    }
    if (size() == 0) {
      addToEmptyProfileConditional(index, a, b, val);
    } else {
      addToNonEmptyProfile(index, a, b, val, exList);
    }
    if (TRACE_ENABLED) {
      log.debug("########\n{}", this);
    }
  }

  private void addToEmptyProfileConditional(int index, int a, int b, int val) {
    if (TRACE_ENABLED) {
      log.debug("1. Add [{}..{})={} at position 0", a, b, val);
    }
    int[] r = {index, val};
    add(new ProfileItemCondition(a, b, val, r));
    if (maxProfile < val) {
      maxProfile = val;
    }
  }

  private void addToNonEmptyProfile(int index, int a, int b, int val, ExclusiveList exList) {
    int i = 0;
    boolean notFound = true;
    while (i < size() && notFound) {
      ProfileItemCondition p = get(i);
      if (b <= p.min) {
        i = handleInsertBeforeCurrent(index, a, b, val, i, p);
        notFound = false;
      } else if (p.max <= a) {
        InsertResult res = handleInsertAfterCurrent(index, a, b, val, i);
        i = res.newI();
        notFound = res.notFound();
      } else {
        i = handleOverlapAt(i, index, a, b, val, p, exList);
        notFound = false;
      }
    }
  }

  private static final class InsertResult {
    final int newI;
    final boolean notFound;

    InsertResult(int newI, boolean notFound) {
      this.newI = newI;
      this.notFound = notFound;
    }

    int newI() {
      return newI;
    }

    boolean notFound() {
      return notFound;
    }
  }

  private int handleInsertBeforeCurrent(
      int index, int a, int b, int val, int i, ProfileItemCondition p) {
    if (a != b) {
      if (b == p.min && val == p.value) {
        if (TRACE_ENABLED) {
          log.debug("2a. Change [{}..{})={} at position {}", a, p.max, val, i);
        }
        int[] r = {index, val};
        add(i + 1, new ProfileItemCondition(a, b, val, r));
      } else {
        if (i > 0) {
          int[] r = {index, val};
          add(i, new ProfileItemCondition(a, b, val, r));
        } else {
          if (TRACE_ENABLED) {
            log.debug("2b. Add [{}..{})={} at position {}", a, b, val, i);
          }
          int[] r = {index, val};
          add(i, new ProfileItemCondition(a, b, val, r));
        }
      }
    }
    if (maxProfile < val) {
      maxProfile = val;
    }
    return i + 1;
  }

  private InsertResult handleInsertAfterCurrent(int index, int a, int b, int val, int i) {
    if (i == size() - 1) {
      if (a != b) {
        if (TRACE_ENABLED) {
          log.debug("3. Add [{}..{})={} at position {}", a, b, val, i + 1);
        }
        int[] r = {index, val};
        add(i + 1, new ProfileItemCondition(a, b, val, r));
      }
      return new InsertResult(i + 1, false);
    }
    return new InsertResult(i + 1, true);
  }

  private int handleOverlapAt(
      int i, int index, int a, int b, int val, ProfileItemCondition p, ExclusiveList exList) {
    ProfileItemCondition new1 = new ProfileItemCondition();
    ProfileItemCondition new2 = new ProfileItemCondition();
    ProfileItemCondition new3 = new ProfileItemCondition();
    int[] r = {index, val};
    if (TRACE_ENABLED) {
      log.debug("Overlap of [{}..{})={}, [{}]  and {}", a, b, val, index, p);
    }
    p.overlap(new ProfileItemCondition(a, b, val, r), new1, new2, new3, exList, r);
    if (TRACE_ENABLED) {
      log.debug("Result = {}, {}, {}", new1, new2, new3);
    }
    remove(i);
    i = addOverlapPart(i, new1, p, val);
    i = addOverlapPart(i, new2, null, val);
    if (new3.min != -1 && new3.min != new3.max) {
      if (new3.max == b) {
        addToProfile(index, new3.min, new3.max, val, exList);
      } else {
        add(i, new3);
      }
      i++;
    }
    return i;
  }

  private int addOverlapPart(int i, ProfileItemCondition part, ProfileItemCondition p, int val) {
    if (part.min == -1) {
      return i;
    }
    ProfileItemCondition previous = (i != 0) ? get(i - 1) : new ProfileItemCondition();
    if (previous.max == part.min && previous.value == part.value) {
      if (TRACE_ENABLED) {
        log.debug("4a/5a. Change [{}..{})={} at position {}", previous.min, part.max, val, i);
      }
      add(i, part);
    } else {
      if (TRACE_ENABLED) {
        log.debug("4b/5b. Adding {}", part);
      }
      if (p != null) {
        part.rectangles = p.rectangles;
      }
      add(i, part);
      if (maxProfile < part.value) {
        maxProfile = part.value;
      }
    }
    return i + 1;
  }

  int max() {
    return maxProfile;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder("[");

    for (Iterator<ProfileItemCondition> e = iterator(); e.hasNext(); ) {

      result.append(e.next());
      if (e.hasNext()) {
        result.append(", ");
      }
    }

    result.append("]");

    return result.toString();
  }
}
