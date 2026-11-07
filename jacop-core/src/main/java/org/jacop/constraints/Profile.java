/*
 * Profile.java
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
import lombok.EqualsAndHashCode;
import lombok.extern.slf4j.Slf4j;

/**
 * Defines a basic data structure to keep the profile for the diffn/1 and cumulative/4 constraints.
 * It consists of ordered pair of time points and the current value.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
@EqualsAndHashCode(callSuper = true)
public class Profile extends ArrayList<ProfileItem> {

  static final boolean TRACE_ENABLED = false;
  static final int CUMUL = 0;
  static final int DIFFN = 1;
  @Serial private static final long serialVersionUID = 8683452581100000012L;
  protected int maxProfileItemHeight;

  short type = CUMUL;

  /** It constructs the prophet file. */
  public Profile() {}

  /**
   * It constructs the profile of a given type (e.g. for cumulative).
   *
   * @param type type of the profile (CUMUL=0, DIFFN=1)
   */
  public Profile(short type) {
    this.type = type;
  }

  /**
   * It adds given amount (val) to the profile between a and b.
   *
   * @param a the minimum range at which it is being added.
   * @param b the maximum range at which it is being added.
   * @param val the amount by which the profiles is updated.
   */
  public void addToProfile(int a, int b, int val) {
    if (size() == 0) {
      addToEmptyProfile(a, b, val);
      return;
    }
    int i = 0;
    boolean notFound = true;
    while (i < size() && notFound) {
      ProfileItem p = get(i);
      if (b <= p.min) {
        notFound = false;
        i = handleBeforeCurrent(a, b, val, i, p);
      } else if (p.max <= a) {
        int[] result = handleAfterCurrent(a, b, val, i, p);
        i = result[0];
        notFound = result[1] != 0;
      } else {
        handleOverlapAt(i, a, b, val, p);
        notFound = false;
      }
    }
  }

  private void addToEmptyProfile(int a, int b, int val) {
    if (TRACE_ENABLED) {
      log.debug("1. Add [{}..{})={} at position 0", a, b, val);
    }
    add(new ProfileItem(type, a, b, val));
    if (maxProfileItemHeight < val) {
      maxProfileItemHeight = val;
    }
  }

  private int handleBeforeCurrent(int a, int b, int val, int i, ProfileItem p) {
    if (a == b) {
      i++;
      if (maxProfileItemHeight < val) {
        maxProfileItemHeight = val;
      }
      return i;
    }
    if (b == p.min && val == p.value) {
      if (TRACE_ENABLED) {
        log.debug("2a. Change [{}..{})={} at position {}", a, p.max, val, i);
      }
      p.min = a;
      if (i > 0) {
        ProfileItem previousP = get(i - 1);
        if (a == previousP.max && previousP.value == val) {
          p.min = previousP.min;
          remove(i - 1);
          i--;
        }
      }
    } else if (i > 0) {
      ProfileItem prev = get(i - 1);
      if (a == prev.max && val == prev.value) {
        prev.max = b;
      } else {
        add(i, new ProfileItem(type, a, b, val));
      }
    } else {
      if (TRACE_ENABLED) {
        log.debug("2b. Add [{}..{})={} at position {}", a, b, val, i);
      }
      add(i, new ProfileItem(type, a, b, val));
    }
    i++;
    if (maxProfileItemHeight < val) {
      maxProfileItemHeight = val;
    }
    return i;
  }

  private int[] handleAfterCurrent(int a, int b, int val, int i, ProfileItem p) {
    if (i != size() - 1) {
      return new int[] {i + 1, 1};
    }
    if (a == b) {
      return new int[] {i + 1, 0};
    }
    if (p.max == a && val == p.value) {
      if (TRACE_ENABLED) {
        log.debug("3a. Change [{}..{})={} at position {}", p.min, b, val, i);
      }
      p.max = b;
    } else {
      if (TRACE_ENABLED) {
        log.debug("3b. Add [{}..{})={} at position {}", a, b, val, i + 1);
      }
      add(i + 1, new ProfileItem(type, a, b, val));
    }
    if (maxProfileItemHeight < val) {
      maxProfileItemHeight = val;
    }
    return new int[] {i + 1, 0};
  }

  private void handleOverlapAt(int i, int a, int b, int val, ProfileItem p) {
    ProfileItem new1 = new ProfileItem(type);
    ProfileItem new2 = new ProfileItem(type);
    ProfileItem new3 = new ProfileItem(type);
    p.overlap(new ProfileItem(type, a, b, val), new1, new2, new3);

    if (TRACE_ENABLED) {
      log.debug(
          "Overlap of [{}..{})={} and {}\nResult = {}, {}, {}", a, b, val, p, new1, new2, new3);
    }

    remove(i);
    i = addOverlapPart(i, new1, val);
    i = addOverlapPart(i, new2, val);
    if (new3.min != -1 && new3.min != new3.max) {
      addToProfile(new3.min, new3.max, new3.value);
    }
  }

  private int addOverlapPart(int i, ProfileItem part, int val) {
    if (part.min == -1) {
      return i;
    }
    ProfileItem previous = (i != 0) ? get(i - 1) : new ProfileItem(type);
    if (previous.max == part.min && previous.value == part.value) {
      if (TRACE_ENABLED) {
        log.debug("4a/5a. Change [{}..{})={} at position {}", previous.min, part.max, val, i);
      }
      previous.setMax(part.max);
    } else {
      if (TRACE_ENABLED) {
        log.debug("4b/5b. Adding {}", part);
      }
      add(i, part);
      if (maxProfileItemHeight < part.value) {
        maxProfileItemHeight = part.value;
      }
      i++;
    }
    return i;
  }

  /**
   * It returns the max height of the profile item encountered in the profile.
   *
   * @return the max height.
   */
  public int max() {
    return maxProfileItemHeight;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder("[");

    for (Iterator<ProfileItem> e = iterator(); e.hasNext(); ) {
      result.append(e.next().toString());
      if (e.hasNext()) {
        result.append(", ");
      }
    }
    result.append("]");
    return result.toString();
  }
}
