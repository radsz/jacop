/*
 * ProfileItem.java
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

import lombok.Getter;
import lombok.NoArgsConstructor;
import lombok.Setter;

/**
 * Defines a basic structure used to update profile for cumulative constraint. It consists if to
 * time-points and a value denoting the interval [a, b) (a belongs to it nad b does not) and the
 * value.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@NoArgsConstructor
public class ProfileItem {

  /** It specifies the starting point of the profile item. */
  @Getter @Setter public int min = -1;

  /** It specifies the ending point of the profile item. */
  @Getter @Setter public int max = -1;

  /** It specifies the amount by which this profile item contributes in the profile. */
  @Getter @Setter public int value = -1;

  @Setter short type = Profile.CUMUL;

  /**
   * It constructs a profile item which spans over interval (a, b) with a given amount specified by
   * val.
   *
   * @param a starting point of the profile item.
   * @param b ending point of the profile item.
   * @param val the contribution of the item towards the profile.
   */
  public ProfileItem(int a, int b, int val) {
    min = a;
    max = b;
    value = val;
  }

  /**
   * It constructs the profile item with a given type.
   *
   * @param type it specifies the type of the profile item.
   */
  public ProfileItem(short type) {
    this.type = type;
  }

  /**
   * It constructs a profile item of a given type spanning across the given interval and
   * contributing a given amount towards the profile.
   *
   * @param type it specifies the type of the profile item.
   * @param a it specifies the starting point of the profile item.
   * @param b it specifies the ending point of the profile item.
   * @param val it specifies how much this profile item contributes in the profile.
   */
  public ProfileItem(short type, int a, int b, int val) {
    this.type = type;
    min = a;
    max = b;
    value = val;
  }

  /**
   * Computes the combined value when two profile items overlap.
   *
   * @param aValue the value from the other profile item
   * @return the combined value
   */
  protected int computeOverlapValue(int aValue) {
    return type == Profile.CUMUL ? aValue + value : Math.max(aValue, value);
  }

  /**
   * It compute the overlap with the specified profile item. The results are given as profile items
   * too.
   *
   * @param a the object for which the overlap with current object is being computed.
   * @param left the left part of this profile item which is not being overlapped.
   * @param overlap the overlapped part.
   * @param right the right part of this profile item which is not being overlapped.
   */
  public void overlap(ProfileItem a, ProfileItem left, ProfileItem overlap, ProfileItem right) {
    overlapInternal(a, left, overlap, right);
  }

  /**
   * Internal implementation of overlap computation with the common structural logic.
   *
   * @param a the object for which the overlap with current object is being computed.
   * @param left the left part of this profile item which is not being overlapped.
   * @param overlap the overlapped part.
   * @param right the right part of this profile item which is not being overlapped.
   */
  protected void overlapInternal(
      ProfileItem a, ProfileItem left, ProfileItem overlap, ProfileItem right) {
    if (a.min == min) {
      overlapWhenAMinEqualsMin(a, overlap, right);
    } else if (a.min < min) {
      overlapWhenAMinLessThanMin(a, left, overlap, right);
    } else {
      overlapWhenAMinGreaterThanMin(a, left, overlap, right);
    }
  }

  private void overlapWhenAMinEqualsMin(ProfileItem a, ProfileItem overlap, ProfileItem right) {
    if (a.max < max) {
      if (min != a.max) {
        overlap.set(min, a.max, computeOverlapValue(a.value));
      }
      right.set(a.max, max, value);
    } else {
      overlap.set(min, max, computeOverlapValue(a.value));
      if (max != a.max) {
        right.set(max, a.max, a.value);
      }
    }
  }

  private void overlapWhenAMinLessThanMin(
      ProfileItem a, ProfileItem left, ProfileItem overlap, ProfileItem right) {
    left.set(a.min, min, a.value);
    if (a.max == max) {
      overlap.set(min, max, computeOverlapValue(a.value));
    } else if (a.max < max) {
      if (min != a.max) {
        overlap.set(min, a.max, computeOverlapValue(a.value));
      }
      right.set(a.max, max, value);
    } else {
      overlap.set(min, max, computeOverlapValue(a.value));
      if (max != a.max) {
        right.set(max, a.max, a.value);
      }
    }
  }

  private void overlapWhenAMinGreaterThanMin(
      ProfileItem a, ProfileItem left, ProfileItem overlap, ProfileItem right) {
    left.set(min, a.min, value);
    if (a.max == max) {
      overlap.set(a.min, a.max, computeOverlapValue(a.value));
    } else if (a.max < max) {
      overlap.set(a.min, a.max, computeOverlapValue(a.value));
      right.set(a.max, max, value);
    } else {
      overlap.set(a.min, max, computeOverlapValue(a.value));
      if (max != a.max) {
        right.set(max, a.max, a.value);
      }
    }
  }

  /**
   * It sets the attributes of the profile item.
   *
   * @param a the starting point of the profile item.
   * @param b the ending point of the profile item.
   * @param val the amount contributed towards a profile by this profile item.
   */
  public void set(int a, int b, int val) {
    min = a;
    max = b;
    value = val;
  }

  private void subtractWhenMinLessThanA(ProfileItem a, ProfileItem left, ProfileItem right) {
    if (max <= a.min) {
      left.set(min, max, value);
    } else if (max <= a.max) {
      left.set(min, a.min, value);
    } else {
      right.set(a.max, max, value);
      left.set(min, a.min, value);
    }
  }

  private void subtractWhenMinGreaterThanA(ProfileItem a, ProfileItem right) {
    if (min <= a.max) {
      if (max > a.max) {
        right.set(a.max, max, value);
      }
    } else {
      right.set(min, max, value);
    }
  }

  /**
   * It computes subtraction of a given item and returns the result.
   *
   * @param a the item being subtracted from this profile item.
   * @param left the left part remaining after subtraction.
   * @param right the right part remaining after subtraction.
   */
  public void subtract(ProfileItem a, ProfileItem left, ProfileItem right) {

    if (min == a.min) {
      if (max > a.max) {
        right.set(a.max, max, value);
      }
      return;
    }
    if (min < a.min) {
      subtractWhenMinLessThanA(a, left, right);
    } else {
      subtractWhenMinGreaterThanA(a, right);
    }
  }

  @Override
  public String toString() {
    return "[" + min + ".." + max + ") = " + value;
  }
}
