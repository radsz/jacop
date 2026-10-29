/*
 * ElementExplanation.java
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

package org.jacop.lcg;

import org.jacop.core.IntVar;

/**
 * Explanations of {@code list[index - offset - 1] = value} over a list of constants: an atom of the
 * value or of the index holds because every position that would violate it is excluded, by the
 * index or by the value.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ElementExplanation {

  private ElementExplanation() {}

  /**
   * Adds to {@code out} the reason of an entry of the index or the value.
   *
   * @param trail the trail
   * @param entry the entry
   * @param index the index variable
   * @param list the constants
   * @param value the value variable, not the index
   * @param offset the index offset: position j is index value j + 1 + offset
   * @param out where the reason entries are added
   * @return false when the entry is of neither variable, or a position is not excluded before it
   */
  public static boolean explain(
      AtomicTrail trail,
      int entry,
      IntVar index,
      int[] list,
      IntVar value,
      int offset,
      EntryList out) {
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    int a = trail.value(entry);
    if (y == index
        && (trail.rootDomain(index).min() < 1 + offset
            || trail.rootDomain(index).max() > list.length + offset)) {
      return false; // index values off the list would need their own reasons
    }
    for (int j = 0; j < list.length; j++) {
      int u = y == value ? list[j] : j + 1 + offset;
      if (violates(kind, a, u) && !excluded(trail, j, entry, index, list, value, offset, out)) {
        return false;
      }
    }
    return y == value || y == index;
  }

  /**
   * Adds to {@code out} the reason of a failure: every position is excluded, by the index or by the
   * value. Of the two choices, one atom per excluded index value first or one per excluded constant
   * first, it keeps the one with fewer distinct atoms: a constant out of the value's domain
   * excludes every position that holds it, so a long list of few constants (a dictionary of words
   * over an alphabet) needs a few atoms of the value instead of one atom of the index per position.
   *
   * @param trail the trail
   * @param index the index variable
   * @param list the constants
   * @param value the value variable, not the index
   * @param offset the index offset
   * @param out where the reason entries are added
   * @return false when a position is not excluded now
   */
  public static boolean explainFailure(
      AtomicTrail trail, IntVar index, int[] list, IntVar value, int offset, EntryList out) {
    int now = trail.size();
    int mark = out.size();
    for (int j = 0; j < list.length; j++) {
      if (!excluded(trail, j, now, index, list, value, offset, out)) {
        out.truncate(mark);
        return false;
      }
    }
    out.sortUnique(mark);
    int byIndex = out.size() - mark;
    int second = out.size();
    for (int j = 0; j < list.length; j++) {
      if (!trail.excludedBefore(value, list[j], now, out)
          && !trail.excludedBefore(index, j + 1 + offset, now, out)) {
        out.truncate(second);
        return true; // cannot happen: the first pass excluded every position
      }
    }
    out.sortUnique(second);
    int byValue = out.size() - second;
    if (byValue < byIndex) {
      for (int k = 0; k < byValue; k++) {
        out.set(mark + k, out.get(second + k));
      }
      out.truncate(mark + byValue);
    } else {
      out.truncate(second);
    }
    return true;
  }

  // whether position j was excluded before a trail position, adding the atom that excluded it
  private static boolean excluded(
      AtomicTrail trail,
      int j,
      int position,
      IntVar index,
      int[] list,
      IntVar value,
      int offset,
      EntryList out) {
    return trail.excludedBefore(index, j + 1 + offset, position, out)
        || trail.excludedBefore(value, list[j], position, out);
  }

  // whether value u falsifies the atom (kind, a)
  private static boolean violates(int kind, int a, int u) {
    return switch (kind) {
      case AtomicTrail.GE -> u < a;
      case AtomicTrail.LE -> u > a;
      default -> u == a;
    };
  }
}
