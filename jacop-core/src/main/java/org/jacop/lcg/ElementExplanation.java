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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;

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
   * Writes list[index - offset] = value as clauses over value literals: a position implies its
   * constant, a value of the value variable needs one of its positions, and the index is one of the
   * positions. Unit propagation on them removes what the element propagators remove, so every
   * explanation of this class, and the generic reason, follows from them.
   *
   * @param model the model
   * @param index the index variable
   * @param list the constants
   * @param value the value variable, not the index
   * @param offset the index offset
   */
  public static void encode(PbModel model, IntVar index, int[] list, IntVar value, int offset) {
    Map<Integer, List<String>> positions = new HashMap<>();
    String[] any = new String[list.length];
    for (int j = 0; j < list.length; j++) {
      String at = model.equalTo(index, j + 1 + offset);
      any[j] = at;
      model.clause(PbModel.not(at), model.equalTo(value, list[j]));
      positions.computeIfAbsent(list[j], k -> new ArrayList<>()).add(at);
    }
    model.clause(any);
    IntDomain d = model.domain(value);
    for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
      int u = e.nextElement();
      List<String> at = positions.getOrDefault(u, List.of());
      String[] c = new String[at.size() + 1];
      c[0] = PbModel.not(model.equalTo(value, u));
      for (int k = 0; k < at.size(); k++) {
        c[k + 1] = at.get(k);
      }
      model.clause(c);
    }
  }

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
    if (y != value && y != index) {
      return false;
    }
    int mark = out.size();
    for (int j = 0; j < list.length; j++) {
      int u = y == value ? list[j] : j + 1 + offset;
      if (violates(kind, a, u) && !excluded(trail, j, entry, index, list, value, offset, out)) {
        return false;
      }
    }
    EntryList alt = trail.alternativeFor(entry);
    boolean shorter = ORDERS == SHORTER || AtomicTrail.style(AtomicTrail.STYLE_ELEMENT_SHORTER);
    if ((ORDERS == INDEX_FIRST && !shorter) || (ORDERS == BOTH && alt == null)) {
      return true;
    }
    // the same positions excluded by the value first: a constant out of the value's domain
    // excludes every position holding it, so it can need fewer atoms
    out.sortUnique(mark);
    EntryList byValue = new EntryList();
    for (int j = 0; j < list.length; j++) {
      int u = y == value ? list[j] : j + 1 + offset;
      if (violates(kind, a, u)
          && !trail.excludedBefore(value, list[j], entry, byValue)
          && !trail.excludedBefore(index, j + 1 + offset, entry, byValue)) {
        return true;
      }
    }
    byValue.sortUnique(0);
    place(out, mark, byValue, alt);
    return true;
  }

  /** Reasons index first only (the default). */
  static final int INDEX_FIRST = 0;

  /** Reasons by the shorter of index first and value first. */
  static final int SHORTER = 1;

  /** Reasons index first, value first given as an alternative reason. */
  static final int BOTH = 2;

  /** Reasons by the shorter order, the longer one given as an alternative reason. */
  static final int SHORTER_BOTH = 3;

  /**
   * How reasons of index and value atoms are built: {@code -Djacop.lcg.elementOrders} = index
   * (default), shorter, both or shorterBoth. Failures always keep the shorter order; with both or
   * shorterBoth the longer one is the alternative.
   */
  static final int ORDERS =
      switch (System.getProperty("jacop.lcg.elementOrders", "index")) {
        case "shorter" -> SHORTER;
        case "both" -> BOTH;
        case "shorterBoth" -> SHORTER_BOTH;
        default -> INDEX_FIRST;
      };

  // with out[mark, size) the index-first reason, places the reason and the alternative by ORDERS
  private static void place(EntryList out, int mark, EntryList byValue, EntryList alt) {
    int byIndex = out.size() - mark;
    boolean valueShorter = byValue.size() < byIndex;
    boolean valueFirst =
        (ORDERS == SHORTER
                || ORDERS == SHORTER_BOTH
                || AtomicTrail.style(AtomicTrail.STYLE_ELEMENT_SHORTER))
            && valueShorter;
    boolean wantAlt = alt != null && (ORDERS == BOTH || ORDERS == SHORTER_BOTH);
    if (wantAlt) {
      if (valueFirst) {
        for (int k = mark; k < out.size(); k++) {
          alt.addFrom(out, k);
        }
      } else {
        for (int k = 0; k < byValue.size(); k++) {
          alt.addFrom(byValue, k);
        }
      }
    }
    if (valueFirst) {
      out.truncate(mark);
      for (int k = 0; k < byValue.size(); k++) {
        out.addFrom(byValue, k);
      }
    }
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
    EntryList alt =
        ORDERS == BOTH || ORDERS == SHORTER_BOTH ? trail.alternativeFor(AtomicTrail.FAILURE) : null;
    if (alt != null) {
      int from = byValue < byIndex ? mark : second;
      int to = byValue < byIndex ? second : out.size();
      for (int k = from; k < to; k++) {
        alt.addFrom(out, k);
      }
    }
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
