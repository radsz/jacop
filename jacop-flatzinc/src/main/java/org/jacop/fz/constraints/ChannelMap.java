/*
 * ChannelMap.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.XeqY;
import org.jacop.core.IntVar;

/**
 * It collects all int_eq_(reif|imp) constraint to create Channel(Reif|Imply) constraints, if
 * possible.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class ChannelMap {

  final Map<IntVar, Map<Integer, IntVar>> cs = new HashMap<>();

  final int minSize = 1;

  // (x, v, b) triples collected by add, so that callers can tell them apart from other
  // reifications of x = v that were not collected (for example bool_eq_reif).
  private final Set<Entry> collected = new HashSet<>();

  // the collected pairs (x, v) of each Boolean b
  private final Map<IntVar, List<Entry>> byBoolean = new HashMap<>();

  private record Entry(IntVar x, int v, IntVar b) {}

  final Support support;

  public ChannelMap(Support support) {
    this.support = support;
  }

  public void add(IntVar x, int v, IntVar b) {
    Map<Integer, IntVar> map = cs.get(x);

    if (map != null && map.get(v) != null && !mergesDuplicates()) {
      // not collected, so the constraint is posted on its own
      return;
    }
    Entry entry = new Entry(x, v, b);
    collected.add(entry);
    byBoolean.computeIfAbsent(b, k -> new ArrayList<>()).add(entry);

    if (map != null) {
      if (map.get(v) != null) {
        support.delayedConstraints.add(new XeqY(map.get(v), b));
      } else {
        map.put(v, b);
        cs.put(x, map);
      }
    } else {
      map = new HashMap<>();
      map.put(v, b);
      cs.put(x, map);
    }
  }

  /**
   * Whether a second Boolean for the same x = v is made equal to the first one. True for
   * reifications, where both are equivalent to x = v; implications b -> (x = v) only share the
   * consequence, so their Booleans stay independent.
   *
   * @return true if Booleans of the same pair are merged
   */
  boolean mergesDuplicates() {
    return true;
  }

  /**
   * Checks whether the constraint b <=> (x = v) was collected and will be posted as part of a
   * channeling constraint for x.
   *
   * @param x the integer variable
   * @param v the value
   * @param b the boolean variable
   * @return true if the constraint must not be posted on its own
   */
  public boolean handles(IntVar x, int v, IntVar b) {
    return size(x) > minSize && collected.contains(new Entry(x, v, b));
  }

  /**
   * Returns the value v such that b implies x = v was collected, if there is one.
   *
   * @param b the boolean variable
   * @param x the integer variable
   * @return the value, or null if no such constraint was collected
   */
  public Integer valueImpliedBy(IntVar b, IntVar x) {
    for (Entry e : byBoolean.getOrDefault(b, List.of())) {
      if (e.x() == x) {
        return e.v();
      }
    }
    return null;
  }

  /**
   * Returns the integer variables x for which some b implies x = v was collected.
   *
   * @param b the boolean variable
   * @return the variables, empty if there is none
   */
  public List<IntVar> variablesOf(IntVar b) {
    List<IntVar> result = new ArrayList<>();
    for (Entry e : byBoolean.getOrDefault(b, List.of())) {
      result.add(e.x());
    }
    return result;
  }

  public int size(IntVar v) {
    Map<Integer, IntVar> m = cs.get(v);

    if (m != null) {
      return m.size();
    } else {
      return 0;
    }
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder();

    Set<Map.Entry<IntVar, Map<Integer, IntVar>>> entries = cs.entrySet();

    for (Map.Entry<IntVar, Map<Integer, IntVar>> e : entries) {
      IntVar v = e.getKey();
      Map<Integer, IntVar> vb = e.getValue();
      Set<Map.Entry<Integer, IntVar>> es = vb.entrySet();

      result.append(v).append("[");

      for (Map.Entry<Integer, IntVar> ei : es) {
        int val = ei.getKey();
        IntVar bb = ei.getValue();

        result.append("[").append(val).append(", ").append(bb).append("]");
      }
    }
    result.append("]");
    return result.toString();
  }
}
