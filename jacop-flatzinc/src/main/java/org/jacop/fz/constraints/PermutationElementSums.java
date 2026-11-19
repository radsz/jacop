/*
 * PermutationElementSums.java
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
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.FzConsole;

/**
 * It finds element constraints {@code y[k] = c[x[k]]} over one constant array {@code c} whose
 * indices {@code x[k]} are the variables of an all_different constraint, and posts the sum of the
 * values {@code y[k]} as a linear constraint. The indices take distinct values of the union {@code
 * U} of their domains, so the sum of {@code y[k]} over the n indices lies between the sum of the n
 * smallest and the n largest values of {@code c} over {@code U}; when the indices are a permutation
 * of {@code U} (n = |U|) the sum is fixed. Neither the element constraints nor the all_different
 * constraint, alone or in the linear relaxation, see this: each {@code y[k]} only gets the smallest
 * value of {@code c} as its lower bound.
 *
 * <p>Permutation flow shop models give each machine the processing times of the jobs in the
 * sequence positions, {@code d[i,k] = p[i,perm[k]]}: the sum is then the machine load, the bound of
 * Taillard (Eur. J. Oper. Res. 64(2), 1993) and of the one-machine relaxations it comes from
 * (Lageweg, Lenstra and Rinnooy Kan, Oper. Res. 26(1), 1978). Taillard's ta006 (20 jobs, 5
 * machines) has a root bound of 160 without the sums and is proved optimal in seconds with them.
 * The sums are the aggregation of the element and all-different reformulation by assignment
 * variables (Refalo, CP 2000, linear formulations of element and all_different), restricted to one
 * row per array.
 *
 * <p>The system property {@code org.jacop.fz.permutationElementSums=false} turns it off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class PermutationElementSums {

  // one element constraint y = c[x - first]; a plain class, since a record would compare its
  // array by identity
  private static final class Element {
    final IntVar x;
    final int[] c;
    final IntVar y;
    final int first;

    Element(IntVar x, int[] c, IntVar y, int first) {
      this.x = x;
      this.c = c;
      this.y = y;
      this.first = first;
    }
  }

  // the key of a constant array: its first index and its values
  private record ArrayKey(int first, List<Integer> values) {}

  // the arrays of more values than this are left out, as the key copies them
  private static final int MAX_ARRAY = 10_000;

  private final Support support;

  private final Map<IntVar, List<Element>> byIndex = new IdentityHashMap<>();

  private int sums;

  private int counts;

  // the most distinct values of an array whose counts are posted
  private static final int MAX_COUNTED = 64;

  PermutationElementSums(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.permutationElementSums is false.
   */
  public static boolean enabled() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.permutationElementSums", "true"));
  }

  /**
   * It records an element constraint {@code y = c[x - first]} over a constant array.
   *
   * @param x the index.
   * @param c the array.
   * @param y the value.
   * @param first the index of {@code c[0]}.
   */
  void add(IntVar x, int[] c, IntVar y, int first) {
    if (!enabled() || x.singleton() || c.length < 2 || c.length > MAX_ARRAY) {
      return;
    }
    byIndex.computeIfAbsent(x, k -> new ArrayList<>(1)).add(new Element(x, c.clone(), y, first));
  }

  /**
   * It records the binary table {@code (v[0], v[1])} as an element constraint over one of its
   * columns when the other column is a function of it, defined on every value from the smallest to
   * the largest value of that column: the visitor group of a visitor, the class of a slot.
   *
   * @param v the two variables of the table.
   * @param tbl the tuples, flattened row by row, before the domains filtered them.
   */
  void addTable(IntVar[] v, int[] tbl) {
    if (!enabled() || v.length != 2 || v[0] == v[1] || tbl.length < 4) {
      return;
    }
    for (int from = 0; from < 2; from++) {
      int[] c = function(tbl, from);
      if (c.length > 0) {
        add(v[from], Arrays.copyOfRange(c, 1, c.length), v[1 - from], c[0]);
      }
    }
  }

  // the column 1 - from of the pairs tbl as a function of column from, {first, c...} with c[a -
  // first] the image of a, or an empty array when a value has two images or a value between the
  // smallest and
  // the largest has none
  private static int[] function(int[] tbl, int from) {
    int min = Integer.MAX_VALUE;
    int max = Integer.MIN_VALUE;
    for (int i = from; i < tbl.length; i += 2) {
      min = Math.min(min, tbl[i]);
      max = Math.max(max, tbl[i]);
    }
    long size = (long) max - min + 1;
    if (size > MAX_ARRAY || size != tbl.length / 2) {
      // a hole or a value with two images
      return new int[0];
    }
    int[] c = new int[(int) size + 1];
    boolean[] set = new boolean[(int) size];
    c[0] = min;
    for (int i = 0; i < tbl.length; i += 2) {
      int a = tbl[i + from] - min;
      if (set[a]) {
        return new int[0];
      }
      set[a] = true;
      c[a + 1] = tbl[i + 1 - from];
    }
    return c;
  }

  /** It posts the sums of the elements over the indices of each all_different constraint. */
  public void detect() {
    if (!enabled() || support.options.proof() != null || byIndex.isEmpty()) {
      return;
    }
    for (IntVar[] x : support.alldifferentLists) {
      post(x);
    }
    for (Support.Shifted s : support.allDifferentOffsets) {
      if (s.o().stream().allMatch(o -> o == 0)) {
        post(s.x().toArray(new IntVar[0]));
      }
    }
    if ((support.options.debug() || support.options.searchStatistics()) && sums + counts > 0) {
      FzConsole.println(
          "%%%mzn-stat: permutationElementSums="
              + sums
              + "\n%%%mzn-stat: permutationElementCounts="
              + counts
              + "\n%%%mzn-stat-end");
    }
    byIndex.clear();
  }

  // the sums over the indices x of one all_different constraint, one for each array
  private void post(IntVar[] x) {
    if (x.length < 2) {
      return;
    }
    IntDomain union = new IntervalDomain();
    for (IntVar v : x) {
      union.unionAdapt(v.dom());
    }
    if (union.getSize() < x.length || union.getSize() > MAX_ARRAY) {
      return;
    }
    // the elements of each array, the first one of each index
    Map<ArrayKey, List<Element>> groups = new HashMap<>();
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (IntVar v : x) {
      if (seen.put(v, Boolean.TRUE) != null) {
        // a variable twice, which the all_different constraint fails on
        return;
      }
      List<Element> es = byIndex.get(v);
      if (es == null) {
        continue;
      }
      Map<ArrayKey, Boolean> own = new HashMap<>();
      for (Element e : es) {
        ArrayKey key = new ArrayKey(e.first, Arrays.stream(e.c).boxed().toList());
        if (own.put(key, Boolean.TRUE) == null) {
          groups.computeIfAbsent(key, k -> new ArrayList<>()).add(e);
        }
      }
    }
    for (Map.Entry<ArrayKey, List<Element>> g : groups.entrySet()) {
      List<Element> es = g.getValue();
      if (es.size() >= 2) {
        boolean permutation = es.size() == x.length && union.getSize() == x.length;
        if (permutation && countsEnabled()) {
          postCounts(es, union);
        }
        post(es, union, permutation);
      }
    }
  }

  /**
   * It tells if the counts of the values of the elements over a permutation are posted, {@code
   * org.jacop.fz.permutationElementCounts} (default true).
   *
   * @return false if the system property is false.
   */
  public static boolean countsEnabled() {
    return Boolean.parseBoolean(
        System.getProperty("org.jacop.fz.permutationElementCounts", "true"));
  }

  /**
   * It posts the counts of the values of the elements es, whose indices are a permutation of union:
   * value c of the array is taken by as many elements as there are indices u of union with c[u] =
   * c. This is the cardinality form of the sums ({@link #post(List, IntDomain, boolean)}): the sum
   * fixes the mean of the values, the counts fix each value. With the all_different constraints
   * over the values themselves the counts give a pigeonhole argument that neither propagation nor
   * lazy clause generation sees. In the mystery shopper of CSPLib (prob004, XCSP 2024), the visitor
   * group of the visitor of a visitee in week w is a table of the visitor, the visitors of a week
   * are a permutation, and the groups that visit one visitee over the W weeks are all different, so
   * a visitee sees each of the W groups once; with these counts a group of s visitors makes s
   * visits a week and W s in all, which the linear relaxation of the counts and the all_different
   * constraints finds is not the number of visitees when the groups differ in size (5-08-1: 39
   * visitees, a group of 8 makes 40 visits), while search finds nothing in 30 minutes. The counts
   * are those of the aggregated assignment formulation of element and all_different (Refalo, CP
   * 2000).
   */
  private void postCounts(List<Element> es, IntDomain union) {
    Element e0 = es.get(0);
    Map<Integer, Integer> count = new TreeMap<>();
    for (ValueEnumeration it = union.valueEnumeration(); it.hasMoreElements(); ) {
      long i = (long) it.nextElement() - e0.first;
      if (i < 0 || i >= e0.c.length) {
        // an index the element constraints remove
        return;
      }
      count.merge(e0.c[(int) i], 1, Integer::sum);
    }
    if (count.size() > MAX_COUNTED || 2 * count.size() > union.getSize()) {
      // too many values, or most values once (processing times of a flow shop): the counts then
      // add little to the sum and slowed the search (Taillard ta011, ta016)
      return;
    }
    int[] values = new int[count.size()];
    IntVar[] counters = new IntVar[count.size()];
    int i = 0;
    for (Map.Entry<Integer, Integer> c : count.entrySet()) {
      values[i] = c.getKey();
      counters[i] = new IntVar(support.store, c.getValue(), c.getValue());
      i++;
    }
    IntVar[] y = new IntVar[es.size()];
    for (int k = 0; k < y.length; k++) {
      y[k] = es.get(k).y;
    }
    support.delayedConstraints.add(new CountValues(y, counters, values));
    counts++;
  }

  // the sum of the values of the elements es, whose indices take distinct values of union
  private void post(List<Element> es, IntDomain union, boolean permutation) {
    Element e0 = es.get(0);
    int[] values = new int[union.getSize()];
    int n = 0;
    for (ValueEnumeration it = union.valueEnumeration(); it.hasMoreElements(); ) {
      long i = (long) it.nextElement() - e0.first;
      if (i < 0 || i >= e0.c.length) {
        // an index the element constraints remove: the indices may take fewer values
        return;
      }
      values[n++] = e0.c[(int) i];
    }
    Arrays.sort(values);
    int k = es.size();
    long low = 0;
    long high = 0;
    long lowSoFar = 0;
    long highSoFar = 0;
    for (int i = 0; i < k; i++) {
      low += values[i];
      high += values[values.length - 1 - i];
    }
    IntVar[] y = new IntVar[k];
    for (int i = 0; i < k; i++) {
      y[i] = es.get(i).y;
      lowSoFar += y[i].min();
      highSoFar += y[i].max();
    }
    if (low < Integer.MIN_VALUE || high > Integer.MAX_VALUE) {
      return;
    }
    if (low <= lowSoFar && high >= highSoFar) {
      // the bounds of the values give the sums already
      return;
    }
    int[] a = new int[k];
    Arrays.fill(a, 1);
    if (permutation || low == high) {
      support.delayedConstraints.add(new LinearInt(y, a, "==", (int) low));
    } else {
      if (low > lowSoFar) {
        support.delayedConstraints.add(new LinearInt(y, a, ">=", (int) low));
      }
      if (high < highSoFar) {
        support.delayedConstraints.add(new LinearInt(y, a, "<=", (int) high));
      }
    }
    sums++;
  }
}
