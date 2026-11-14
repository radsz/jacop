/*
 * BinPackingPermutations.java
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.FzConsole;

/**
 * It finds bin packing constraints whose items fall into groups that fill every bin with exactly
 * one item: the bin variables of an all_different constraint, as many as there are bins and with
 * their values among the bins, form a permutation of the bins. Team assignment models (one player
 * of each board in every team) are written so. For each such group and bin it posts the dual
 * viewpoint, the position of the item of the group the bin gets, channelled to the bins by {@link
 * Assignment}, the weight of that item by {@link ElementInteger}, and the load of each bin as the
 * sum of these weights, the weights of the items placed for good and the load of the other items
 * (redundant modelling with channelling, Cheng, Lee and Wu, Constraints 4(2), 1999). The bin
 * packing constraint bounds a load by the items that still may go into the bin, so it does not see
 * that the bin gets one more item of every group: with partial assignments its bounds on a load are
 * the weights placed so far and all items left, while the new sums add the lightest and heaviest
 * item left in each group.
 *
 * <p>The system property {@code org.jacop.fz.binPackingPermutations=false} turns it off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class BinPackingPermutations {

  // the arguments of one bin packing constraint; a plain class, since a record would compare its
  // arrays by identity
  private static final class Packing {
    final IntVar[] bin;
    final IntVar[] load;
    final int[] w;
    final int minBin;

    Packing(IntVar[] bin, IntVar[] load, int[] w, int minBin) {
      this.bin = bin;
      this.load = load;
      this.w = w;
      this.minBin = minBin;
    }
  }

  private final Support support;

  private final List<Packing> packings = new ArrayList<>();

  BinPackingPermutations(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.binPackingPermutations is false.
   */
  public static boolean enabled() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.binPackingPermutations", "true"));
  }

  /**
   * It records one bin packing constraint of the model.
   *
   * @param bin the bin of each item.
   * @param load the load of each bin.
   * @param w the size of each item.
   * @param minBin the index of the first bin.
   */
  void add(IntVar[] bin, IntVar[] load, int[] w, int minBin) {
    packings.add(new Packing(bin.clone(), load.clone(), w.clone(), minBin));
  }

  /** It posts the dual viewpoint of the permutation groups of every recorded bin packing. */
  public void detect() {
    if (!enabled() || support.options.proof() != null || packings.isEmpty()) {
      return;
    }
    int found = 0;
    int groups = 0;
    for (Packing p : packings) {
      int g = post(p);
      if (g > 0) {
        found++;
        groups += g;
      }
    }
    if (support.options.debug() && found > 0) {
      FzConsole.println(
          "% bin packing permutations: " + found + " constraints, " + groups + " groups");
    }
  }

  // the item of each bin variable; null when a variable is the bin of two items
  private static Map<IntVar, Integer> items(IntVar[] bin) {
    Map<IntVar, Integer> item = new IdentityHashMap<>();
    for (int i = 0; i < bin.length; i++) {
      if (!bin[i].singleton() && item.put(bin[i], i) != null) {
        return null;
      }
    }
    return item;
  }

  // the items of an all_different that is a permutation of the bins, or null
  private static int[] group(IntVar[] x, Map<IntVar, Integer> item, Packing p, boolean[] used) {
    int n = p.load.length;
    if (x.length != n) {
      return null;
    }
    int[] g = new int[n];
    for (int k = 0; k < n; k++) {
      Integer i = item.get(x[k]);
      if (i == null || used[i] || x[k].min() < p.minBin || x[k].max() > p.minBin + n - 1) {
        return null;
      }
      g[k] = i;
    }
    return g;
  }

  // it posts the sums for one bin packing and returns the number of groups used
  private int post(Packing p) {
    int n = p.load.length;
    Map<IntVar, Integer> item = items(p.bin);
    if (item == null || n < 3) {
      return 0;
    }
    boolean[] used = new boolean[p.bin.length];
    List<int[]> groups = new ArrayList<>();
    for (IntVar[] x : support.alldifferentLists) {
      int[] g = group(x, item, p, used);
      if (g == null) {
        continue;
      }
      boolean distinct = false;
      for (int i : g) {
        used[i] = true;
        distinct |= p.w[i] != p.w[g[0]];
      }
      // a group of equal weights adds the same weight to every bin
      groups.add(distinct ? g : new int[] {g[0]});
    }
    if (groups.stream().noneMatch(g -> g.length > 1)) {
      return 0;
    }
    // the weights of the other items: placed for good, or still free
    long[] fixed = new long[n];
    long low = 0;
    long high = 0;
    for (int[] g : groups) {
      if (g.length == 1) {
        for (int j = 0; j < n; j++) {
          fixed[j] += p.w[g[0]];
        }
      }
    }
    for (int i = 0; i < p.bin.length; i++) {
      if (used[i]) {
        continue;
      }
      if (p.bin[i].singleton()) {
        int j = p.bin[i].value() - p.minBin;
        if (j >= 0 && j < n) {
          fixed[j] += p.w[i];
        }
      } else if (p.w[i] < 0) {
        low += p.w[i];
      } else {
        high += p.w[i];
      }
    }
    if (low < IntDomain.MIN_INT || high > IntDomain.MAX_INT) {
      return 0;
    }
    for (long f : fixed) {
      if (Math.abs(f) > IntDomain.MAX_INT) {
        return 0;
      }
    }
    List<int[]> permutations = groups.stream().filter(g -> g.length > 1).toList();
    int m = permutations.size();
    boolean rest = low < high;
    IntVar[][] weight = new IntVar[n][m];
    for (int k = 0; k < m; k++) {
      int[] g = permutations.get(k);
      IntVar[] x = new IntVar[n];
      int[] w = new int[n];
      int min = Integer.MAX_VALUE;
      int max = Integer.MIN_VALUE;
      for (int t = 0; t < n; t++) {
        x[t] = p.bin[g[t]];
        w[t] = p.w[g[t]];
        min = Math.min(min, w[t]);
        max = Math.max(max, w[t]);
      }
      // position[j] is the position in x (from 1) of the item that bin minBin + j gets
      IntVar[] position = new IntVar[n];
      for (int j = 0; j < n; j++) {
        position[j] = new IntVar(support.store, 1, n);
        weight[j][k] = new IntVar(support.store, min, max);
        support.delayedConstraints.add(new ElementInteger(position[j], w, weight[j][k], 0));
      }
      support.delayedConstraints.add(new Assignment(x, position, 1, p.minBin));
    }
    for (int j = 0; j < n; j++) {
      int size = m + 1 + (rest ? 1 : 0);
      IntVar[] terms = Arrays.copyOf(weight[j], size);
      int[] coefficients = new int[size];
      Arrays.fill(coefficients, 0, m, 1);
      terms[m] = p.load[j];
      coefficients[m] = -1;
      if (rest) {
        terms[m + 1] = new IntVar(support.store, (int) low, (int) high);
        coefficients[m + 1] = 1;
      }
      support.delayedConstraints.add(new LinearInt(terms, coefficients, "==", (int) -fixed[j]));
    }
    return m;
  }
}
