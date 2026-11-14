/*
 * BinPackingCliqueDetector.java
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.binpacking.VectorBinpacking;
import org.jacop.core.IntVar;
import org.jacop.fz.FzConsole;

/**
 * It finds bin packing constraints over the same bin variables, one per dimension of a vector bin
 * packing problem (MiniZinc has no vector bin packing global, so models write one {@code
 * bin_packing_capa} or {@code bin_packing_load} per dimension), and posts what {@link
 * VectorBinpacking} adds to them: a bin packing constraint on the surrogate dimension, the sum of
 * the dimensions scaled to a common capacity, and optionally the cliques of the conflict graph as
 * {@link org.jacop.constraints.Alldistinct} constraints (Gualandi and Lombardi, CP 2013).
 *
 * <p>The surrogate dimension is on by default; the system property {@code
 * org.jacop.fz.binPackingSurrogate=false} turns it off. On 75 random vector bin packing instances
 * (30 s) it proved 62 optima instead of 49 with the model's search and 65 instead of 54 with free
 * search, for example every instance with anti-correlated sizes, where no bin holds three items.
 *
 * <p>The system property {@code org.jacop.fz.binPackingCliques} selects the groups that get
 * cliques: {@code vector} the groups of at least two constraints, {@code all} also single
 * constraints, and {@code false} (the default) none. The cliques are off by default because on the
 * same benchmarks they proved no more optima, with or without the surrogate dimension.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class BinPackingCliqueDetector {

  // the bin variables of a group and, per dimension, its loads and sizes; plain classes, since a
  // record would compare its arrays by identity
  private static final class Group {
    final IntVar[] bin;
    final int minBin;
    final List<IntVar[]> loads = new ArrayList<>();
    final List<int[]> sizes = new ArrayList<>();

    Group(IntVar[] bin, int minBin) {
      this.bin = bin;
      this.minBin = minBin;
    }
  }

  private final Support support;

  // bin variables and first bin -> one entry per dimension
  private final Map<List<Object>, Group> groups = new LinkedHashMap<>();

  BinPackingCliqueDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return true if the system property org.jacop.fz.binPackingCliques is vector or all.
   */
  public static boolean enabled() {
    String mode = System.getProperty("org.jacop.fz.binPackingCliques", "false");
    return "vector".equalsIgnoreCase(mode) || "all".equalsIgnoreCase(mode);
  }

  private static int minDimensions() {
    return "all".equalsIgnoreCase(System.getProperty("org.jacop.fz.binPackingCliques")) ? 1 : 2;
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
    List<Object> key = new ArrayList<>(bin.length + 2);
    key.add(minBin);
    key.add(load.length);
    key.addAll(Arrays.asList(bin));
    Group group = groups.computeIfAbsent(key, k -> new Group(bin, minBin));
    group.loads.add(load);
    group.sizes.add(w);
  }

  /**
   * It tells if the surrogate dimensions are posted.
   *
   * @return false if the system property org.jacop.fz.binPackingSurrogate is false.
   */
  public static boolean surrogateEnabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.binPackingSurrogate"));
  }

  /**
   * It posts the surrogate dimensions and the cliques of each group of bin packing constraints over
   * the same bins.
   */
  public void detect() {
    boolean cliques = enabled();
    boolean surrogates = surrogateEnabled();
    if (!cliques && !surrogates) {
      return;
    }
    long start = System.nanoTime();
    int minDimensions = minDimensions();
    int found = 0;
    int surrogate = 0;
    for (Group group : groups.values()) {
      IntVar[][] load = group.loads.toArray(new IntVar[0][]);
      int[][] w = group.sizes.toArray(new int[0][]);
      if (surrogates && group.loads.size() >= 2) {
        List<Constraint> s =
            VectorBinpacking.surrogateConstraints(support.store, group.bin, load, w, group.minBin);
        support.delayedConstraints.addAll(s);
        surrogate += s.size();
      }
      if (!cliques || group.loads.size() < minDimensions) {
        continue;
      }
      List<Constraint> c =
          VectorBinpacking.cliqueConstraints(group.bin, w, VectorBinpacking.maxCapacities(load));
      support.delayedConstraints.addAll(c);
      found += c.size();
    }
    if (support.options.debug() && !groups.isEmpty()) {
      FzConsole.println(
          "% bin packing cliques: "
              + groups.size()
              + " groups, "
              + found
              + " cliques, "
              + surrogate
              + " surrogate dimensions, "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
  }
}
