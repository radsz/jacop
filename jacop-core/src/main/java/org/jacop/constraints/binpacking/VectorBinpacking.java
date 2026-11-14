/*
 * VectorBinpacking.java
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

package org.jacop.constraints.binpacking;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * VectorBinpacking packs items with a size in each of several dimensions into bins with a capacity
 * in each dimension (vector or multidimensional bin packing): for every bin and every dimension the
 * sizes of the items in the bin sum to the bin's load in that dimension.
 *
 * <p>It is decomposed as proposed by Gualandi and Lombardi, "A Simple and Effective Decomposition
 * for the Multidimensional Binpacking Constraint", CP 2013: one {@link Binpacking} per dimension,
 * plus an {@link Alldistinct} on the bin variables of each clique of the conflict graph. Two items
 * conflict when they exceed the largest capacity in some dimension, so they never share a bin. A
 * conflict graph built from all dimensions has cliques that no single dimension sees, and the
 * matching of {@link Alldistinct} prunes bins that Binpacking, reasoning one bin at a time, keeps.
 * The paper also breaks the symmetry of the bins; that removes solutions, so it is left to the
 * model.
 *
 * <p>It also posts a {@link Binpacking} on a surrogate dimension, the sum of the dimensions each
 * scaled to a common capacity (surrogate relaxation, as in the lower bounds of Caprara and Toth,
 * "Lower bounds and algorithms for the 2-dimensional vector packing problem", Discrete Applied
 * Mathematics 2001). Items that fit a bin together fit it in the surrogate dimension, so no
 * solution is lost, and the bin-count bounds (L2 and dual feasible functions) and cardinality rules
 * of Binpacking on that dimension see what no single dimension shows: with sizes (w, 80 - w) in
 * bins of capacity (100, 100) every item takes 80 of the surrogate capacity 200, so no bin holds
 * three items, while each dimension alone allows many more. Surrogates of pairs of dimensions,
 * tried on three-dimensional instances, pruned nothing more and slowed the search.
 *
 * <p>The cliques are found greedily ({@link #conflictCliques}): each one starts from an edge not
 * covered yet and grows by the item adjacent to the most remaining candidates. Cliques of fewer
 * than three items are dropped, since Binpacking already separates two conflicting items once one
 * of them is packed.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class VectorBinpacking extends DecomposedConstraint<Constraint> {

  /** The largest number of items for which cliques are searched. */
  public static final int MAX_ITEMS = 5000;

  // the largest common capacity of the surrogate dimensions taken as the lcm of the capacities
  private static final long MAX_LCM = 1L << 20;

  /** The largest number of cliques posted. */
  public static final int MAX_CLIQUES = 500;

  // word operations of the clique search; the cliques found before it runs out are kept
  private static final long CLIQUE_BUDGET = 50_000_000L;

  private final IntVar[] bin;
  private final IntVar[][] load;
  private final int[][] w;
  private final int minBin;

  private List<Constraint> constraints;

  /**
   * It creates a vector bin packing constraint.
   *
   * @param bin the bin of each item.
   * @param load the load of each bin in each dimension, load[d][b] for dimension d and bin b.
   * @param w the size of each item in each dimension, w[d][i] for dimension d and item i.
   * @param minBin the index of the first bin.
   */
  public VectorBinpacking(IntVar[] bin, IntVar[][] load, int[][] w, int minBin) {
    checkInputForNullness(new String[] {"bin", "load", "w"}, bin, load, w);
    if (load.length != w.length || load.length == 0) {
      throw new IllegalArgumentException(
          "Constraint VectorBinpacking needs the same number (at least one) of dimensions in load"
              + " and w");
    }
    for (int d = 0; d < w.length; d++) {
      if (w[d].length != bin.length) {
        throw new IllegalArgumentException(
            "Constraint VectorBinpacking has sizes of dimension "
                + d
                + " for a different number"
                + " of items than bin");
      }
      if (load[d].length != load[0].length) {
        throw new IllegalArgumentException(
            "Constraint VectorBinpacking has loads of dimension "
                + d
                + " for a different number"
                + " of bins than dimension 0");
      }
      checkInput(w[d], t -> t >= 0, "size of an item is not >= 0");
    }
    this.bin = Arrays.copyOf(bin, bin.length);
    this.load = new IntVar[load.length][];
    this.w = new int[w.length][];
    for (int d = 0; d < w.length; d++) {
      this.load[d] = Arrays.copyOf(load[d], load[d].length);
      this.w[d] = Arrays.copyOf(w[d], w[d].length);
    }
    this.minBin = minBin;
  }

  /**
   * It creates a vector bin packing constraint with fixed capacities; the loads are new variables.
   *
   * @param store the store in which the load variables are created.
   * @param bin the bin of each item.
   * @param capacity the capacity of each bin in each dimension, capacity[d][b].
   * @param w the size of each item in each dimension, w[d][i] for dimension d and item i.
   * @param minBin the index of the first bin.
   */
  public VectorBinpacking(Store store, IntVar[] bin, int[][] capacity, int[][] w, int minBin) {
    this(bin, loads(store, capacity), w, minBin);
  }

  private static IntVar[][] loads(Store store, int[][] capacity) {
    IntVar[][] load = new IntVar[capacity.length][];
    for (int d = 0; d < capacity.length; d++) {
      load[d] = new IntVar[capacity[d].length];
      for (int b = 0; b < capacity[d].length; b++) {
        load[d][b] = new IntVar(store, 0, capacity[d][b]);
      }
    }
    return load;
  }

  @Override
  public void imposeDecomposition(Store store) {
    for (Constraint c : decompose(store)) {
      store.impose(c);
    }
  }

  @Override
  public List<Constraint> decompose(Store store) {
    if (constraints == null) {
      constraints = new ArrayList<>();
      for (int d = 0; d < w.length; d++) {
        constraints.add(new Binpacking(bin, load[d], w[d], minBin));
      }
      constraints.addAll(surrogateConstraints(store, bin, load, w, minBin));
      constraints.addAll(cliqueConstraints(bin, w, maxCapacities(load)));
    }
    return constraints;
  }

  /**
   * It returns the largest capacity of a bin in each dimension.
   *
   * @param load the load of each bin in each dimension, load[d][b].
   * @return the largest maximum of the loads of each dimension.
   */
  public static int[] maxCapacities(IntVar[][] load) {
    int[] capacity = new int[load.length];
    for (int d = 0; d < load.length; d++) {
      capacity[d] = Integer.MIN_VALUE;
      for (IntVar l : load[d]) {
        capacity[d] = Math.max(capacity[d], l.max());
      }
    }
    return capacity;
  }

  /**
   * It returns a {@link Binpacking}, with its cardinality rules, on the surrogate dimension, the
   * sum of all dimensions. Dimension d is multiplied by L / c[d], where c[d] is its largest
   * capacity and L the least common multiple of the capacities (or by the nearest integer to max(c)
   * / c[d] when that multiple is too large), so every dimension weighs about the same. The load of
   * a bin in a surrogate dimension is a new variable between 0 and the weighted sum of the largest
   * loads of the bin. Any positive multipliers give a relaxation: items that fit a bin in every
   * dimension fit it in the sum.
   *
   * @param store the store in which the surrogate loads are created.
   * @param bin the bin of each item.
   * @param load the load of each bin in each dimension, load[d][b].
   * @param w the size of each item in each dimension, w[d][i].
   * @param minBin the index of the first bin.
   * @return the Binpacking constraint, or none with fewer than two dimensions or when a surrogate
   *     size or capacity would not fit an int.
   */
  public static List<Constraint> surrogateConstraints(
      Store store, IntVar[] bin, IntVar[][] load, int[][] w, int minBin) {
    List<Constraint> result = new ArrayList<>();
    int k = w.length;
    if (k < 2) {
      return result;
    }
    long[] multiplier = multipliers(maxCapacities(load));
    if (multiplier == null) {
      return result;
    }
    int[] size = new int[bin.length];
    long total = 0;
    for (int i = 0; i < bin.length; i++) {
      long sum = 0;
      for (int d = 0; d < k; d++) {
        sum += multiplier[d] * w[d][i];
      }
      total += sum;
      if (total > Integer.MAX_VALUE) {
        return result;
      }
      size[i] = (int) sum;
    }
    IntVar[] surrogateLoad = new IntVar[load[0].length];
    for (int b = 0; b < surrogateLoad.length; b++) {
      long capacity = 0;
      for (int d = 0; d < k; d++) {
        capacity += multiplier[d] * Math.max(0, load[d][b].max());
      }
      if (capacity > Integer.MAX_VALUE) {
        return result;
      }
      surrogateLoad[b] = new IntVar(store, 0, (int) capacity);
    }
    // the cardinality rules bound the items of a bin by the smallest surrogate sizes
    result.add(new Binpacking(bin, surrogateLoad, size, minBin).cardinalityReasoning(true));
    return result;
  }

  // L / c[d] with L the lcm of the capacities, or round(max(c) / c[d]) when L is too large; null
  // when a capacity is not positive
  private static long[] multipliers(int[] capacity) {
    long lcm = 1;
    long max = 0;
    for (int c : capacity) {
      if (c <= 0) {
        return null;
      }
      max = Math.max(max, c);
      if (lcm <= MAX_LCM) {
        lcm = lcm / gcd(lcm, c) * c;
      }
    }
    long[] multiplier = new long[capacity.length];
    for (int d = 0; d < capacity.length; d++) {
      multiplier[d] =
          lcm <= MAX_LCM ? lcm / capacity[d] : Math.max(1, Math.round((double) max / capacity[d]));
    }
    return multiplier;
  }

  private static long gcd(long a, long b) {
    return b == 0 ? a : gcd(b, a % b);
  }

  /**
   * It returns an {@link Alldistinct} for each clique of conflicting items, items that exceed the
   * capacity of some dimension together. Items that share a bin variable are merged first, as
   * {@link Binpacking} does, so their sizes add up.
   *
   * @param bin the bin of each item.
   * @param w the size of each item in each dimension, w[d][i].
   * @param capacity the largest capacity of a bin in each dimension.
   * @return the Alldistinct constraints, each with degree weight 0.
   */
  public static List<Constraint> cliqueConstraints(IntVar[] bin, int[][] w, int[] capacity) {
    Map<IntVar, Integer> itemOf = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    List<long[]> sizes = new ArrayList<>();
    for (int i = 0; i < bin.length; i++) {
      Integer k = itemOf.get(bin[i]);
      if (k == null) {
        k = vars.size();
        itemOf.put(bin[i], k);
        vars.add(bin[i]);
        sizes.add(new long[w.length]);
      }
      for (int d = 0; d < w.length; d++) {
        sizes.get(k)[d] += w[d][i];
      }
    }
    List<Constraint> result = new ArrayList<>();
    for (int[] clique : conflictCliques(sizes.toArray(new long[0][]), capacity)) {
      IntVar[] x = new IntVar[clique.length];
      for (int k = 0; k < clique.length; k++) {
        x[k] = vars.get(clique[k]);
      }
      result.add(new Alldistinct(x).setDegreeWeight(0));
    }
    return result;
  }

  /**
   * It finds cliques of the conflict graph of the items: two items conflict when their sizes in
   * some dimension exceed its capacity. Cliques are grown greedily from the edges not covered yet,
   * until every edge is covered, {@link #MAX_CLIQUES} cliques are found or the work budget runs
   * out.
   *
   * @param size the size of each item in each dimension, size[i][d].
   * @param capacity the capacity of each dimension.
   * @return the cliques of at least three items, each given by its item indices in increasing
   *     order.
   */
  public static List<int[]> conflictCliques(long[][] size, int[] capacity) {
    int n = size.length;
    List<int[]> result = new ArrayList<>();
    if (n < 3 || n > MAX_ITEMS) {
      return result;
    }
    int words = (n + 63) >>> 6;
    long[][] adj = new long[n][words];
    long[][] open = new long[n][words];
    int[] openDegree = new int[n];
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        for (int d = 0; d < capacity.length; d++) {
          if (size[i][d] + size[j][d] > capacity[d]) {
            set(adj[i], j);
            set(adj[j], i);
            set(open[i], j);
            set(open[j], i);
            openDegree[i]++;
            openDegree[j]++;
            break;
          }
        }
      }
    }
    long work = (long) n * n;
    while (result.size() < MAX_CLIQUES && work < CLIQUE_BUDGET) {
      int u = -1;
      for (int i = 0; i < n; i++) {
        if (openDegree[i] > 0 && (u < 0 || openDegree[i] > openDegree[u])) {
          u = i;
        }
      }
      if (u < 0) {
        break;
      }
      int v = -1;
      for (int j = nextSet(open[u], 0); j >= 0; j = nextSet(open[u], j + 1)) {
        if (v < 0 || openDegree[j] > openDegree[v]) {
          v = j;
        }
      }
      long[] members = new long[words];
      set(members, u);
      set(members, v);
      long[] candidates = new long[words];
      for (int k = 0; k < words; k++) {
        candidates[k] = adj[u][k] & adj[v][k];
      }
      int cliqueSize = 2;
      while (true) {
        int best = -1;
        int bestGrowth = -1;
        int bestOpen = -1;
        for (int c = nextSet(candidates, 0); c >= 0; c = nextSet(candidates, c + 1)) {
          int growth = 0;
          int toCover = 0;
          for (int k = 0; k < words; k++) {
            growth += Long.bitCount(adj[c][k] & candidates[k]);
            toCover += Long.bitCount(open[c][k] & members[k]);
          }
          work += words;
          if (growth > bestGrowth || growth == bestGrowth && toCover > bestOpen) {
            best = c;
            bestGrowth = growth;
            bestOpen = toCover;
          }
        }
        if (best < 0) {
          break;
        }
        set(members, best);
        cliqueSize++;
        for (int k = 0; k < words; k++) {
          candidates[k] &= adj[best][k];
        }
      }
      int[] clique = new int[cliqueSize];
      int m = 0;
      for (int i = nextSet(members, 0); i >= 0; i = nextSet(members, i + 1)) {
        clique[m++] = i;
        for (int k = 0; k < words; k++) {
          openDegree[i] -= Long.bitCount(open[i][k] & members[k]);
          open[i][k] &= ~members[k];
        }
      }
      work += (long) cliqueSize * words;
      if (cliqueSize >= 3) {
        result.add(clique);
      }
    }
    return result;
  }

  private static void set(long[] bits, int i) {
    bits[i >>> 6] |= 1L << i;
  }

  private static int nextSet(long[] bits, int from) {
    int k = from >>> 6;
    if (k >= bits.length) {
      return -1;
    }
    long word = bits[k] & (-1L << from);
    while (true) {
      if (word != 0) {
        return (k << 6) + Long.numberOfTrailingZeros(word);
      }
      if (++k == bits.length) {
        return -1;
      }
      word = bits[k];
    }
  }
}
