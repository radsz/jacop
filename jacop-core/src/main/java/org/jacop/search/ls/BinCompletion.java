/*
 * BinCompletion.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * owners of this library are free to combine it with any closed source
 * application, for example, by using this library as a library,
 * and to distribute the result as long as the source code of
 * this library is not distributed.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.search.ls;

import java.util.Arrays;
import java.util.Random;
import java.util.function.BooleanSupplier;

/**
 * Packs items into a given number of bins of one capacity by bin completion with restarts, a primal
 * heuristic for bin packing at its lower bound.
 *
 * <p>Each step takes the item whose bin has the fewest completions, the sets of remaining items
 * that fill the rest of its bin to within the waste still allowed (the capacity of all bins minus
 * the total weight), and tries first those that pack the items with the fewest completions of their
 * own, with random noise; an item without completion fails the branch. Bin completion builds a
 * solution bin by bin (R. E. Korf, A new algorithm for optimal bin packing, AAAI 2002; E. L.
 * Schreiber and R. E. Korf, Improved bin completion for optimal bin packing and number
 * partitioning, IJCAI 2013); choosing the item with the fewest completions first is the first-fail
 * principle (R. M. Haralick and G. L. Elliott, Increasing tree search efficiency for constraint
 * satisfaction problems, Artificial Intelligence 14, 1980), and randomized restarts with a growing
 * node limit cut the heavy tails of such searches (C. P. Gomes, B. Selman and H. Kautz, Boosting
 * combinatorial search through randomization, AAAI 1998).
 *
 * <p>On the Falkenauer triplets of the OR-Library (E. Falkenauer, A hybrid grouping genetic
 * algorithm for bin packing, Journal of Heuristics 2, 1996), where every bin of an optimal packing
 * is full with three items, the lower bound is the optimum and the search finds such a packing in a
 * few thousand nodes, whatever the order of the items; branching on the items' bins did not.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class BinCompletion {

  // completions counted per item when choosing the next one; an item with more counts as this many
  private static final int MAX_COMPLETIONS = 256;

  // completions tried in a bin; with waste allowed there can be many more
  private static final int MAX_TRIED = 1024;

  private static final int FIRST_LIMIT = 100;

  private final int[] weight; // the distinct weights, decreasing
  private final int[] count; // the items of each distinct weight still unpacked
  private final int[] itemsOf; // the items of each distinct weight
  private final int capacity;
  private final int bins;
  private final int total;
  private final Random random;

  private long nodes;
  private long limit;
  private long allNodes;
  private int restarts;

  // the completion chosen in each bin, as counts per distinct weight, the first entry its item
  private final int[][] chosen;
  private int depth;

  // scratch of the completion search
  private final int[] take;
  private int[][] found;
  private int foundCount;

  /**
   * Creates the search.
   *
   * @param weights the weights of the items, positive and at most the capacity
   * @param capacity the capacity of every bin
   * @param bins the number of bins
   * @param seed the seed of the random choices
   */
  public BinCompletion(int[] weights, int capacity, int bins, long seed) {
    int[] sorted = weights.clone();
    Arrays.sort(sorted);
    int distinct = 0;
    for (int i = 0; i < sorted.length; i++) {
      if (i == 0 || sorted[i] != sorted[i - 1]) {
        distinct++;
      }
    }
    weight = new int[distinct];
    count = new int[distinct];
    int k = -1;
    for (int i = sorted.length - 1; i >= 0; i--) {
      if (k < 0 || weight[k] != sorted[i]) {
        weight[++k] = sorted[i];
      }
      count[k]++;
    }
    itemsOf = count.clone();
    long sum = 0;
    for (int w : weights) {
      sum += w;
    }
    this.capacity = capacity;
    this.bins = bins;
    this.total = (int) Math.min(Integer.MAX_VALUE, sum);
    this.random = new Random(seed);
    chosen = new int[bins][];
    take = new int[distinct];
    found = new int[16][];
  }

  /**
   * Searches for a packing until one is found or stop says so.
   *
   * @param stop tells when to give up, asked after every run
   * @return the bins of the packing, one array of item weights each, or null
   */
  public int[][] run(BooleanSupplier stop) {
    long waste = (long) capacity * bins - total;
    if (waste < 0 || weight.length == 0 || weight[0] > capacity) {
      return null;
    }
    limit = FIRST_LIMIT;
    while (!stop.getAsBoolean()) {
      System.arraycopy(itemsOf, 0, count, 0, count.length);
      nodes = 0;
      depth = 0;
      int left = 0;
      for (int c : count) {
        left += c;
      }
      int result = search(left, (int) waste);
      allNodes += nodes;
      if (result > 0) {
        return packing();
      }
      if (result == 0) {
        // the whole tree failed: no packing in this many bins
        return null;
      }
      restarts++;
      limit += limit / 3 + 1;
    }
    return null;
  }

  /** The number of nodes of all runs. */
  public long nodes() {
    return allNodes;
  }

  /** The number of restarts. */
  public int restarts() {
    return restarts;
  }

  private int[][] packing() {
    int[][] out = new int[depth][];
    for (int b = 0; b < depth; b++) {
      int[] c = chosen[b];
      int n = 1;
      for (int k = 1; k < c.length; k++) {
        n += c[k];
      }
      int[] items = new int[n];
      items[0] = weight[c[0]];
      int at = 1;
      for (int k = 1; k < c.length; k++) {
        for (int j = 0; j < c[k]; j++) {
          items[at++] = weight[k - 1];
        }
      }
      out[b] = items;
    }
    return out;
  }

  /**
   * Packs the items left into the bins left.
   *
   * @return 1 on a packing, 0 when the tree failed, -1 when the node limit stopped it
   */
  private int search(int left, int waste) {
    if (left == 0) {
      return 1;
    }
    if (depth == bins) {
      return 0;
    }
    if (++nodes > limit) {
      return -1;
    }
    // the item with the fewest completions, ties to the larger, then at random
    int best = -1;
    int bestCount = Integer.MAX_VALUE;
    int ties = 0;
    int[] hard = new int[weight.length];
    for (int k = 0; k < weight.length; k++) {
      if (count[k] == 0) {
        continue;
      }
      count[k]--;
      int n = completions(capacity - weight[k], waste, false);
      count[k]++;
      hard[k] = n;
      if (n == 0) {
        return 0;
      }
      if (n < bestCount) {
        best = k;
        bestCount = n;
        ties = 1;
      } else if (n == bestCount && bestCount < MAX_COMPLETIONS && random.nextInt(++ties) == 0) {
        best = k;
      }
    }
    count[best]--;
    completions(capacity - weight[best], waste, true);
    int[][] options = Arrays.copyOf(found, foundCount);
    // with completions left out, a failure of those tried proves nothing
    boolean limited = foundCount >= MAX_TRIED;
    order(options, hard);
    for (int[] option : options) {
      int used = 0;
      int sum = 0;
      for (int k = 0; k < option.length; k++) {
        count[k] -= option[k];
        used += option[k];
        sum += option[k] * weight[k];
      }
      int[] record = new int[option.length + 1];
      record[0] = best;
      System.arraycopy(option, 0, record, 1, option.length);
      chosen[depth++] = record;
      int result = search(left - 1 - used, waste - (capacity - weight[best] - sum));
      if (result > 0) {
        return result;
      }
      depth--;
      for (int k = 0; k < option.length; k++) {
        count[k] += option[k];
      }
      if (result < 0) {
        limited = true;
        break;
      }
    }
    count[best]++;
    return limited ? -1 : 0;
  }

  /**
   * Orders the completions by how hard their items are to pack elsewhere, the sum over their items
   * of one over the item's completions, each score scaled by a random factor in [1, 2) so restarts
   * try other orders.
   */
  private void order(int[][] options, int[] hard) {
    double[] score = new double[options.length];
    for (int i = 0; i < options.length; i++) {
      double sum = 0;
      for (int k = 0; k < options[i].length; k++) {
        if (options[i][k] > 0) {
          sum += options[i][k] / (double) hard[k];
        }
      }
      score[i] = sum * (1 + random.nextDouble());
    }
    // insertion sort by decreasing score, the arrays being short
    for (int i = 1; i < options.length; i++) {
      int[] option = options[i];
      double value = score[i];
      int j = i - 1;
      while (j >= 0 && score[j] < value) {
        options[j + 1] = options[j];
        score[j + 1] = score[j];
        j--;
      }
      options[j + 1] = option;
      score[j + 1] = value;
    }
  }

  /**
   * Counts, or with keep collects in found, the sets of remaining items whose total is at most room
   * and at least room - waste, up to {@link #MAX_COMPLETIONS} when counting and {@link #MAX_TRIED}
   * when collecting.
   */
  private int completions(int room, int waste, boolean keep) {
    foundCount = 0;
    Arrays.fill(take, 0);
    smallest = Integer.MAX_VALUE;
    for (int k = weight.length - 1; k >= 0; k--) {
      if (count[k] > 0) {
        smallest = weight[k];
        break;
      }
    }
    return completions(0, room, room - waste, keep, 0);
  }

  // the smallest weight of an unpacked item, at the start of a completion search
  private int smallest;

  private int completions(int k, int room, int least, boolean keep, int n) {
    int cap = keep ? MAX_TRIED : MAX_COMPLETIONS;
    if (least <= 0) {
      // the bin is full enough with what it holds; more items may still fit
      n++;
      if (keep) {
        if (foundCount == found.length) {
          found = Arrays.copyOf(found, 2 * found.length);
        }
        found[foundCount++] = take.clone();
      }
      if (n >= cap) {
        return n;
      }
    }
    // the items that fit, the weights being decreasing; below least, only those that leave room
    // for one more item can be part of a completion
    int j = firstAtMost(room, k);
    int below = least > 0 ? firstAtMost(least - 1, j) : weight.length;
    for (; j < weight.length; j++) {
      if (j == below) {
        j = firstAtMost(room - smallest, j);
        if (j >= weight.length) {
          break;
        }
      }
      if (take[j] == count[j]) {
        continue;
      }
      take[j]++;
      n = completions(j, room - weight[j], least - weight[j], keep, n);
      take[j]--;
      if (n >= cap) {
        return n;
      }
    }
    return n;
  }

  /** The first index from at with a weight at most value (the weights decrease). */
  private int firstAtMost(int value, int from) {
    int lo = from;
    int hi = weight.length;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (weight[mid] > value) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return lo;
  }
}
