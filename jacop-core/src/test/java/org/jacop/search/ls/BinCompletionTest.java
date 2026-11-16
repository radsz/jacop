/*
 * BinCompletionTest.java
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
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */
package org.jacop.search.ls;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Tests {@link BinCompletion}: every packing it returns holds the items in the given bins within
 * the capacity, it finds perfect triplet packings in shuffled order, and it proves that small
 * instances need more bins.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class BinCompletionTest {

  private static void assertPacking(int[] weights, int capacity, int bins, int[][] packing) {
    assertNotNull(packing);
    assertTrue(packing.length <= bins);
    List<Integer> packed = new ArrayList<>();
    for (int[] bin : packing) {
      assertTrue(Arrays.stream(bin).sum() <= capacity, Arrays.toString(bin));
      for (int x : bin) {
        packed.add(x);
      }
    }
    int[] got = packed.stream().mapToInt(Integer::intValue).sorted().toArray();
    int[] want = weights.clone();
    Arrays.sort(want);
    assertArrayEquals(want, got);
  }

  @Test
  void findsPerfectTripletPackingsInAnyOrder() {
    // Falkenauer-style triplets: each bin of capacity 1000 holds one item of 380..490 and two of
    // 250 or more that fill it exactly
    Random random = new Random(7);
    for (int trial = 0; trial < 20; trial++) {
      int bins = 10 + random.nextInt(20);
      List<Integer> items = new ArrayList<>();
      for (int b = 0; b < bins; b++) {
        int a = 380 + random.nextInt(111);
        int c = 250 + random.nextInt(1000 - a - 500 + 1);
        items.add(a);
        items.add(c);
        items.add(1000 - a - c);
      }
      Collections.shuffle(items, random);
      int[] weights = items.stream().mapToInt(Integer::intValue).toArray();
      long end = System.nanoTime() + 10_000_000_000L;
      int[][] packing =
          new BinCompletion(weights, 1000, bins, trial).run(() -> System.nanoTime() > end);
      assertPacking(weights, 1000, bins, packing);
      assertEquals(bins, packing.length);
    }
  }

  @Test
  void packsWithWasteAndRefutesTooFewBins() {
    // 5+4, 5+4, 3+3 in three bins of 9, 5+3, 5+3, 4+4 in three bins of 8; two bins hold at most
    // 18 < 24
    int[] weights = {5, 5, 4, 4, 3, 3};
    assertPacking(weights, 9, 3, new BinCompletion(weights, 9, 3, 1).run(() -> false));
    assertPacking(weights, 8, 3, new BinCompletion(weights, 8, 3, 1).run(() -> false));
    assertNull(new BinCompletion(weights, 9, 2, 1).run(() -> false));
    // three items of 6 in bins of 10: each bin holds one, so two bins are too few although 18 <= 20
    int[] sixes = {6, 6, 6};
    assertNull(new BinCompletion(sixes, 10, 2, 1).run(() -> false));
    assertPacking(sixes, 10, 3, new BinCompletion(sixes, 10, 3, 1).run(() -> false));
  }

  @Test
  void randomInstancesAgreeWithBruteForce() {
    Random random = new Random(11);
    for (int trial = 0; trial < 300; trial++) {
      int n = 1 + random.nextInt(7);
      int capacity = 5 + random.nextInt(10);
      int[] weights = new int[n];
      for (int i = 0; i < n; i++) {
        weights[i] = 1 + random.nextInt(capacity);
      }
      int optimum = bruteForce(weights, capacity);
      for (int bins = 1; bins <= n; bins++) {
        int[][] packing = new BinCompletion(weights, capacity, bins, trial).run(() -> false);
        if (bins < optimum) {
          assertNull(packing, Arrays.toString(weights) + " in " + bins + " bins of " + capacity);
        } else {
          assertPacking(weights, capacity, bins, packing);
        }
      }
    }
  }

  /** The fewest bins, by trying every assignment of items to bins. */
  private static int bruteForce(int[] weights, int capacity) {
    for (int bins = 1; ; bins++) {
      if (fits(weights, 0, new int[bins], capacity)) {
        return bins;
      }
    }
  }

  private static boolean fits(int[] weights, int i, int[] load, int capacity) {
    if (i == weights.length) {
      return true;
    }
    for (int b = 0; b < load.length; b++) {
      if (load[b] + weights[i] <= capacity) {
        load[b] += weights[i];
        boolean ok = fits(weights, i + 1, load, capacity);
        load[b] -= weights[i];
        if (ok) {
          return true;
        }
      }
    }
    return false;
  }
}
