/*
 * GraphAutomorphismsTest.java
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

package org.jacop.presolve;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.junit.jupiter.api.Test;

/**
 * Checks the generators of {@link GraphAutomorphisms}: each is an automorphism, and together they
 * generate the whole group, whose order is compared with known groups and with an enumeration of
 * all permutations of small random graphs.
 */
class GraphAutomorphismsTest {

  private static final long WORK = Long.MAX_VALUE;
  private static final long NANOS = 60_000_000_000L;

  @Test
  void knownGroups() {
    assertEquals(1, order(new int[1], edges(1)));
    assertEquals(720, order(new int[6], complete(6)));
    assertEquals(24, order(new int[12], cycle(12)));
    assertEquals(120, order(new int[10], petersen()));
    assertEquals(384, order(new int[16], hypercube(4)));
    assertEquals(120, order(new int[6], star(5)));
    // two disjoint triangles: 3! on each, and the swap of the triangles
    assertEquals(72, order(new int[6], union(cycle(3), cycle(3))));
    // colours: a cycle of six with alternate colours keeps the rotations by two and three
    // reflections
    assertEquals(6, order(new int[] {0, 1, 0, 1, 0, 1}, cycle(6)));
    // no edges, distinct colours
    assertEquals(1, order(new int[] {0, 1, 2, 3}, edges(4)));
  }

  @Test
  void randomGraphsHaveTheGroupOfAnEnumeration() {
    Random random = new Random(7);
    int trials = Integer.getInteger("automorphisms.trials", 400);
    int nontrivial = 0;
    for (int trial = 0; trial < trials; trial++) {
      int n = 1 + random.nextInt(8);
      int[] colors = new int[n];
      int k = 1 + random.nextInt(3);
      for (int v = 0; v < n; v++) {
        colors[v] = random.nextInt(k);
      }
      double p = random.nextDouble();
      int[][] adj = random(n, p, random);
      long expected = bruteForceOrder(colors, adj);
      assertEquals(expected, order(colors, adj), "trial " + trial + " " + Arrays.deepToString(adj));
      if (expected > 1) {
        nontrivial++;
      }
    }
    assertTrue(nontrivial > trials / 4, "nontrivial " + nontrivial);
  }

  @Test
  void theGroupOnInterestingVerticesIsFound() {
    Random random = new Random(13);
    int trials = Integer.getInteger("automorphisms.trials", 400);
    for (int trial = 0; trial < trials; trial++) {
      int n = 1 + random.nextInt(8);
      int[] colors = new int[n];
      boolean[] interesting = new boolean[n];
      for (int v = 0; v < n; v++) {
        colors[v] = random.nextInt(3);
        interesting[v] = random.nextInt(3) == 0;
      }
      List<Integer> order = new ArrayList<>();
      for (int v = 0; v < n; v++) {
        if (interesting[v]) {
          order.add(v);
        }
      }
      java.util.Collections.shuffle(order, random);
      int[][] adj = random(n, random.nextDouble(), random);
      GraphAutomorphisms.Result r =
          new GraphAutomorphisms(colors, adj, order.stream().mapToInt(Integer::intValue).toArray())
              .generators(WORK, NANOS);
      assertTrue(r.complete());
      Set<List<Integer>> expected = new HashSet<>();
      int[] p = new int[n];
      for (int i = 0; i < n; i++) {
        p[i] = i;
      }
      do {
        if (isAutomorphism(colors, adj, p)) {
          expected.add(restrict(p, interesting));
        }
      } while (nextPermutation(p));
      Set<List<Integer>> found = new HashSet<>();
      for (int[] g : arrays(n, r)) {
        assertTrue(isAutomorphism(colors, adj, g));
      }
      for (List<Integer> g : group(n, arrays(n, r))) {
        found.add(restrict(g.stream().mapToInt(Integer::intValue).toArray(), interesting));
      }
      assertEquals(expected, found, "trial " + trial + " " + Arrays.deepToString(adj));
    }
  }

  private static List<Integer> restrict(int[] g, boolean[] interesting) {
    List<Integer> l = new ArrayList<>();
    for (int v = 0; v < g.length; v++) {
      if (interesting[v]) {
        l.add(g[v]);
      }
    }
    return l;
  }

  @Test
  void regularGraphsHaveTheGroupOfAnEnumeration() {
    // vertex-transitive and regular graphs are where refinement alone tells least apart
    Random random = new Random(3);
    for (int trial = 0; trial < 30; trial++) {
      int n = 8;
      int[][] adj = randomRegular(n, 3, random);
      if (adj == null) {
        continue;
      }
      int[] colors = new int[n];
      assertEquals(bruteForceOrder(colors, adj), order(colors, adj), Arrays.deepToString(adj));
    }
  }

  @Test
  void aSmallBudgetReturnsAutomorphismsOnly() {
    int[][] adj = hypercube(5);
    int[] colors = new int[adj.length];
    GraphAutomorphisms.Result r = new GraphAutomorphisms(colors, adj).generators(500, NANOS);
    assertFalse(r.complete());
    for (int[] g : arrays(adj.length, r)) {
      assertTrue(isAutomorphism(colors, adj, g));
    }
  }

  private static long order(int[] colors, int[][] adj) {
    GraphAutomorphisms.Result r = new GraphAutomorphisms(colors, adj).generators(WORK, NANOS);
    assertTrue(r.complete());
    for (int[] g : arrays(colors.length, r)) {
      assertTrue(isAutomorphism(colors, adj, g), Arrays.toString(g));
    }
    return closure(colors.length, arrays(colors.length, r));
  }

  private static List<int[]> arrays(int n, GraphAutomorphisms.Result r) {
    return r.generators().stream().map(g -> g.toArray(n)).toList();
  }

  private static long closure(int n, List<int[]> generators) {
    return group(n, generators).size();
  }

  private static Set<List<Integer>> group(int n, List<int[]> generators) {
    Set<List<Integer>> seen = new HashSet<>();
    Deque<int[]> queue = new ArrayDeque<>();
    int[] id = new int[n];
    for (int i = 0; i < n; i++) {
      id[i] = i;
    }
    seen.add(asList(id));
    queue.add(id);
    while (!queue.isEmpty()) {
      int[] p = queue.poll();
      for (int[] g : generators) {
        int[] q = new int[n];
        for (int i = 0; i < n; i++) {
          q[i] = g[p[i]];
        }
        if (seen.add(asList(q))) {
          queue.add(q);
        }
      }
    }
    return seen;
  }

  private static List<Integer> asList(int[] a) {
    List<Integer> l = new ArrayList<>(a.length);
    for (int x : a) {
      l.add(x);
    }
    return l;
  }

  private static long bruteForceOrder(int[] colors, int[][] adj) {
    int n = colors.length;
    int[] p = new int[n];
    for (int i = 0; i < n; i++) {
      p[i] = i;
    }
    long count = 0;
    do {
      if (isAutomorphism(colors, adj, p)) {
        count++;
      }
    } while (nextPermutation(p));
    return count;
  }

  private static boolean nextPermutation(int[] p) {
    int i = p.length - 2;
    while (i >= 0 && p[i] >= p[i + 1]) {
      i--;
    }
    if (i < 0) {
      return false;
    }
    int j = p.length - 1;
    while (p[j] <= p[i]) {
      j--;
    }
    int t = p[i];
    p[i] = p[j];
    p[j] = t;
    for (int a = i + 1, b = p.length - 1; a < b; a++, b--) {
      t = p[a];
      p[a] = p[b];
      p[b] = t;
    }
    return true;
  }

  private static boolean isAutomorphism(int[] colors, int[][] adj, int[] g) {
    int n = colors.length;
    boolean[] image = new boolean[n];
    for (int v = 0; v < n; v++) {
      if (colors[v] != colors[g[v]] || image[g[v]]) {
        return false;
      }
      image[g[v]] = true;
    }
    for (int v = 0; v < n; v++) {
      Set<Integer> targets = new HashSet<>();
      for (int u : adj[g[v]]) {
        targets.add(u);
      }
      Set<Integer> mapped = new HashSet<>();
      for (int u : adj[v]) {
        mapped.add(g[u]);
      }
      if (!targets.equals(mapped)) {
        return false;
      }
    }
    return true;
  }

  private static int[][] edges(int n, int... pairs) {
    List<List<Integer>> a = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      a.add(new ArrayList<>());
    }
    for (int i = 0; i < pairs.length; i += 2) {
      a.get(pairs[i]).add(pairs[i + 1]);
      a.get(pairs[i + 1]).add(pairs[i]);
    }
    return a.stream()
        .map(l -> l.stream().mapToInt(Integer::intValue).toArray())
        .toArray(int[][]::new);
  }

  private static int[][] complete(int n) {
    List<Integer> pairs = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        pairs.add(i);
        pairs.add(j);
      }
    }
    return edges(n, pairs.stream().mapToInt(Integer::intValue).toArray());
  }

  private static int[][] cycle(int n) {
    int[] pairs = new int[2 * n];
    for (int i = 0; i < n; i++) {
      pairs[2 * i] = i;
      pairs[2 * i + 1] = (i + 1) % n;
    }
    return edges(n, pairs);
  }

  private static int[][] star(int leaves) {
    int[] pairs = new int[2 * leaves];
    for (int i = 0; i < leaves; i++) {
      pairs[2 * i] = 0;
      pairs[2 * i + 1] = i + 1;
    }
    return edges(leaves + 1, pairs);
  }

  private static int[][] petersen() {
    return edges(
        10, 0, 1, 1, 2, 2, 3, 3, 4, 4, 0, 0, 5, 1, 6, 2, 7, 3, 8, 4, 9, 5, 7, 7, 9, 9, 6, 6, 8, 8,
        5);
  }

  private static int[][] hypercube(int d) {
    int n = 1 << d;
    List<Integer> pairs = new ArrayList<>();
    for (int v = 0; v < n; v++) {
      for (int b = 0; b < d; b++) {
        int u = v ^ (1 << b);
        if (v < u) {
          pairs.add(v);
          pairs.add(u);
        }
      }
    }
    return edges(n, pairs.stream().mapToInt(Integer::intValue).toArray());
  }

  private static int[][] union(int[][] a, int[][] b) {
    int[][] r = new int[a.length + b.length][];
    for (int v = 0; v < a.length; v++) {
      r[v] = a[v].clone();
    }
    for (int v = 0; v < b.length; v++) {
      r[a.length + v] = Arrays.stream(b[v]).map(u -> u + a.length).toArray();
    }
    return r;
  }

  private static int[][] random(int n, double p, Random random) {
    List<Integer> pairs = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (random.nextDouble() < p) {
          pairs.add(i);
          pairs.add(j);
        }
      }
    }
    return edges(n, pairs.stream().mapToInt(Integer::intValue).toArray());
  }

  /** A random d-regular simple graph by the pairing model, or null if the pairing failed. */
  private static int[][] randomRegular(int n, int d, Random random) {
    List<Integer> points = new ArrayList<>();
    for (int v = 0; v < n; v++) {
      for (int k = 0; k < d; k++) {
        points.add(v);
      }
    }
    java.util.Collections.shuffle(points, random);
    Set<Long> seen = new HashSet<>();
    int[] pairs = new int[points.size()];
    for (int i = 0; i < points.size(); i += 2) {
      int a = points.get(i);
      int b = points.get(i + 1);
      if (a == b || !seen.add((long) Math.min(a, b) * n + Math.max(a, b))) {
        return null;
      }
      pairs[i] = a;
      pairs[i + 1] = b;
    }
    return edges(n, pairs);
  }
}
