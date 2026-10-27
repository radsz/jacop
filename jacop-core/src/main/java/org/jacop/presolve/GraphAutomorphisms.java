/*
 * GraphAutomorphisms.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Finds generators of the automorphism group of a vertex-coloured undirected graph, the way
 * symmetry detection in CP and MIP presolve does it (Puget, "Automatic detection of variable and
 * value symmetries", CP 2005; CP-SAT's {@code find_graph_symmetries}): a model is turned into a
 * graph whose automorphisms are symmetries of the model, and the generators found here are broken
 * by the caller.
 *
 * <p>The search is individualization and refinement, as in nauty, saucy and bliss. The colouring is
 * refined to the coarsest equitable partition; the first path individualizes the smallest vertex of
 * the first non-singleton cell (interesting vertices first, see {@link #GraphAutomorphisms(int[],
 * int[][], int[])}) until the partition is discrete. Then, from the deepest level up, for each
 * vertex {@code w} of the cell individualized at level {@code k} that is not yet in the orbit of
 * the vertex chosen there, it searches for an automorphism that fixes the vertices chosen above
 * {@code k} and maps the chosen vertex to {@code w}: the other side individualizes {@code w} and
 * then, level by level, each vertex of the corresponding cell, prunes every branch whose refinement
 * differs from the first path, and compares each discrete partition it reaches with the first leaf.
 * With enough budget the generators found generate the whole group (the Schreier-Sims argument over
 * the stabilizer chain of the first path).
 *
 * <p>The work is kept proportional to what changes: a split moves only the vertices the splitter
 * reaches, an individualized vertex leaves the rest of its cell in place, partitions are undone
 * from a trail, and a candidate leaf is compared with the first leaf only at the positions the
 * search wrote, so generators are sparse ({@link Permutation}).
 *
 * <p>Every generator returned is checked against the edges, so it is an automorphism whatever the
 * budget; a search cut short by the budget only misses generators ({@link Result#complete()} is
 * then false).
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class GraphAutomorphisms {

  /**
   * Generators found.
   *
   * @param generators permutations of the vertices.
   * @param complete true if the search ran to the end, so the generators generate the whole group.
   */
  public record Result(List<Permutation> generators, boolean complete) {}

  /**
   * A permutation of the vertices, given by the vertices it moves.
   *
   * @param points the vertices moved, in increasing order.
   * @param images the image of each of them.
   */
  public record Permutation(int[] points, int[] images) {

    /**
     * Returns the image of a vertex.
     *
     * @param v a vertex.
     * @return its image.
     */
    public int image(int v) {
      int i = Arrays.binarySearch(points, v);
      return i < 0 ? v : images[i];
    }

    /**
     * Returns the permutation as an array.
     *
     * @param n the number of vertices.
     * @return the array whose element v is the image of v.
     */
    public int[] toArray(int n) {
      int[] g = new int[n];
      for (int v = 0; v < n; v++) {
        g[v] = v;
      }
      for (int i = 0; i < points.length; i++) {
        g[points[i]] = images[i];
      }
      return g;
    }
  }

  /** The largest number of vertices. */
  public static final int MAX_VERTICES = (1 << 21) - 1;

  private static final long MASK = (1L << 21) - 1;

  private static final class OutOfBudget extends RuntimeException {
    OutOfBudget() {
      super(null, null, false, false);
    }
  }

  private final int n;
  private final int[] color;
  private final int[] interesting;
  private final int[][] adj;

  // the partition: elements in cell order; a cell is identified by the position of its first
  // element, and cellEnd is valid at those positions
  private final int[] elems;
  private final int[] pos;
  private final int[] cellOf;
  private final int[] cellEnd;
  private int cells;

  // splits, undone in reverse order: pairs (cell, piece split off from it)
  private int[] trail = new int[64];
  private int trailSize;

  // refinement scratch
  private final int[] count;
  private final int[] touched;
  private final boolean[] queued;
  private final int[] queue;
  private int head;
  private int tail;
  private long[] sortBuffer = new long[16];

  // the search for one automorphism: its stack, the identity outside the vertices it moves, and
  // the log of the positions it writes
  private int[][] candidates;
  private int[] next;
  private int[] marks;
  private int[] image;
  private int[] stamp;
  private int stampValue;
  private boolean logging;
  private int[] logPos = new int[64];
  private int[] logOld = new int[64];
  private int logSize;

  private long work;
  private long workLimit;
  private long deadline;

  /**
   * Prepares the search on a graph.
   *
   * @param colors the colour of each vertex; automorphisms map a vertex to one of the same colour.
   * @param adjacency the neighbours of each vertex; the graph is undirected, so every edge has to
   *     be listed at both ends. Duplicates and loops are ignored.
   */
  public GraphAutomorphisms(int[] colors, int[][] adjacency) {
    this(colors, adjacency, null);
  }

  /**
   * Prepares the search on a graph where only the images of some vertices matter. The search then
   * returns generators of the group the automorphisms make on those vertices, and saves the work of
   * finding automorphisms that fix them all: the first path individualizes them first, in the order
   * given, and no automorphism is searched below the level where they are all fixed. A generator
   * may still be the identity on them. The order is the base of the stabilizer chain: the
   * generators found at the level of a vertex fix every vertex before it, which suits lex-leader
   * constraints that compare the vertices in the same order.
   *
   * @param colors the colour of each vertex; automorphisms map a vertex to one of the same colour.
   * @param adjacency the neighbours of each vertex, as for {@link #GraphAutomorphisms(int[],
   *     int[][])}.
   * @param interesting the vertices whose images matter, in the order they are individualized, or
   *     null for all.
   */
  public GraphAutomorphisms(int[] colors, int[][] adjacency, int[] interesting) {
    if (colors.length != adjacency.length) {
      throw new IllegalArgumentException("One colour and one adjacency list per vertex expected");
    }
    n = colors.length;
    if (n > MAX_VERTICES) {
      throw new IllegalArgumentException("More than " + MAX_VERTICES + " vertices");
    }
    color = colors.clone();
    this.interesting = interesting == null ? null : interesting.clone();
    if (interesting != null) {
      for (int v : interesting) {
        if (v < 0 || v >= n) {
          throw new IllegalArgumentException("No vertex " + v);
        }
      }
    }
    adj = new int[n][];
    for (int v = 0; v < n; v++) {
      int[] a = adjacency[v].clone();
      Arrays.sort(a);
      int k = 0;
      for (int i = 0; i < a.length; i++) {
        if (a[i] != v && (k == 0 || a[k - 1] != a[i])) {
          a[k++] = a[i];
        }
      }
      adj[v] = Arrays.copyOf(a, k);
    }
    for (int v = 0; v < n; v++) {
      for (int u : adj[v]) {
        if (Arrays.binarySearch(adj[u], v) < 0) {
          throw new IllegalArgumentException("Edge " + v + "-" + u + " is listed at one end only");
        }
      }
    }
    elems = new int[n];
    pos = new int[n];
    cellOf = new int[n];
    cellEnd = new int[n + 1];
    count = new int[n];
    touched = new int[n];
    queued = new boolean[n];
    queue = new int[n + 1];
  }

  /**
   * Searches for generators.
   *
   * @param maxWork the largest number of adjacency entries the search reads; the search stops when
   *     it has read more.
   * @param maxNanos the longest time the search runs, in nanoseconds.
   * @return the generators found.
   */
  public Result generators(long maxWork, long maxNanos) {
    work = 0;
    workLimit = maxWork;
    deadline = System.nanoTime() + maxNanos;
    List<Permutation> generators = new ArrayList<>();
    if (n == 0) {
      return new Result(generators, true);
    }
    try {
      search(generators);
      return new Result(generators, true);
    } catch (OutOfBudget _) {
      return new Result(generators, false);
    }
  }

  private void search(List<Permutation> generators) {
    initialPartition();
    refine();

    // the first path, through the cells of interesting vertices first
    List<int[]> levels = new ArrayList<>(); // {mark, target cell, target size, chosen, cells}
    List<Long> traces = new ArrayList<>();
    int first = 0;
    int nextInteresting = 0;
    int relevant = interesting == null ? -1 : -2;
    while (cells < n) {
      int chosen;
      if (relevant == -2 && interesting != null) {
        while (nextInteresting < interesting.length
            && cellEnd[cellOf[interesting[nextInteresting]]] - cellOf[interesting[nextInteresting]]
                == 1) {
          nextInteresting++;
        }
        if (nextInteresting == interesting.length) {
          // every interesting vertex is fixed: what lies below moves none of them
          relevant = levels.size();
          if (relevant == 0) {
            return;
          }
          first = 0;
          continue;
        }
        chosen = interesting[nextInteresting];
        first = cellOf[chosen];
      } else {
        first = firstNonSingleton(first);
        chosen = smallest(first);
      }
      int mark = trailSize;
      int size = cellEnd[first] - first;
      individualize(chosen);
      long trace = refine();
      levels.add(new int[] {mark, first, size, chosen, cells});
      traces.add(trace);
    }
    if (relevant < 0) {
      relevant = levels.size();
    }
    int[] leaf = elems.clone();
    int depth = levels.size();
    long[] trace = new long[depth];
    for (int k = 0; k < depth; k++) {
      trace[k] = traces.get(k);
    }
    candidates = new int[depth][];
    next = new int[depth];
    marks = new int[depth];
    image = new int[n];
    for (int v = 0; v < n; v++) {
      image[v] = v;
    }
    stamp = new int[n];

    int[] orbit = new int[n];
    for (int v = 0; v < n; v++) {
      orbit[v] = v;
    }
    for (int k = relevant - 1; k >= 0; k--) {
      int[] level = levels.get(k);
      undo(level[0]);
      int chosen = level[3];
      int[] candidates = cellElements(level[1]);
      Arrays.sort(candidates);
      for (int w : candidates) {
        if (w == chosen || find(orbit, w) == find(orbit, chosen)) {
          continue;
        }
        Permutation g = mapTo(levels, trace, leaf, k, w);
        if (g != null) {
          generators.add(g);
          for (int i = 0; i < g.points().length; i++) {
            union(orbit, g.points()[i], g.images()[i]);
          }
        }
      }
    }
  }

  /**
   * Searches for an automorphism that fixes what the first path fixes above level k and maps the
   * vertex chosen at level k to w. The partition is the first path's at level k, its elements in
   * the order of the first leaf, and is left so: the positions written are logged and restored, so
   * at a leaf only they can differ from the first leaf.
   */
  private Permutation mapTo(List<int[]> levels, long[] trace, int[] leaf, int k, int w) {
    candidates[k] = new int[] {w};
    next[k] = 0;
    int level = k;
    int base = trailSize;
    logSize = 0;
    logging = true;
    try {
      while (true) {
        if (next[level] == candidates[level].length) {
          if (level == k) {
            undo(base);
            return null;
          }
          level--;
          undo(marks[level]);
          continue;
        }
        int u = candidates[level][next[level]++];
        marks[level] = trailSize;
        individualize(u);
        long t = refine();
        int[] expected = levels.get(level);
        if (t != trace[level] || cells != expected[4]) {
          undo(marks[level]);
          continue;
        }
        if (cells == n) {
          Permutation g = leafAutomorphism(leaf);
          if (g != null) {
            undo(base);
            return g;
          }
          undo(marks[level]);
          continue;
        }
        int[] below = levels.get(level + 1);
        if (cellEnd[below[1]] - below[1] != below[2]) {
          undo(marks[level]);
          continue;
        }
        // the vertex the first path chose is tried first: it is the image under many symmetries
        int[] cell = cellElements(below[1]);
        for (int i = 0; i < cell.length; i++) {
          if (cell[i] == below[3]) {
            cell[i] = cell[0];
            cell[0] = below[3];
            break;
          }
        }
        level++;
        candidates[level] = cell;
        next[level] = 0;
      }
    } finally {
      logging = false;
      for (int i = logSize - 1; i >= 0; i--) {
        elems[logPos[i]] = logOld[i];
      }
      for (int i = 0; i < logSize; i++) {
        pos[elems[logPos[i]]] = logPos[i];
      }
      logSize = 0;
    }
  }

  /**
   * The map from the first leaf to the discrete partition reached, if it is an automorphism. Only
   * the positions written since the search started can differ from the first leaf.
   */
  private Permutation leafAutomorphism(int[] leaf) {
    stampValue++;
    int moved = 0;
    int[] points = new int[16];
    for (int i = 0; i < logSize; i++) {
      int p = logPos[i];
      if (stamp[p] == stampValue) {
        continue;
      }
      stamp[p] = stampValue;
      if (elems[p] != leaf[p]) {
        if (moved == points.length) {
          points = Arrays.copyOf(points, 2 * moved);
        }
        points[moved++] = leaf[p];
        image[leaf[p]] = elems[p];
      }
    }
    boolean automorphism = true;
    for (int i = 0; i < moved && automorphism; i++) {
      int v = points[i];
      int gv = image[v];
      if (color[v] != color[gv] || adj[v].length != adj[gv].length) {
        automorphism = false;
        break;
      }
      int[] target = adj[gv];
      spend(adj[v].length);
      for (int u : adj[v]) {
        if (Arrays.binarySearch(target, image[u]) < 0) {
          automorphism = false;
          break;
        }
      }
    }
    Permutation g = null;
    if (automorphism) {
      int[] sorted = Arrays.copyOf(points, moved);
      Arrays.sort(sorted);
      int[] images = new int[moved];
      for (int i = 0; i < moved; i++) {
        images[i] = image[sorted[i]];
      }
      g = new Permutation(sorted, images);
    }
    for (int i = 0; i < moved; i++) {
      image[points[i]] = points[i];
    }
    return g;
  }

  private void initialPartition() {
    Integer[] order = new Integer[n];
    for (int v = 0; v < n; v++) {
      order[v] = v;
    }
    Arrays.sort(
        order, (a, b) -> color[a] != color[b] ? Integer.compare(color[a], color[b]) : a - b);
    cells = 0;
    for (int i = 0; i < n; i++) {
      int v = order[i];
      elems[i] = v;
      pos[v] = i;
    }
    int start = 0;
    for (int i = 1; i <= n; i++) {
      if (i == n || color[elems[i]] != color[elems[start]]) {
        cellEnd[start] = i;
        for (int j = start; j < i; j++) {
          cellOf[elems[j]] = start;
        }
        cells++;
        enqueue(start);
        start = i;
      }
    }
    trailSize = 0;
  }

  private int firstNonSingleton(int from) {
    int c = from;
    while (cellEnd[c] - c == 1) {
      c = cellEnd[c];
    }
    return c;
  }

  private int smallest(int cell) {
    int best = Integer.MAX_VALUE;
    for (int i = cell; i < cellEnd[cell]; i++) {
      best = Math.min(best, elems[i]);
    }
    return best;
  }

  private int[] cellElements(int cell) {
    return Arrays.copyOfRange(elems, cell, cellEnd[cell]);
  }

  /**
   * Splits v off the end of its cell as a cell of its own; the rest keeps the cell's position, so
   * neither this nor its undo touches the rest.
   */
  private void individualize(int v) {
    int c = cellOf[v];
    int end = cellEnd[c];
    int last = end - 1;
    int pv = pos[v];
    int u = elems[last];
    place(last, v);
    place(pv, u);
    cellEnd[c] = last;
    cellEnd[last] = end;
    cellOf[v] = last;
    push(c, last);
    cells++;
    // the rest needs no splitting: its counts are those of the old cell minus those of v
    enqueue(last);
  }

  /**
   * Refines the partition until it is equitable, splitting by the cells in the queue (Hopcroft's
   * scheme: of the pieces of a cell that is not queued, all but the largest are queued). Returns a
   * hash of what was split, in order; refinements related by an automorphism give the same hash.
   * The work of a splitter is proportional to the edges it has and the vertices they reach, not to
   * the size of the cells it splits.
   */
  private long refine() {
    long h = 1;
    while (head != tail) {
      int s = queue[head];
      head = head == n ? 0 : head + 1;
      queued[s] = false;
      int end = cellEnd[s];
      int nt = 0;
      for (int i = s; i < end; i++) {
        int[] a = adj[elems[i]];
        spend(a.length);
        for (int u : a) {
          if (count[u]++ == 0) {
            touched[nt++] = u;
          }
        }
      }
      // touched vertices by cell, then by count
      if (sortBuffer.length < nt) {
        sortBuffer = new long[Math.max(nt, 2 * sortBuffer.length)];
      }
      for (int t = 0; t < nt; t++) {
        int u = touched[t];
        sortBuffer[t] = ((long) cellOf[u] << 42) | ((long) count[u] << 21) | u;
      }
      Arrays.sort(sortBuffer, 0, nt);
      h = mix(h, s);
      int from = 0;
      while (from < nt) {
        int c = (int) (sortBuffer[from] >>> 42);
        int to = from + 1;
        while (to < nt && (int) (sortBuffer[to] >>> 42) == c) {
          to++;
        }
        h = split(c, from, to, h);
        from = to;
      }
      for (int t = 0; t < nt; t++) {
        count[touched[t]] = 0;
      }
    }
    return h;
  }

  private static int countOf(long key) {
    return (int) ((key >>> 21) & MASK);
  }

  private static int vertexOf(long key) {
    return (int) (key & MASK);
  }

  /**
   * Splits cell c by the counts of its touched vertices, sortBuffer[from..to) in increasing count;
   * the other vertices of the cell have count 0. The untouched vertices stay at the front and keep
   * the cell; the touched ones move to the back, one piece per count.
   */
  private long split(int c, int from, int to, long h) {
    int end = cellEnd[c];
    int size = end - c;
    int t = to - from;
    h = mix(h, c);
    if (t == size && countOf(sortBuffer[from]) == countOf(sortBuffer[to - 1])) {
      return mix(h, countOf(sortBuffer[from]));
    }
    // the touched vertices to the back
    int b = end - t;
    int q = b;
    for (int k = from; k < to; k++) {
      int u = vertexOf(sortBuffer[k]);
      if (pos[u] < b) {
        while (count[elems[q]] > 0) {
          q++;
        }
        int w = elems[q];
        place(pos[u], w);
        place(q, u);
      }
    }
    for (int k = from; k < to; k++) {
      place(b + k - from, vertexOf(sortBuffer[k]));
    }
    // pieces in increasing count: the untouched part first, if any
    int pieces = 0;
    int largest = c;
    int largestSize = -1;
    if (b > c) {
      pieces++;
      largestSize = b - c;
      h = mix(mix(h, 0), b - c);
    }
    int start = b;
    for (int k = from; k < to; k++) {
      if (k + 1 == to || countOf(sortBuffer[k + 1]) != countOf(sortBuffer[k])) {
        int pEnd = b + k + 1 - from;
        pieces++;
        h = mix(mix(h, countOf(sortBuffer[k])), pEnd - start);
        if (pEnd - start > largestSize) {
          largestSize = pEnd - start;
          largest = start;
        }
        start = pEnd;
      }
    }
    // the pieces after the first, split off from the back so that undo merges them in order
    int pieceEnd = end;
    for (int k = to - 1; k >= from; k--) {
      int p = b + k - from;
      boolean boundary = k == from ? b > c : countOf(sortBuffer[k - 1]) != countOf(sortBuffer[k]);
      if (boundary) {
        cellEnd[p] = pieceEnd;
        for (int j = p; j < pieceEnd; j++) {
          cellOf[elems[j]] = p;
        }
        push(c, p);
        pieceEnd = p;
      }
    }
    cellEnd[c] = pieceEnd;
    cells += pieces - 1;

    boolean all = queued[c];
    for (int p = c; p < end; p = cellEnd[p]) {
      if (all || p != largest) {
        enqueue(p);
      }
    }
    return h;
  }

  /** Puts v at position p, logging the position while an automorphism is searched for. */
  private void place(int p, int v) {
    if (logging) {
      if (logSize == logPos.length) {
        logPos = Arrays.copyOf(logPos, 2 * logSize);
        logOld = Arrays.copyOf(logOld, 2 * logSize);
      }
      logPos[logSize] = p;
      logOld[logSize++] = elems[p];
    }
    elems[p] = v;
    pos[v] = p;
  }

  private void enqueue(int c) {
    if (!queued[c]) {
      queued[c] = true;
      queue[tail] = c;
      tail = tail == n ? 0 : tail + 1;
    }
  }

  private void push(int cell, int piece) {
    if (trailSize + 2 > trail.length) {
      trail = Arrays.copyOf(trail, 2 * trail.length);
    }
    trail[trailSize++] = cell;
    trail[trailSize++] = piece;
  }

  private void undo(int mark) {
    while (trailSize > mark) {
      int piece = trail[--trailSize];
      int cell = trail[--trailSize];
      int end = cellEnd[piece];
      for (int i = piece; i < end; i++) {
        cellOf[elems[i]] = cell;
      }
      cellEnd[cell] = end;
      cells--;
    }
  }

  private void spend(long w) {
    work += w;
    if (work > workLimit) {
      throw new OutOfBudget();
    }
    if ((work & 0xFFFF) < w && System.nanoTime() > deadline) {
      throw new OutOfBudget();
    }
  }

  private static long mix(long h, long x) {
    long z = (h ^ x) * 0x9E3779B97F4A7C15L;
    return z ^ (z >>> 31);
  }

  private static int find(int[] parent, int v) {
    while (parent[v] != v) {
      parent[v] = parent[parent[v]];
      v = parent[v];
    }
    return v;
  }

  private static void union(int[] parent, int a, int b) {
    int ra = find(parent, a);
    int rb = find(parent, b);
    if (ra != rb) {
      parent[Math.max(ra, rb)] = Math.min(ra, rb);
    }
  }
}
