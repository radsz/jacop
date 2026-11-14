/*
 * GeostInstanceGenerator.java
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

package org.jacop.geost;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.TreeSet;
import org.jacop.geost.GeostInstance.Area;
import org.jacop.geost.GeostInstance.Box;
import org.jacop.geost.GeostInstance.NonOverlap;
import org.jacop.geost.GeostInstance.Obj;

/**
 * Generates families of small random Geost instances. Every family stresses one feature of the
 * constraint; the instances are small enough to enumerate all solutions by brute force.
 *
 * <p>Run {@link #main} to rewrite the corpus used by {@code GeostBruteForceTest}:
 *
 * <pre>
 * java -cp ... org.jacop.geost.GeostInstanceGenerator jacop-core/src/test/resources/geost/corpus.txt 60
 * </pre>
 *
 * <p>The second argument is the number of instances per family.
 */
public final class GeostInstanceGenerator {

  /** A family of instances. */
  public enum Family {
    /** 1-D segments, single-box shapes, some objects choose among lengths. */
    SEG1D,
    /** 1-D shapes made of several segments with gaps (other objects fit into the gaps). */
    MULTISEG1D,
    /** 2-D rectangles, some objects choose an orientation. */
    RECT2D,
    /** 2-D polyomino-like shapes with holes and non-convex outlines, polymorphic objects. */
    POLY2D,
    /** 3-D boxes. */
    BOX3D,
    /** 1-D and 2-D objects with variable start, duration and end in the time dimension. */
    TIME,
    /** Non-overlap over a random subset of the dimensions, with and without time. */
    SUBDIMS,
    /** Several non-overlap constraints over different subsets of objects. */
    MULTI,
    /** 2-D objects inside an area with holes. */
    AREA,
    /** Negative coordinates and negative shape offsets. */
    NEGATIVE,
    /** Objects that are partly or fully fixed when the constraint is posted. */
    FIXED,
    /** Tight packings of small polyominoes into a small area (exact covers and near covers). */
    TILING,
    /** Everything mixed, object numbers not contiguous. */
    MIXED
  }

  private final Random random;

  public GeostInstanceGenerator(long seed) {
    random = new Random(seed);
  }

  /** Product of the domain sizes, to keep brute force cheap. */
  static double space(GeostInstance g) {
    double p = 1;
    for (Obj o : g.objects) {
      for (int[] c : o.coords()) {
        p *= c.length;
      }
      p *= o.shape().length * o.start().length * o.dur().length;
    }
    return p;
  }

  public GeostInstance generate(Family family, String name) {
    while (true) {
      GeostInstance g = attempt(family, name);
      if (space(g) <= 3e7) {
        return g;
      }
    }
  }

  private GeostInstance attempt(Family f, String name) {
    return switch (f) {
      case SEG1D -> seg1d(name, false);
      case MULTISEG1D -> seg1d(name, true);
      case RECT2D -> rect2d(name, false, false);
      case POLY2D -> poly2d(name, false);
      case BOX3D -> box3d(name);
      case TIME -> time(name);
      case SUBDIMS -> subdims(name);
      case MULTI -> multi(name);
      case AREA -> rect2d(name, true, false);
      case NEGATIVE -> random.nextBoolean() ? rect2d(name, false, true) : poly2d(name, true);
      case FIXED -> fixed(name);
      case TILING -> tiling(name);
      case MIXED -> mixed(name);
    };
  }

  // ---------------------------------------------------------------------------------------------
  // helpers

  int between(int lo, int hi) {
    return lo + random.nextInt(hi - lo + 1);
  }

  /** Values lo..hi with some removed (at least one kept). */
  int[] domain(int lo, int hi, int holeOneIn) {
    List<Integer> values = new ArrayList<>();
    for (int v = lo; v <= hi; v++) {
      if (holeOneIn <= 0 || random.nextInt(holeOneIn) != 0) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(between(lo, hi));
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  int[] coordDomain(int lo, int maxSize) {
    int size = between(1, maxSize);
    return domain(lo, lo + size - 1, random.nextInt(3) == 0 ? 4 : 0);
  }

  /** A random nonempty subset of 0..n-1 of at most max elements. */
  int[] subset(int n, int max) {
    List<Integer> all = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      all.add(i);
    }
    Collections.shuffle(all, random);
    int size = between(1, Math.min(max, n));
    return all.subList(0, size).stream().mapToInt(Integer::intValue).sorted().toArray();
  }

  static int[] range(int n) {
    int[] r = new int[n];
    for (int i = 0; i < n; i++) {
      r[i] = i;
    }
    return r;
  }

  static int[] one(int v) {
    return new int[] {v};
  }

  /** An object with the fixed time interval [0, 1) that the FlatZinc front end uses. */
  static Obj spatial(int no, int[][] coords, int[] shape) {
    return new Obj(no, coords, shape, one(0), one(1), one(1));
  }

  /** All dimensions plus time, as posted by the FlatZinc front end. */
  static int[] allDims(int k) {
    return range(k + 1);
  }

  static Box box(int[] offset, int[] length) {
    return new Box(offset, length);
  }

  /** A polyomino-like shape: a random set of cells of a w x h grid, one box per row run. */
  List<Box> cells2d(int w, int h, int cells, int dx, int dy) {
    boolean[][] grid = new boolean[w][h];
    int placed = 0;
    // grow from a random cell so that most shapes are connected
    int cx = random.nextInt(w);
    int cy = random.nextInt(h);
    grid[cx][cy] = true;
    placed++;
    int tries = 0;
    while (placed < cells && tries++ < 100) {
      int x = random.nextInt(w);
      int y = random.nextInt(h);
      if (grid[x][y]) {
        continue;
      }
      boolean near =
          (x > 0 && grid[x - 1][y])
              || (x + 1 < w && grid[x + 1][y])
              || (y > 0 && grid[x][y - 1])
              || (y + 1 < h && grid[x][y + 1]);
      if (near || random.nextInt(5) == 0) {
        grid[x][y] = true;
        placed++;
      }
    }
    List<Box> boxes = new ArrayList<>();
    for (int y = 0; y < h; y++) {
      int x = 0;
      while (x < w) {
        if (!grid[x][y]) {
          x++;
          continue;
        }
        int start = x;
        while (x < w && grid[x][y]) {
          x++;
        }
        boxes.add(box(new int[] {start + dx, y + dy}, new int[] {x - start, 1}));
      }
    }
    return boxes;
  }

  // ---------------------------------------------------------------------------------------------
  // families

  private GeostInstance seg1d(String name, boolean multi) {
    List<List<Box>> shapes = new ArrayList<>();
    int ns = between(1, 4);
    for (int s = 0; s < ns; s++) {
      List<Box> boxes = new ArrayList<>();
      if (multi && random.nextBoolean()) {
        int pos = between(-1, 1);
        int pieces = between(2, 3);
        for (int p = 0; p < pieces; p++) {
          int len = between(1, 2);
          boxes.add(box(one(pos), one(len)));
          pos += len + between(1, 2);
        }
      } else {
        boxes.add(box(one(multi ? between(-1, 1) : 0), one(between(1, 3))));
      }
      shapes.add(boxes);
    }
    int n = between(2, 4);
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      objects.add(spatial(i, new int[][] {coordDomain(between(0, 3), 6)}, subset(ns, 2)));
    }
    List<NonOverlap> no = List.of(new NonOverlap(range(n), allDims(1)));
    return new GeostInstance(name, 1, shapes, objects, no, null);
  }

  private List<List<Box>> rectangles(int ns, int maxSide) {
    List<List<Box>> shapes = new ArrayList<>();
    for (int s = 0; s < ns; s++) {
      int w = between(1, maxSide);
      int h = between(1, maxSide);
      shapes.add(List.of(box(new int[] {0, 0}, new int[] {w, h})));
      if (s + 1 < ns && random.nextBoolean()) {
        // its rotation
        shapes.add(List.of(box(new int[] {0, 0}, new int[] {h, w})));
        s++;
      }
    }
    return shapes;
  }

  private GeostInstance rect2d(String name, boolean area, boolean negative) {
    int ns = between(1, 4);
    List<List<Box>> shapes = rectangles(ns, 3);
    if (negative) {
      // shift some shapes so that their boxes start left of or below the origin
      List<List<Box>> shifted = new ArrayList<>();
      for (List<Box> s : shapes) {
        Box b = s.get(0);
        shifted.add(
            List.of(
                box(
                    new int[] {b.offset()[0] - between(0, 2), b.offset()[1] - between(0, 2)},
                    b.length())));
      }
      shapes = shifted;
    }
    int n = between(2, 4);
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int lo = negative ? between(-4, 0) : between(0, 2);
      objects.add(
          spatial(
              i,
              new int[][] {
                coordDomain(lo, 4), coordDomain(negative ? between(-4, 0) : between(0, 2), 4)
              },
              subset(shapes.size(), 2)));
    }
    Area a = null;
    if (area) {
      // the area does not always start at 0
      int ax = between(0, 1);
      int ay = between(0, 1);
      int w = between(4, 7);
      int h = between(4, 7);
      List<Box> holes = new ArrayList<>();
      int nh = between(0, 2);
      for (int i = 0; i < nh; i++) {
        holes.add(
            box(
                new int[] {ax + between(0, w - 1), ay + between(0, h - 1)},
                new int[] {between(1, 2), between(1, 2)}));
      }
      a = new Area(box(new int[] {ax, ay}, new int[] {w, h}), holes);
    }
    List<NonOverlap> no = List.of(new NonOverlap(range(n), allDims(2)));
    return new GeostInstance(name, 2, shapes, objects, no, a);
  }

  private List<List<Box>> polyShapes(int ns, boolean negative) {
    List<List<Box>> shapes = new ArrayList<>();
    for (int s = 0; s < ns; s++) {
      int dx = negative ? between(-2, 0) : 0;
      int dy = negative ? between(-2, 0) : 0;
      shapes.add(cells2d(3, 3, between(1, 5), dx, dy));
    }
    return shapes;
  }

  private GeostInstance poly2d(String name, boolean negative) {
    int ns = between(1, 4);
    List<List<Box>> shapes = polyShapes(ns, negative);
    int n = between(2, 3);
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int lo = negative ? between(-3, 0) : between(0, 2);
      objects.add(
          spatial(
              i,
              new int[][] {
                coordDomain(lo, 4), coordDomain(negative ? between(-3, 0) : between(0, 2), 4)
              },
              subset(ns, 3)));
    }
    List<NonOverlap> no = List.of(new NonOverlap(range(n), allDims(2)));
    return new GeostInstance(name, 2, shapes, objects, no, null);
  }

  private GeostInstance box3d(String name) {
    List<List<Box>> shapes = new ArrayList<>();
    int ns = between(1, 3);
    for (int s = 0; s < ns; s++) {
      int[] len = {between(1, 2), between(1, 2), between(1, 2)};
      List<Box> boxes = new ArrayList<>();
      boxes.add(box(new int[] {0, 0, 0}, len));
      if (random.nextInt(3) == 0) {
        // an L: a second box next to the first in some dimension
        int d = random.nextInt(3);
        int[] off = {0, 0, 0};
        off[d] = len[d];
        boxes.add(box(off, new int[] {1, 1, 1}));
      }
      shapes.add(boxes);
    }
    int n = between(2, 3);
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      objects.add(
          spatial(
              i,
              new int[][] {
                coordDomain(between(0, 1), 3),
                coordDomain(between(0, 1), 3),
                coordDomain(between(0, 1), 3)
              },
              subset(ns, 2)));
    }
    List<NonOverlap> no = List.of(new NonOverlap(range(n), allDims(3)));
    return new GeostInstance(name, 3, shapes, objects, no, null);
  }

  /** Time domains: start, duration (0 included sometimes, Geost forbids it) and end. */
  Obj timed(int no, int[][] coords, int[] shape) {
    int[] start = domain(0, between(0, 3), 4);
    int[] dur = domain(random.nextInt(4) == 0 ? 0 : 1, between(1, 3), 4);
    int[] end = domain(between(0, 2), between(2, 6), 4);
    return new Obj(no, coords, shape, start, dur, end);
  }

  private GeostInstance time(String name) {
    int k = between(1, 2);
    List<List<Box>> shapes =
        k == 1
            ? List.of(
                List.of(box(one(0), one(between(1, 2)))), List.of(box(one(0), one(between(1, 3)))))
            : rectangles(2, 2);
    int n = between(2, k == 1 ? 4 : 3);
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int[][] coords = new int[k][];
      for (int d = 0; d < k; d++) {
        coords[d] = coordDomain(between(0, 2), 3);
      }
      objects.add(timed(i, coords, subset(shapes.size(), 2)));
    }
    List<NonOverlap> no = List.of(new NonOverlap(range(n), allDims(k)));
    return new GeostInstance(name, k, shapes, objects, no, null);
  }

  private GeostInstance subdims(String name) {
    int k = between(1, 3);
    List<List<Box>> shapes = new ArrayList<>();
    int ns = between(1, 3);
    for (int s = 0; s < ns; s++) {
      int[] off = new int[k];
      int[] len = new int[k];
      for (int d = 0; d < k; d++) {
        len[d] = between(1, 2);
      }
      shapes.add(List.of(box(off, len)));
    }
    int n = between(2, k == 3 ? 3 : 4);
    boolean timed = random.nextBoolean();
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int[][] coords = new int[k][];
      for (int d = 0; d < k; d++) {
        coords[d] = coordDomain(between(0, 2), k == 3 ? 3 : 4);
      }
      objects.add(timed ? timed(i, coords, subset(ns, 2)) : spatial(i, coords, subset(ns, 2)));
    }
    // a random nonempty subset of 0..k, which may or may not contain time (k)
    int[] dims = subset(k + 1, k + 1);
    if (!timed && dims.length == 1 && dims[0] == k) {
      // with the common fixed time interval, time alone forbids any two objects
      dims = new int[] {random.nextInt(k), k};
      Arrays.sort(dims);
    }
    List<NonOverlap> no = List.of(new NonOverlap(range(n), dims));
    return new GeostInstance(name, k, shapes, objects, no, null);
  }

  private GeostInstance multi(String name) {
    int k = between(1, 2);
    List<List<Box>> shapes =
        k == 1
            ? List.of(List.of(box(one(0), one(1))), List.of(box(one(0), one(2))))
            : rectangles(2, 2);
    int n = between(3, k == 1 ? 5 : 4);
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int[][] coords = new int[k][];
      for (int d = 0; d < k; d++) {
        coords[d] = coordDomain(between(0, 2), 4);
      }
      objects.add(spatial(i, coords, subset(shapes.size(), 2)));
    }
    List<NonOverlap> no = new ArrayList<>();
    int nc = between(1, 3);
    for (int c = 0; c < nc; c++) {
      int[] scope = subset(n, n);
      if (scope.length < 2) {
        scope = new int[] {0, n - 1};
      }
      no.add(new NonOverlap(scope, random.nextBoolean() ? allDims(k) : range(k)));
    }
    return new GeostInstance(name, k, shapes, objects, no, null);
  }

  private GeostInstance fixed(String name) {
    GeostInstance base =
        random.nextBoolean() ? rect2d(name, random.nextBoolean(), false) : poly2d(name, false);
    List<Obj> objects = new ArrayList<>();
    for (Obj o : base.objects) {
      int[][] coords = o.coords().clone();
      int[] shape = o.shape();
      int r = random.nextInt(3);
      if (r == 0) {
        // fully fixed
        for (int d = 0; d < coords.length; d++) {
          coords[d] = one(coords[d][random.nextInt(coords[d].length)]);
        }
        shape = one(shape[random.nextInt(shape.length)]);
      } else if (r == 1) {
        coords[0] = one(coords[0][random.nextInt(coords[0].length)]);
      }
      objects.add(new Obj(o.no(), coords, shape, o.start(), o.dur(), o.end()));
    }
    return new GeostInstance(name, base.k, base.shapes, objects, base.nonOverlaps, base.area);
  }

  private GeostInstance tiling(String name) {
    int w = between(3, 5);
    int h = between(2, 4);
    int ns = between(2, 4);
    List<List<Box>> shapes = new ArrayList<>();
    for (int s = 0; s < ns; s++) {
      shapes.add(cells2d(between(1, 3), between(1, 3), between(2, 4), 0, 0));
    }
    int n = between(2, 4);
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      objects.add(
          spatial(i, new int[][] {domain(0, w - 1, 0), domain(0, h - 1, 0)}, subset(ns, 3)));
    }
    Area a = new Area(box(new int[] {0, 0}, new int[] {w, h}), List.of());
    List<NonOverlap> no = List.of(new NonOverlap(range(n), allDims(2)));
    return new GeostInstance(name, 2, shapes, objects, no, a);
  }

  private GeostInstance mixed(String name) {
    GeostInstance base =
        switch (random.nextInt(5)) {
          case 0 -> seg1d(name, true);
          case 1 -> rect2d(name, random.nextBoolean(), random.nextBoolean());
          case 2 -> poly2d(name, random.nextBoolean());
          case 3 -> time(name);
          default -> multi(name);
        };
    // renumber objects with gaps and in a random order
    List<Integer> ids = new ArrayList<>();
    TreeSet<Integer> used = new TreeSet<>();
    while (used.size() < base.objects.size()) {
      used.add(random.nextInt(3 * base.objects.size() + 2));
    }
    ids.addAll(used);
    Collections.shuffle(ids, random);
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < base.objects.size(); i++) {
      Obj o = base.objects.get(i);
      objects.add(new Obj(ids.get(i), o.coords(), o.shape(), o.start(), o.dur(), o.end()));
    }
    List<NonOverlap> no = new ArrayList<>();
    for (NonOverlap c : base.nonOverlaps) {
      no.add(new NonOverlap(Arrays.stream(c.objects()).map(ids::get).toArray(), c.dims()));
    }
    return new GeostInstance(name, base.k, base.shapes, objects, no, base.area);
  }

  // ---------------------------------------------------------------------------------------------

  /** Writes perFamily instances of every family, with brute-force solution counts. */
  public static void main(String[] args) throws IOException {
    Path out = Path.of(args[0]);
    int perFamily = Integer.parseInt(args[1]);
    long maxSolutions = args.length > 2 ? Long.parseLong(args[2]) : 3000;
    StringBuilder b = new StringBuilder();
    b.append("# Small Geost instances with their number of solutions, from brute force.\n");
    b.append("# Generated by org.jacop.geost.GeostInstanceGenerator; format in GeostInstance.\n");
    for (Family f : Family.values()) {
      GeostInstanceGenerator gen = new GeostInstanceGenerator(f.ordinal() * 1_000_003L + 7);
      int written = 0;
      int index = 0;
      while (written < perFamily) {
        GeostInstance g = gen.generate(f, f.name().toLowerCase() + "-" + index++);
        GeostInstance.Solutions s = g.bruteForce(false, maxSolutions);
        if (s == null) {
          continue;
        }
        g.expectedCount = s.count;
        g.expectedHash = s.hash();
        b.append(g.format());
        written++;
      }
    }
    Files.createDirectories(out.toAbsolutePath().getParent());
    Files.writeString(out, b.toString(), StandardCharsets.UTF_8);
  }
}
