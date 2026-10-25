/*
 * GeostBenchmark.java
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
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiFunction;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.geost.GeostInstance.Area;
import org.jacop.geost.GeostInstance.Box;
import org.jacop.geost.GeostInstance.NonOverlap;
import org.jacop.geost.GeostInstance.Obj;
import org.jacop.geost.GeostInstance.Posted;
import org.jacop.geost.GeostInstance.Rect;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;

/**
 * Performance benchmarks for Geost, with the same instances posted as Diffn, Diff2 and a pairwise
 * decomposition where they apply.
 *
 * <p>Every benchmark is a satisfaction problem solved with a fixed search (objects in order; per
 * object its shape, its coordinates, its start and its duration; smallest value first), for the
 * first solution or for all of them. Each run reports nodes, failures, solutions and time as one
 * JSON line, and checks every solution it finds against the instance. Known solution counts (for
 * example 8 tilings of a 3 x 20 rectangle by the 12 pentominoes, counting reflections and
 * rotations) are checked too, and so is agreement between the models.
 *
 * <pre>
 * java -cp jacop-core/target/classes:jacop-core/target/test-classes:... \
 *     org.jacop.geost.GeostBenchmark [--filter regex] [--models geost,diffn] [--limit seconds]
 *     [--repeat n] [--out results.jsonl] [--label name] [--list]
 * </pre>
 *
 * <p>{@code scripts/geost-benchmarks.py} runs it on two builds and compares them.
 */
public final class GeostBenchmark {

  /** A benchmark: an instance, whether all solutions are wanted, and the known count if any. */
  public record Bench(String name, GeostInstance instance, boolean all, long expected) {}

  // ---------------------------------------------------------------------------------------------
  // polyominoes

  static final Map<String, int[][]> PENTOMINOES = new LinkedHashMap<>();

  static final Map<String, int[][]> TETROMINOES = new LinkedHashMap<>();

  static {
    PENTOMINOES.put("F", new int[][] {{1, 0}, {2, 0}, {0, 1}, {1, 1}, {1, 2}});
    PENTOMINOES.put("I", new int[][] {{0, 0}, {0, 1}, {0, 2}, {0, 3}, {0, 4}});
    PENTOMINOES.put("L", new int[][] {{0, 0}, {0, 1}, {0, 2}, {0, 3}, {1, 3}});
    PENTOMINOES.put("N", new int[][] {{1, 0}, {1, 1}, {0, 2}, {1, 2}, {0, 3}});
    PENTOMINOES.put("P", new int[][] {{0, 0}, {1, 0}, {0, 1}, {1, 1}, {0, 2}});
    PENTOMINOES.put("T", new int[][] {{0, 0}, {1, 0}, {2, 0}, {1, 1}, {1, 2}});
    PENTOMINOES.put("U", new int[][] {{0, 0}, {2, 0}, {0, 1}, {1, 1}, {2, 1}});
    PENTOMINOES.put("V", new int[][] {{0, 0}, {0, 1}, {0, 2}, {1, 2}, {2, 2}});
    PENTOMINOES.put("W", new int[][] {{0, 0}, {0, 1}, {1, 1}, {1, 2}, {2, 2}});
    PENTOMINOES.put("X", new int[][] {{1, 0}, {0, 1}, {1, 1}, {2, 1}, {1, 2}});
    PENTOMINOES.put("Y", new int[][] {{1, 0}, {0, 1}, {1, 1}, {1, 2}, {1, 3}});
    PENTOMINOES.put("Z", new int[][] {{0, 0}, {1, 0}, {1, 1}, {1, 2}, {2, 2}});
    TETROMINOES.put("I", new int[][] {{0, 0}, {0, 1}, {0, 2}, {0, 3}});
    TETROMINOES.put("O", new int[][] {{0, 0}, {1, 0}, {0, 1}, {1, 1}});
    TETROMINOES.put("T", new int[][] {{0, 0}, {1, 0}, {2, 0}, {1, 1}});
    TETROMINOES.put("L", new int[][] {{0, 0}, {0, 1}, {0, 2}, {1, 2}});
    TETROMINOES.put("S", new int[][] {{1, 0}, {2, 0}, {0, 1}, {1, 1}});
  }

  /** The distinct orientations (rotations and reflections) of a set of cells, normalised. */
  static List<Set<List<Integer>>> orientations(int[][] cells) {
    List<Set<List<Integer>>> result = new ArrayList<>();
    for (int flip = 0; flip < 2; flip++) {
      int[][] c = new int[cells.length][];
      for (int i = 0; i < cells.length; i++) {
        c[i] = new int[] {flip == 1 ? -cells[i][0] : cells[i][0], cells[i][1]};
      }
      for (int r = 0; r < 4; r++) {
        for (int[] p : c) {
          int x = p[0];
          p[0] = -p[1];
          p[1] = x;
        }
        int minX = Arrays.stream(c).mapToInt(p -> p[0]).min().orElseThrow();
        int minY = Arrays.stream(c).mapToInt(p -> p[1]).min().orElseThrow();
        Set<List<Integer>> norm =
            new TreeSet<>(
                Comparator.<List<Integer>>comparingInt(l -> l.get(1))
                    .thenComparingInt(l -> l.get(0)));
        for (int[] p : c) {
          norm.add(List.of(p[0] - minX, p[1] - minY));
        }
        if (!result.contains(norm)) {
          result.add(norm);
        }
      }
    }
    return result;
  }

  /** Boxes of a set of cells: one box per horizontal run. */
  static List<Box> runs(Set<List<Integer>> cells) {
    List<Box> boxes = new ArrayList<>();
    for (List<Integer> c : cells) {
      if (cells.contains(List.of(c.get(0) - 1, c.get(1)))) {
        continue;
      }
      int w = 1;
      while (cells.contains(List.of(c.get(0) + w, c.get(1)))) {
        w++;
      }
      boxes.add(new Box(new int[] {c.get(0), c.get(1)}, new int[] {w, 1}));
    }
    return boxes;
  }

  /**
   * Polyominoes placed in a w x h board, one object per piece choosing among the orientations of
   * the piece, with optional holes in the board.
   */
  static GeostInstance polyominoes(
      String name, Map<String, int[][]> set, String pieces, int w, int h, List<Box> holes) {
    List<List<Box>> shapes = new ArrayList<>();
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < pieces.length(); i++) {
      int[][] cells = set.get(String.valueOf(pieces.charAt(i)));
      List<Integer> kinds = new ArrayList<>();
      for (Set<List<Integer>> o : orientations(cells)) {
        kinds.add(shapes.size());
        shapes.add(runs(o));
      }
      objects.add(
          GeostInstanceGenerator.spatial(
              i,
              new int[][] {range(0, w - 1), range(0, h - 1)},
              kinds.stream().mapToInt(Integer::intValue).toArray()));
    }
    Area area = new Area(new Box(new int[] {0, 0}, new int[] {w, h}), holes);
    return new GeostInstance(
        name,
        2,
        shapes,
        objects,
        List.of(new NonOverlap(range(0, pieces.length() - 1), new int[] {0, 1, 2})),
        area);
  }

  static int[] range(int lo, int hi) {
    int[] r = new int[hi - lo + 1];
    for (int i = 0; i < r.length; i++) {
      r[i] = lo + i;
    }
    return r;
  }

  // ---------------------------------------------------------------------------------------------
  // rectangles and boxes

  /** Squares of sides n, n-1, ..., 1 in a w x h rectangle (Korf's consecutive squares). */
  static GeostInstance squares(int n, int w, int h) {
    List<List<Box>> shapes = new ArrayList<>();
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int side = n - i;
      shapes.add(List.of(new Box(new int[] {0, 0}, new int[] {side, side})));
      objects.add(
          GeostInstanceGenerator.spatial(
              i, new int[][] {range(0, w - side), range(0, h - side)}, new int[] {i}));
    }
    Area area = new Area(new Box(new int[] {0, 0}, new int[] {w, h}), List.of());
    return new GeostInstance(
        "squares" + n + "-" + w + "x" + h,
        2,
        shapes,
        objects,
        List.of(new NonOverlap(range(0, n - 1), new int[] {0, 1, 2})),
        area);
  }

  /**
   * Random rectangles that may be rotated (two shapes each), in a square area that they fill to
   * about the given percentage.
   */
  static GeostInstance rotations(String name, long seed, int n, int maxSide, int fillPercent) {
    Random r = new Random(seed);
    List<List<Box>> shapes = new ArrayList<>();
    int[][] sides = new int[n][2];
    int total = 0;
    for (int i = 0; i < n; i++) {
      sides[i][0] = 1 + r.nextInt(maxSide);
      sides[i][1] = 1 + r.nextInt(maxSide);
      total += sides[i][0] * sides[i][1];
    }
    // a square area that the rectangles fill to about fillPercent
    int side = (int) Math.ceil(Math.sqrt(total * 100.0 / fillPercent));
    for (int[] s : sides) {
      side = Math.max(side, Math.max(s[0], s[1]));
    }
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int a = sides[i][0];
      int c = sides[i][1];
      int[] kinds;
      shapes.add(List.of(new Box(new int[] {0, 0}, new int[] {a, c})));
      if (a != c) {
        shapes.add(List.of(new Box(new int[] {0, 0}, new int[] {c, a})));
        kinds = new int[] {shapes.size() - 2, shapes.size() - 1};
      } else {
        kinds = new int[] {shapes.size() - 1};
      }
      objects.add(
          GeostInstanceGenerator.spatial(
              i, new int[][] {range(0, side - 1), range(0, side - 1)}, kinds));
    }
    Area area = new Area(new Box(new int[] {0, 0}, new int[] {side, side}), List.of());
    return new GeostInstance(
        name,
        2,
        shapes,
        objects,
        List.of(new NonOverlap(range(0, n - 1), new int[] {0, 1, 2})),
        area);
  }

  /** 3-D boxes of the given sizes in a c0 x c1 x height container. */
  static GeostInstance boxes3d(String name, int[][] sizes, int c0, int c1, int height) {
    List<List<Box>> shapes = new ArrayList<>();
    List<Obj> objects = new ArrayList<>();
    int[] cap = {c0, c1, height};
    for (int i = 0; i < sizes.length; i++) {
      shapes.add(List.of(new Box(new int[] {0, 0, 0}, sizes[i].clone())));
      int[][] coords = new int[3][];
      for (int d = 0; d < 3; d++) {
        coords[d] = range(0, cap[d] - sizes[i][d]);
      }
      objects.add(GeostInstanceGenerator.spatial(i, coords, new int[] {i}));
    }
    return new GeostInstance(
        name,
        3,
        shapes,
        objects,
        List.of(new NonOverlap(range(0, sizes.length - 1), new int[] {0, 1, 2, 3})),
        null);
  }

  /**
   * Jobs that each need w contiguous machines of a line of m machines for a duration d or d + 1,
   * all within the horizon. With time = true the time is Geost's time dimension (start, duration
   * and end variables); otherwise it is a second coordinate and the two durations are two shapes,
   * which is the same problem posted without the time dimension.
   */
  static GeostInstance jobs(String name, long seed, int n, int m, int horizon, boolean time) {
    Random r = new Random(seed);
    List<List<Box>> shapes = new ArrayList<>();
    List<Obj> objects = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int w = 1 + r.nextInt(Math.min(3, m));
      int d = 1 + r.nextInt(3);
      boolean flexible = r.nextBoolean();
      int[] durs = flexible ? new int[] {d, d + 1} : new int[] {d};
      if (time) {
        shapes.add(List.of(new Box(new int[] {0}, new int[] {w})));
        objects.add(
            new Obj(
                i,
                new int[][] {range(0, m - w)},
                new int[] {shapes.size() - 1},
                range(0, horizon - d),
                durs,
                range(d, horizon)));
      } else {
        int[] kinds = new int[durs.length];
        for (int j = 0; j < durs.length; j++) {
          shapes.add(List.of(new Box(new int[] {0, 0}, new int[] {w, durs[j]})));
          kinds[j] = shapes.size() - 1;
        }
        objects.add(
            GeostInstanceGenerator.spatial(
                i, new int[][] {range(0, m - w), range(0, horizon - d)}, kinds));
      }
    }
    Area area =
        time ? null : new Area(new Box(new int[] {0, 0}, new int[] {m, horizon}), List.of());
    int[] dims = time ? new int[] {0, 1} : new int[] {0, 1, 2};
    return new GeostInstance(
        name, time ? 1 : 2, shapes, objects, List.of(new NonOverlap(range(0, n - 1), dims)), area);
  }

  // ---------------------------------------------------------------------------------------------

  /**
   * The benchmark set. Names ending in "-all" enumerate all solutions; the others look for the
   * first one. The "stress" ones are not expected to finish within a minute and measure how many
   * nodes a model explores in the time limit.
   */
  public static List<Bench> benchmarks() {
    List<Bench> b = new ArrayList<>();
    String all12 = "FILNPTUVWXYZ";
    // polyomino tilings; the 5 free tetrominoes cannot tile a rectangle (checkerboard argument)
    b.add(
        new Bench(
            "tetro-4x5-all", polyominoes("t", TETROMINOES, "IOTLS", 5, 4, List.of()), true, 0));
    b.add(
        new Bench(
            "tetro-2x10-all", polyominoes("t", TETROMINOES, "IOTLS", 10, 2, List.of()), true, 0));
    b.add(
        new Bench(
            "pent-5x5-all", polyominoes("p", PENTOMINOES, "ILPNU", 5, 5, List.of()), true, -1));
    b.add(
        new Bench(
            "pent-5x6-all", polyominoes("p", PENTOMINOES, "FILPNU", 6, 5, List.of()), true, -1));
    b.add(
        new Bench(
            "pent-3x10-all", polyominoes("p", PENTOMINOES, "ILPUVY", 10, 3, List.of()), true, -1));
    b.add(
        new Bench(
            "pent-5x8", polyominoes("p", PENTOMINOES, "FILNPTUV", 8, 5, List.of()), false, -1));
    b.add(
        new Bench(
            "pent-4x10", polyominoes("p", PENTOMINOES, "FILNPTUVWY", 10, 4, List.of()), false, -1));
    b.add(
        new Bench(
            "stress-pent-3x20", polyominoes("p", PENTOMINOES, all12, 20, 3, List.of()), false, -1));
    b.add(
        new Bench(
            "stress-pent-6x10", polyominoes("p", PENTOMINOES, all12, 10, 6, List.of()), false, -1));
    // Dana Scott's 8 x 8 board without its central 2 x 2 square
    List<Box> centre = List.of(new Box(new int[] {3, 3}, new int[] {2, 2}));
    b.add(
        new Bench(
            "stress-pent-8x8-hole", polyominoes("p", PENTOMINOES, all12, 8, 8, centre), false, -1));
    // consecutive squares in their smallest enclosing rectangles (Huang and Korf 2013)
    int[][] korf = {
      {8, 14, 15}, {9, 15, 20}, {10, 15, 27}, {11, 19, 27}, {12, 23, 29}, {13, 22, 38}
    };
    for (int[] k : korf) {
      b.add(new Bench("squares" + k[0], squares(k[0], k[1], k[2]), false, -1));
    }
    // rectangles that may be rotated: all solutions of small tight instances, first of larger
    b.add(new Bench("rot5-all", rotations("r", 11, 5, 3, 90), true, -1));
    b.add(new Bench("rot6-all", rotations("r", 12, 6, 3, 90), true, -1));
    b.add(new Bench("rot7-all", rotations("r", 13, 7, 3, 95), true, -1));
    b.add(new Bench("rot16", rotations("r", 15, 16, 4, 95), false, -1));
    b.add(new Bench("rot20", rotations("r", 16, 20, 5, 99), false, -1));
    // 3-D boxes (box3_12 of the earlier Geost audit) at the optimal height and one below
    int[][] box12 = {
      {3, 2, 3}, {3, 3, 1}, {3, 1, 3}, {3, 1, 3}, {2, 2, 2}, {3, 1, 2},
      {1, 1, 1}, {3, 1, 1}, {1, 1, 3}, {1, 3, 3}, {2, 1, 3}, {2, 3, 3}
    };
    b.add(new Bench("box3-12-h5", boxes3d("b", box12, 5, 5, 5), false, -1));
    b.add(new Bench("box3-12-h4", boxes3d("b", box12, 5, 5, 4), false, 0));
    // jobs on a line of machines, through the time dimension and as plain 2-D packing
    for (boolean time : new boolean[] {true, false}) {
      String t = time ? "time" : "space";
      b.add(new Bench("jobs6-" + t + "-all", jobs("j", 5, 6, 4, 6, time), true, -1));
      b.add(new Bench("jobs12-" + t, jobs("j", 6, 12, 5, 8, time), false, -1));
      b.add(new Bench("jobs16-" + t, jobs("j", 7, 16, 6, 9, time), false, -1));
    }
    return b;
  }

  /** The models a benchmark can be posted as. */
  static Map<String, BiFunction<GeostInstance, Store, Posted>> models(GeostInstance g) {
    Map<String, BiFunction<GeostInstance, Store, Posted>> m = new LinkedHashMap<>();
    m.put("geost", (i, s) -> i.postGeost(s, false));
    if (g.diffnExpressible()) {
      m.put(
          "diffn",
          (i, s) ->
              i.postRectangles(s, g.sameBoxCounts() ? Rect.DIFFN_STRICT : Rect.DIFFN_NONSTRICT));
      m.put("diff2", (i, s) -> i.postRectangles(s, Rect.DIFF2));
    }
    m.put("decomposition", (i, s) -> i.postDecomposition(s));
    return m;
  }

  /** The outcome of one run. */
  record Run(
      String bench,
      String model,
      String status,
      long solutions,
      long nodes,
      long fails,
      long millis,
      boolean ok,
      String note) {

    String json(String label) {
      return String.format(
          "{\"label\":\"%s\",\"bench\":\"%s\",\"model\":\"%s\",\"status\":\"%s\",\"solutions\":%d,"
              + "\"nodes\":%d,\"fails\":%d,\"ms\":%d,\"ok\":%s,\"note\":\"%s\"}",
          label, bench, model, status, solutions, nodes, fails, millis, ok, note);
    }
  }

  static Run run(
      Bench bench, String model, BiFunction<GeostInstance, Store, Posted> post, int limit) {
    GeostInstance g = bench.instance();
    long t0 = System.nanoTime();
    Store store = new Store();
    Posted p = post.apply(g, store);
    IntVar[] solution = p.vars();
    // per object: shape, coordinates, start, duration (the end follows)
    int w = g.varsPerObject();
    List<IntVar> order = new ArrayList<>();
    for (int i = 0; i < g.objects.size(); i++) {
      order.add(solution[i * w + g.k]);
      for (int d = 0; d < g.k; d++) {
        order.add(solution[i * w + d]);
      }
      order.add(solution[i * w + g.k + 1]);
      order.add(solution[i * w + g.k + 2]);
    }
    long[] wrong = {0};
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setTimeOut(limit);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            if (!g.check(Arrays.stream(solution).mapToInt(IntVar::value).toArray())) {
              wrong[0]++;
            }
            return result;
          }
        });
    search.getSolutionListener().searchAll(bench.all());
    search.getSolutionListener().recordSolutions(false);
    boolean found =
        store.consistency()
            && search.labeling(
                store, new SimpleSelect<>(order.toArray(new IntVar[0]), null, new IndomainMin<>()));
    long millis = (System.nanoTime() - t0) / 1_000_000;
    long solutions = search.getSolutionListener().solutionsNo();
    String status;
    if (search.timeOutOccured) {
      status = "LIMIT";
    } else if (bench.all()) {
      status = "ALL";
    } else {
      status = found ? "SAT" : "UNSAT";
    }
    boolean ok = wrong[0] == 0;
    String note = wrong[0] == 0 ? "" : wrong[0] + " wrong solutions";
    if (bench.expected() >= 0 && !status.equals("LIMIT")) {
      long expected = bench.expected();
      boolean match = bench.all() ? solutions == expected : (solutions > 0) == (expected > 0);
      if (!match) {
        ok = false;
        note += " expected " + expected;
      }
    }
    return new Run(
        bench.name(),
        model,
        status,
        solutions,
        search.getNodes(),
        search.getWrongDecisions(),
        millis,
        ok,
        note.trim());
  }

  public static void main(String[] args) throws IOException {
    String filter = ".*";
    List<String> wantedModels = null;
    int limit = 60;
    int repeat = 1;
    String label = "jacop";
    Path out = null;
    boolean list = false;
    for (int i = 0; i < args.length; i++) {
      switch (args[i]) {
        case "--filter" -> filter = args[++i];
        case "--models" -> wantedModels = Arrays.asList(args[++i].split(","));
        case "--limit" -> limit = Integer.parseInt(args[++i]);
        case "--repeat" -> repeat = Integer.parseInt(args[++i]);
        case "--label" -> label = args[++i];
        case "--out" -> out = Path.of(args[++i]);
        case "--list" -> list = true;
        default -> throw new IllegalArgumentException("unknown argument " + args[i]);
      }
    }
    PrintStream file = out == null ? null : new PrintStream(Files.newOutputStream(out), true);
    // warm the JIT on a small benchmark
    for (Bench b : benchmarks()) {
      if (b.name().equals("pent-5x5-all")) {
        for (var m : models(b.instance()).entrySet()) {
          run(b, m.getKey(), m.getValue(), 10);
        }
      }
    }
    int failures = 0;
    for (Bench b : benchmarks()) {
      if (!b.name().matches(filter)) {
        continue;
      }
      if (list) {
        System.out.println(b.name() + " " + models(b.instance()).keySet());
        continue;
      }
      Map<String, Long> counts = new LinkedHashMap<>();
      for (var m : models(b.instance()).entrySet()) {
        if (wantedModels != null && !wantedModels.contains(m.getKey())) {
          continue;
        }
        Run best = null;
        for (int r = 0; r < repeat; r++) {
          Run run = run(b, m.getKey(), m.getValue(), limit);
          if (best == null || run.millis() < best.millis()) {
            best = run;
          }
        }
        if (!best.status().equals("LIMIT")) {
          counts.put(
              m.getKey(),
              best.status().equals("ALL") ? best.solutions() : best.solutions() > 0 ? 1L : 0L);
        }
        if (!best.ok()) {
          failures++;
        }
        String line = best.json(label);
        System.out.println(line);
        if (file != null) {
          file.println(line);
        }
      }
      if (counts.values().stream().distinct().count() > 1) {
        failures++;
        System.out.println("# models disagree on " + b.name() + ": " + counts);
      }
    }
    if (file != null) {
      file.close();
    }
    if (failures > 0) {
      System.out.println("# " + failures + " failed checks");
      System.exit(1);
    }
  }
}
