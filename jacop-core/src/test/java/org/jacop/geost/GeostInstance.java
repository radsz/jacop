/*
 * GeostInstance.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import org.jacop.constraints.And;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Diff2;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.diffn.Nooverlap;
import org.jacop.constraints.geost.Dbox;
import org.jacop.constraints.geost.ExternalConstraint;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.InArea;
import org.jacop.constraints.geost.LexChain;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.Shape;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * A small Geost instance that can be written to and read from text, enumerated by brute force, and
 * posted as Geost, as a pairwise decomposition into primitive constraints, or (when it is a plain
 * packing in one or two dimensions) as Diffn, Nooverlap and Diff2 over the boxes of the shapes.
 *
 * <p>The meaning is that of the Geost constraint with its time dimension: every object has k
 * coordinates, a shape, and a time interval [start, end) with start + duration = end and duration
 * at least 1. A {@link NonOverlap} over a set of objects and a set of dimensions (k is the time
 * dimension) requires every two boxes of two different objects to be apart in at least one of those
 * dimensions; in the dimensions that are not selected, objects are treated as unbounded. An {@link
 * Area} keeps every box inside a box and out of its holes. The boxes of one shape do not overlap
 * each other.
 *
 * <p>The text format has one line per item, between {@code instance <name>} and {@code end}:
 *
 * <pre>
 * instance rect2d-17
 * dims 2
 * shape 0 0,0/2,1 1,0/1,2        (one shape: boxes as offset/length)
 * object 0 x 0..3,5;1..2 s 0,1 t 0 d 1 e 1
 * nonoverlap 0,1,2 dims 0,1,2
 * area 0,0/5,4 holes 1,1/1,1
 * expect 1234 9f3a...            (solution count and an order-independent hash)
 * end
 * </pre>
 */
public final class GeostInstance {

  /** A box of a shape, as offset and length per dimension. */
  public record Box(int[] offset, int[] length) {

    String format() {
      return join(offset) + "/" + join(length);
    }
  }

  /** A non-overlapping external constraint. */
  public record NonOverlap(int[] objects, int[] dims) {}

  /** An allowed area with forbidden holes. */
  public record Area(Box box, List<Box> holes) {}

  /** One object: domains of its variables. */
  public record Obj(int no, int[][] coords, int[] shape, int[] start, int[] dur, int[] end) {}

  public final String name;
  public final int k;
  public final List<List<Box>> shapes;
  public final List<Obj> objects;
  public final List<NonOverlap> nonOverlaps;
  public final Area area;

  /** Expected solution count, or -1 when unknown. */
  public long expectedCount = -1;

  /** Expected solution hash, or null when unknown. */
  public String expectedHash;

  public GeostInstance(
      String name,
      int k,
      List<List<Box>> shapes,
      List<Obj> objects,
      List<NonOverlap> nonOverlaps,
      Area area) {
    this.name = name;
    this.k = k;
    this.shapes = shapes;
    this.objects = objects;
    this.nonOverlaps = nonOverlaps;
    this.area = area;
  }

  /** Number of variables of one object in the solution vector: coordinates, shape, s, d, e. */
  public int varsPerObject() {
    return k + 4;
  }

  // ---------------------------------------------------------------------------------------------
  // Text format

  public String format() {
    StringBuilder b = new StringBuilder();
    b.append("instance ").append(name).append('\n');
    b.append("dims ").append(k).append('\n');
    for (int s = 0; s < shapes.size(); s++) {
      b.append("shape ").append(s);
      for (Box box : shapes.get(s)) {
        b.append(' ').append(box.format());
      }
      b.append('\n');
    }
    for (Obj o : objects) {
      b.append("object ").append(o.no()).append(" x ");
      for (int d = 0; d < k; d++) {
        b.append(d == 0 ? "" : ";").append(formatDomain(o.coords()[d]));
      }
      b.append(" s ").append(formatDomain(o.shape()));
      b.append(" t ").append(formatDomain(o.start()));
      b.append(" d ").append(formatDomain(o.dur()));
      b.append(" e ").append(formatDomain(o.end()));
      b.append('\n');
    }
    for (NonOverlap no : nonOverlaps) {
      b.append("nonoverlap ").append(join(no.objects())).append(" dims ").append(join(no.dims()));
      b.append('\n');
    }
    if (area != null) {
      b.append("area ").append(area.box().format());
      if (!area.holes().isEmpty()) {
        b.append(" holes");
        for (Box h : area.holes()) {
          b.append(' ').append(h.format());
        }
      }
      b.append('\n');
    }
    if (expectedCount >= 0) {
      b.append("expect ").append(expectedCount).append(' ').append(expectedHash).append('\n');
    }
    b.append("end\n");
    return b.toString();
  }

  /** Parses all instances of a corpus text; lines starting with # are comments. */
  public static List<GeostInstance> parseAll(String text) {
    List<GeostInstance> result = new ArrayList<>();
    String name = null;
    int k = 0;
    List<List<Box>> shapes = null;
    List<Obj> objects = null;
    List<NonOverlap> nonOverlaps = null;
    Area area = null;
    long count = -1;
    String hash = null;
    for (String raw : text.split("\n")) {
      String line = raw.trim();
      if (line.isEmpty() || line.startsWith("#")) {
        continue;
      }
      String[] t = line.split("\\s+");
      switch (t[0]) {
        case "instance" -> {
          name = t[1];
          shapes = new ArrayList<>();
          objects = new ArrayList<>();
          nonOverlaps = new ArrayList<>();
          area = null;
          count = -1;
          hash = null;
        }
        case "dims" -> k = Integer.parseInt(t[1]);
        case "shape" -> {
          List<Box> boxes = new ArrayList<>();
          for (int i = 2; i < t.length; i++) {
            boxes.add(parseBox(t[i]));
          }
          shapes.add(boxes);
        }
        case "object" -> {
          int no = Integer.parseInt(t[1]);
          int[][] coords = new int[k][];
          String[] cs = t[3].split(";");
          for (int d = 0; d < k; d++) {
            coords[d] = parseDomain(cs[d]);
          }
          objects.add(
              new Obj(
                  no,
                  coords,
                  parseDomain(t[5]),
                  parseDomain(t[7]),
                  parseDomain(t[9]),
                  parseDomain(t[11])));
        }
        case "nonoverlap" -> nonOverlaps.add(new NonOverlap(parseInts(t[1]), parseInts(t[3])));
        case "area" -> {
          List<Box> holes = new ArrayList<>();
          for (int i = 3; i < t.length; i++) {
            holes.add(parseBox(t[i]));
          }
          area = new Area(parseBox(t[1]), holes);
        }
        case "expect" -> {
          count = Long.parseLong(t[1]);
          hash = t[2];
        }
        case "end" -> {
          GeostInstance g = new GeostInstance(name, k, shapes, objects, nonOverlaps, area);
          g.expectedCount = count;
          g.expectedHash = hash;
          result.add(g);
        }
        default -> throw new IllegalArgumentException("unknown line: " + line);
      }
    }
    return result;
  }

  static String join(int[] a) {
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < a.length; i++) {
      b.append(i == 0 ? "" : ",").append(a[i]);
    }
    return b.toString();
  }

  static int[] parseInts(String s) {
    return Arrays.stream(s.split(",")).mapToInt(Integer::parseInt).toArray();
  }

  static Box parseBox(String s) {
    String[] p = s.split("/");
    return new Box(parseInts(p[0]), parseInts(p[1]));
  }

  /** Formats sorted distinct values as ranges, for example 0..3,5. */
  static String formatDomain(int[] values) {
    StringBuilder b = new StringBuilder();
    int i = 0;
    while (i < values.length) {
      int j = i;
      while (j + 1 < values.length && values[j + 1] == values[j] + 1) {
        j++;
      }
      b.append(b.isEmpty() ? "" : ",").append(values[i]);
      if (j > i) {
        b.append("..").append(values[j]);
      }
      i = j + 1;
    }
    return b.toString();
  }

  static int[] parseDomain(String s) {
    TreeSet<Integer> values = new TreeSet<>();
    for (String part : s.split(",")) {
      int r = part.indexOf("..", 1);
      if (r < 0) {
        values.add(Integer.parseInt(part));
      } else {
        int lo = Integer.parseInt(part.substring(0, r));
        int hi = Integer.parseInt(part.substring(r + 2));
        for (int v = lo; v <= hi; v++) {
          values.add(v);
        }
      }
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  // ---------------------------------------------------------------------------------------------
  // Semantics and brute force

  /** A placement of one object. */
  record Placement(int[] x, int s, int start, int dur, int end) {}

  /** True when two boxes of placed objects overlap in every selected dimension. */
  boolean overlap(Placement a, Box ba, Placement b, Box bb, int[] dims) {
    for (int d : dims) {
      if (d == k) {
        if (a.end() <= b.start() || b.end() <= a.start()) {
          return false;
        }
      } else {
        int sa = a.x()[d] + ba.offset()[d];
        int sb = b.x()[d] + bb.offset()[d];
        if (sa + ba.length()[d] <= sb || sb + bb.length()[d] <= sa) {
          return false;
        }
      }
    }
    return true;
  }

  boolean conflict(Placement a, Placement b, int[] dims) {
    for (Box ba : shapes.get(a.s())) {
      for (Box bb : shapes.get(b.s())) {
        if (overlap(a, ba, b, bb, dims)) {
          return true;
        }
      }
    }
    return false;
  }

  boolean inArea(Placement p) {
    if (area == null) {
      return true;
    }
    for (Box b : shapes.get(p.s())) {
      for (int d = 0; d < k; d++) {
        int s = p.x()[d] + b.offset()[d];
        if (s < area.box().offset()[d]
            || s + b.length()[d] > area.box().offset()[d] + area.box().length()[d]) {
          return false;
        }
      }
      for (Box h : area.holes()) {
        boolean all = true;
        for (int d = 0; d < k && all; d++) {
          int s = p.x()[d] + b.offset()[d];
          all = s < h.offset()[d] + h.length()[d] && h.offset()[d] < s + b.length()[d];
        }
        if (all) {
          return false;
        }
      }
    }
    return true;
  }

  /** All placements of an object that satisfy its own constraints (time and area). */
  List<Placement> placements(Obj o) {
    List<Placement> result = new ArrayList<>();
    int[] x = new int[k];
    placements(o, 0, x, result);
    return result;
  }

  private void placements(Obj o, int d, int[] x, List<Placement> result) {
    if (d < k) {
      for (int v : o.coords()[d]) {
        x[d] = v;
        placements(o, d + 1, x, result);
      }
      return;
    }
    Set<Integer> ends = new HashSet<>();
    for (int e : o.end()) {
      ends.add(e);
    }
    for (int s : o.shape()) {
      for (int st : o.start()) {
        for (int du : o.dur()) {
          if (du >= 1 && ends.contains(st + du)) {
            Placement p = new Placement(x.clone(), s, st, du, st + du);
            if (inArea(p)) {
              result.add(p);
            }
          }
        }
      }
    }
  }

  /** The result of an enumeration: count, hash and (optionally) all solutions. */
  public static final class Solutions {
    public long count;
    long hash;
    public final Set<List<Integer>> all;

    Solutions(boolean keep) {
      all = keep ? new HashSet<>() : null;
    }

    public void add(int[] solution) {
      count++;
      hash += mix(Arrays.hashCode(solution));
      if (all != null) {
        all.add(Arrays.stream(solution).boxed().toList());
      }
    }

    public String hash() {
      return String.format("%016x", hash);
    }
  }

  static long mix(long z) {
    z = (z ^ (z >>> 33)) * 0xff51afd7ed558ccdL;
    z = (z ^ (z >>> 33)) * 0xc4ceb9fe1a85ec53L;
    return z ^ (z >>> 33);
  }

  /**
   * Enumerates every solution by placing objects one by one and checking each new object against
   * the objects placed before. Gives up (returns null) once more than limit solutions exist.
   */
  public Solutions bruteForce(boolean keep, long limit) {
    List<List<Placement>> cand = new ArrayList<>();
    for (Obj o : objects) {
      cand.add(placements(o));
    }
    // dims of the non-overlap constraints between object i and object j
    int n = objects.size();
    @SuppressWarnings("unchecked")
    List<int[]>[][] between = new List[n][n];
    Map<Integer, Integer> index = new HashMap<>();
    for (int i = 0; i < n; i++) {
      index.put(objects.get(i).no(), i);
    }
    for (NonOverlap no : nonOverlaps) {
      for (int a : no.objects()) {
        for (int b : no.objects()) {
          int i = index.get(a);
          int j = index.get(b);
          if (i < j) {
            if (between[j][i] == null) {
              between[j][i] = new ArrayList<>();
            }
            between[j][i].add(no.dims());
          }
        }
      }
    }
    Solutions sol = new Solutions(keep);
    Placement[] chosen = new Placement[n];
    if (!enumerate(cand, between, chosen, 0, sol, limit)) {
      return null;
    }
    return sol;
  }

  private boolean enumerate(
      List<List<Placement>> cand,
      List<int[]>[][] between,
      Placement[] chosen,
      int i,
      Solutions sol,
      long limit) {
    if (i == chosen.length) {
      sol.add(vector(chosen));
      return sol.count <= limit;
    }
    for (Placement p : cand.get(i)) {
      boolean ok = true;
      for (int j = 0; j < i && ok; j++) {
        if (between[i][j] != null) {
          for (int[] dims : between[i][j]) {
            if (conflict(p, chosen[j], dims)) {
              ok = false;
              break;
            }
          }
        }
      }
      if (ok) {
        chosen[i] = p;
        if (!enumerate(cand, between, chosen, i + 1, sol, limit)) {
          return false;
        }
      }
    }
    return true;
  }

  int[] vector(Placement[] chosen) {
    int w = varsPerObject();
    int[] v = new int[chosen.length * w];
    for (int i = 0; i < chosen.length; i++) {
      Placement p = chosen[i];
      System.arraycopy(p.x(), 0, v, i * w, k);
      v[i * w + k] = p.s();
      v[i * w + k + 1] = p.start();
      v[i * w + k + 2] = p.dur();
      v[i * w + k + 3] = p.end();
    }
    return v;
  }

  /** True when the solution vector satisfies the instance. */
  public boolean check(int[] v) {
    int w = varsPerObject();
    int n = objects.size();
    Placement[] p = new Placement[n];
    Map<Integer, Integer> index = new HashMap<>();
    for (int i = 0; i < n; i++) {
      Obj o = objects.get(i);
      index.put(o.no(), i);
      int[] x = Arrays.copyOfRange(v, i * w, i * w + k);
      p[i] = new Placement(x, v[i * w + k], v[i * w + k + 1], v[i * w + k + 2], v[i * w + k + 3]);
      for (int d = 0; d < k; d++) {
        if (Arrays.binarySearch(o.coords()[d], x[d]) < 0) {
          return false;
        }
      }
      if (Arrays.binarySearch(o.shape(), p[i].s()) < 0
          || Arrays.binarySearch(o.start(), p[i].start()) < 0
          || Arrays.binarySearch(o.dur(), p[i].dur()) < 0
          || Arrays.binarySearch(o.end(), p[i].end()) < 0
          || p[i].dur() < 1
          || p[i].start() + p[i].dur() != p[i].end()
          || !inArea(p[i])) {
        return false;
      }
    }
    for (NonOverlap no : nonOverlaps) {
      for (int a : no.objects()) {
        for (int b : no.objects()) {
          if (a < b && conflict(p[index.get(a)], p[index.get(b)], no.dims())) {
            return false;
          }
        }
      }
    }
    return true;
  }

  // ---------------------------------------------------------------------------------------------
  // Posting

  /** The variables of a posted model, in solution-vector order. */
  public record Posted(IntVar[] vars, Constraint constraint) {}

  static IntVar var(Store store, String name, int[] values) {
    IntervalDomain dom = new IntervalDomain();
    for (int v : values) {
      dom.unionAdapt(v, v);
    }
    return new IntVar(store, name, dom);
  }

  /** Variables in solution-vector order; singleton domains share one variable when asked. */
  IntVar[] variables(Store store, boolean shareSingletons) {
    Map<Integer, IntVar> constants = new HashMap<>();
    int w = varsPerObject();
    IntVar[] vars = new IntVar[objects.size() * w];
    for (int i = 0; i < objects.size(); i++) {
      Obj o = objects.get(i);
      int[][] doms = new int[w][];
      System.arraycopy(o.coords(), 0, doms, 0, k);
      doms[k] = o.shape();
      doms[k + 1] = o.start();
      doms[k + 2] = o.dur();
      doms[k + 3] = o.end();
      String[] names = {"s", "t", "d", "e"};
      for (int j = 0; j < w; j++) {
        String nm = (j < k ? "x" + j : names[j - k]) + "_" + o.no();
        if (shareSingletons && doms[j].length == 1) {
          vars[i * w + j] =
              constants.computeIfAbsent(doms[j][0], v -> new IntVar(store, "c" + v, v, v));
        } else {
          vars[i * w + j] = var(store, nm, doms[j]);
        }
      }
    }
    return vars;
  }

  static Dbox dbox(Box b) {
    return new Dbox(b.offset().clone(), b.length().clone());
  }

  /** Posts the instance as one Geost constraint. */
  public Posted postGeost(Store store, boolean shareSingletons) {
    return postGeost(store, shareSingletons, true);
  }

  /** Creates the variables and the Geost constraint, and imposes it when asked. */
  public Posted postGeost(Store store, boolean shareSingletons, boolean impose) {
    IntVar[] vars = variables(store, shareSingletons);
    List<GeostObject> objs = geostObjects(vars, range(objects.size()));
    Geost geost = new Geost(objs, externalConstraints(objs), geostShapes());
    if (impose) {
      store.impose(geost);
    }
    return new Posted(vars, geost);
  }

  /**
   * Posts the instance as one Geost constraint with its volume reasoning on or off, and with a
   * lexicographic chain over each group of interchangeable objects when asked.
   */
  public Posted postGeostWith(Store store, boolean volume, boolean lex) {
    IntVar[] vars = variables(store, false);
    List<GeostObject> objs = geostObjects(vars, range(objects.size()));
    List<ExternalConstraint> ecs = new ArrayList<>(externalConstraints(objs));
    if (lex) {
      for (List<Integer> group : interchangeableGroups()) {
        ecs.add(new LexChain(group.stream().map(objs::get).toArray(GeostObject[]::new)));
      }
    }
    Geost geost = new Geost(objs, ecs, geostShapes());
    geost.setVolumeReasoning(volume);
    store.impose(geost);
    return new Posted(vars, geost);
  }

  /**
   * The groups of two or more objects (by position) that are interchangeable: the same domains of
   * every variable and the same non-overlap constraints, so that swapping two of them maps
   * solutions to solutions.
   */
  public List<List<Integer>> interchangeableGroups() {
    Map<String, List<Integer>> groups = new LinkedHashMap<>();
    for (int i = 0; i < objects.size(); i++) {
      Obj o = objects.get(i);
      StringBuilder key = new StringBuilder();
      key.append(Arrays.deepToString(o.coords()))
          .append(Arrays.toString(o.shape()))
          .append(Arrays.toString(o.start()))
          .append(Arrays.toString(o.dur()))
          .append(Arrays.toString(o.end()));
      for (NonOverlap no : nonOverlaps) {
        key.append(Arrays.stream(no.objects()).anyMatch(x -> x == o.no()) ? '1' : '0');
      }
      groups.computeIfAbsent(key.toString(), x -> new ArrayList<>()).add(i);
    }
    return groups.values().stream().filter(g -> g.size() > 1).toList();
  }

  /**
   * Posts every non-overlap and the area as a Geost constraint of its own, over new Geost objects
   * of the same variables, so that several Geost constraints share variables.
   */
  public Posted postGeostSplit(Store store) {
    IntVar[] vars = variables(store, false);
    int w = varsPerObject();
    for (int i = 0; i < objects.size(); i++) {
      store.impose(new XgtC(vars[i * w + k + 2], 0));
      store.impose(new XplusYeqZ(vars[i * w + k + 1], vars[i * w + k + 2], vars[i * w + k + 3]));
    }
    Map<Integer, Integer> index = new HashMap<>();
    for (int i = 0; i < objects.size(); i++) {
      index.put(objects.get(i).no(), i);
    }
    for (NonOverlap no : nonOverlaps) {
      int[] scope = Arrays.stream(no.objects()).map(index::get).toArray();
      List<GeostObject> objs = geostObjects(vars, scope);
      store.impose(
          new Geost(
              objs,
              List.of(new NonOverlapping(objs.toArray(new GeostObject[0]), no.dims().clone())),
              geostShapes()));
    }
    if (area != null) {
      List<GeostObject> objs = geostObjects(vars, range(objects.size()));
      store.impose(new Geost(objs, List.of(inArea()), geostShapes()));
    }
    return new Posted(vars, null);
  }

  static int[] range(int n) {
    int[] r = new int[n];
    for (int i = 0; i < n; i++) {
      r[i] = i;
    }
    return r;
  }

  List<Shape> geostShapes() {
    List<Shape> shapeList = new ArrayList<>();
    for (int s = 0; s < shapes.size(); s++) {
      List<Dbox> boxes = new ArrayList<>();
      for (Box b : shapes.get(s)) {
        boxes.add(dbox(b));
      }
      shapeList.add(new Shape(s, boxes));
    }
    return shapeList;
  }

  /** Geost objects for the objects at the given positions (object numbers are kept). */
  List<GeostObject> geostObjects(IntVar[] vars, int[] positions) {
    int w = varsPerObject();
    List<GeostObject> objs = new ArrayList<>();
    for (int i : positions) {
      IntVar[] x = Arrays.copyOfRange(vars, i * w, i * w + k);
      objs.add(
          new GeostObject(
              objects.get(i).no(),
              x,
              vars[i * w + k],
              vars[i * w + k + 1],
              vars[i * w + k + 2],
              vars[i * w + k + 3]));
    }
    return objs;
  }

  List<ExternalConstraint> externalConstraints(List<GeostObject> objs) {
    // objs holds every object, in order
    Map<Integer, GeostObject> byNo = new HashMap<>();
    for (int i = 0; i < objs.size(); i++) {
      byNo.put(objects.get(i).no(), objs.get(i));
    }
    List<ExternalConstraint> ecs = new ArrayList<>();
    for (NonOverlap no : nonOverlaps) {
      GeostObject[] scope =
          Arrays.stream(no.objects()).mapToObj(byNo::get).toArray(GeostObject[]::new);
      ecs.add(new NonOverlapping(scope, no.dims().clone()));
    }
    if (area != null) {
      ecs.add(inArea());
    }
    return ecs;
  }

  InArea inArea() {
    List<Dbox> holes = new ArrayList<>();
    for (Box h : area.holes()) {
      holes.add(dbox(h));
    }
    return new InArea(dbox(area.box()), holes);
  }

  /**
   * Posts the instance as a pairwise decomposition into primitive constraints: for every pair of
   * objects in a non-overlap, every pair of shapes they may take and every pair of boxes, the
   * shapes differ or the boxes are apart in some selected dimension.
   */
  public Posted postDecomposition(Store store) {
    IntVar[] vars = variables(store, false);
    int w = varsPerObject();
    Map<Integer, Integer> index = new HashMap<>();
    for (int i = 0; i < objects.size(); i++) {
      index.put(objects.get(i).no(), i);
    }
    for (int i = 0; i < objects.size(); i++) {
      IntVar s = vars[i * w + k];
      store.impose(new XgtC(vars[i * w + k + 2], 0));
      store.impose(new XplusYeqZ(vars[i * w + k + 1], vars[i * w + k + 2], vars[i * w + k + 3]));
      if (area != null) {
        for (int sid : objects.get(i).shape()) {
          List<PrimitiveConstraint> inside = new ArrayList<>();
          for (Box b : shapes.get(sid)) {
            for (int d = 0; d < k; d++) {
              IntVar x = vars[i * w + d];
              inside.add(new XgteqC(x, area.box().offset()[d] - b.offset()[d]));
              inside.add(
                  new XlteqC(
                      x,
                      area.box().offset()[d]
                          + area.box().length()[d]
                          - b.offset()[d]
                          - b.length()[d]));
            }
            for (Box h : area.holes()) {
              List<PrimitiveConstraint> apart = new ArrayList<>();
              for (int d = 0; d < k; d++) {
                IntVar x = vars[i * w + d];
                // box ends before the hole, or starts after it
                apart.add(new XlteqC(x, h.offset()[d] - b.offset()[d] - b.length()[d]));
                apart.add(new XgteqC(x, h.offset()[d] + h.length()[d] - b.offset()[d]));
              }
              inside.add(new Or(apart));
            }
          }
          store.impose(new Or(new XneqC(s, sid), new And(inside)));
        }
      }
    }
    for (NonOverlap no : nonOverlaps) {
      for (int a : no.objects()) {
        for (int b : no.objects()) {
          if (a >= b) {
            continue;
          }
          int i = index.get(a);
          int j = index.get(b);
          for (int si : objects.get(i).shape()) {
            for (int sj : objects.get(j).shape()) {
              for (Box bi : shapes.get(si)) {
                for (Box bj : shapes.get(sj)) {
                  List<PrimitiveConstraint> or = new ArrayList<>();
                  or.add(new XneqC(vars[i * w + k], si));
                  or.add(new XneqC(vars[j * w + k], sj));
                  for (int d : no.dims()) {
                    if (d == k) {
                      or.add(new XlteqY(vars[i * w + k + 3], vars[j * w + k + 1]));
                      or.add(new XlteqY(vars[j * w + k + 3], vars[i * w + k + 1]));
                    } else {
                      IntVar xi = vars[i * w + d];
                      IntVar xj = vars[j * w + d];
                      // xi + oi + li <= xj + oj
                      or.add(
                          new XplusClteqZ(
                              xi, bi.offset()[d] + bi.length()[d] - bj.offset()[d], xj));
                      or.add(
                          new XplusClteqZ(
                              xj, bj.offset()[d] + bj.length()[d] - bi.offset()[d], xi));
                    }
                  }
                  store.impose(new Or(or));
                }
              }
            }
          }
        }
      }
    }
    return new Posted(vars, null);
  }

  /**
   * True when the instance is a plain packing that Diffn and Diff2 can express: one or two
   * dimensions, one non-overlap over all objects that selects every spatial dimension, and time
   * that either is not selected or is the same fixed interval for every object.
   */
  public boolean diffnExpressible() {
    if (k > 2 || nonOverlaps.size() != 1) {
      return false;
    }
    NonOverlap no = nonOverlaps.get(0);
    if (no.objects().length != objects.size()) {
      return false;
    }
    boolean time = false;
    int spatial = 0;
    for (int d : no.dims()) {
      if (d == k) {
        time = true;
      } else {
        spatial++;
      }
    }
    if (spatial != k) {
      return false;
    }
    if (time) {
      int[] t0 = objects.get(0).start();
      int[] e0 = objects.get(0).end();
      for (Obj o : objects) {
        if (o.start().length != 1
            || o.end().length != 1
            || o.start()[0] != t0[0]
            || o.end()[0] != e0[0]) {
          return false;
        }
      }
    }
    return true;
  }

  /** True when every object chooses among shapes with the same number of boxes. */
  public boolean sameBoxCounts() {
    for (Obj o : objects) {
      int n = shapes.get(o.shape()[0]).size();
      for (int s : o.shape()) {
        if (shapes.get(s).size() != n) {
          return false;
        }
      }
    }
    return true;
  }

  /** Which rectangle constraint to use for {@link #postRectangles}. */
  public enum Rect {
    DIFFN_STRICT,
    DIFFN_NONSTRICT,
    NOOVERLAP_STRICT,
    DIFF2
  }

  /**
   * Posts a plain packing (see {@link #diffnExpressible()}) as one rectangle constraint over the
   * boxes of all objects, holes as fixed rectangles, the area as bounds on the box origins and time
   * as start + duration = end. A 1-D instance gets a second dimension of height 1. Objects whose
   * shapes have fewer boxes get boxes of size 0, so only the non-strict constraints apply then.
   */
  public Posted postRectangles(Store store, Rect kind) {
    return postRectangles(store, kind, true);
  }

  /**
   * Like {@link #postRectangles(Store, Rect)}, but the rectangle constraint itself is only imposed
   * when asked (the constraints that define the rectangles always are).
   */
  public Posted postRectangles(Store store, Rect kind, boolean impose) {
    IntVar[] vars = variables(store, false);
    int w = varsPerObject();
    List<List<IntVar>> rects = new ArrayList<>();
    IntVar zero = new IntVar(store, "zero", 0, 0);
    IntVar one = new IntVar(store, "one", 1, 1);
    for (int i = 0; i < objects.size(); i++) {
      Obj o = objects.get(i);
      IntVar s = vars[i * w + k];
      store.impose(new XgtC(vars[i * w + k + 2], 0));
      store.impose(new XplusYeqZ(vars[i * w + k + 1], vars[i * w + k + 2], vars[i * w + k + 3]));
      int maxBoxes = 0;
      for (int sid : o.shape()) {
        maxBoxes = Math.max(maxBoxes, shapes.get(sid).size());
      }
      for (int b = 0; b < maxBoxes; b++) {
        IntVar[] origin = new IntVar[2];
        IntVar[] length = new IntVar[2];
        for (int d = 0; d < 2; d++) {
          if (d >= k) {
            origin[d] = zero;
            length[d] = one;
            continue;
          }
          int[] off = new int[shapes.size()];
          int[] len = new int[shapes.size()];
          for (int sid = 0; sid < shapes.size(); sid++) {
            List<Box> boxes = shapes.get(sid);
            Box box = b < boxes.size() ? boxes.get(b) : boxes.get(0);
            off[sid] = box.offset()[d];
            len[sid] = b < boxes.size() ? box.length()[d] : 0;
          }
          IntVar offVar = new IntVar(store, -1000, 1000);
          IntVar lenVar = new IntVar(store, 0, 1000);
          store.impose(new ElementInteger(s, off, offVar, -1));
          store.impose(new ElementInteger(s, len, lenVar, -1));
          origin[d] = new IntVar(store, -10000, 10000);
          store.impose(new XplusYeqZ(vars[i * w + d], offVar, origin[d]));
          length[d] = lenVar;
          if (area != null) {
            store.impose(new XgteqC(origin[d], area.box().offset()[d]));
            IntVar endVar = new IntVar(store, -10000, 10000);
            store.impose(new XplusYeqZ(origin[d], lenVar, endVar));
            store.impose(new XlteqC(endVar, area.box().offset()[d] + area.box().length()[d]));
          }
        }
        rects.add(List.of(origin[0], origin[1], length[0], length[1]));
      }
    }
    if (area != null) {
      // holes may overlap each other, so the obstacles are the unit cells of their union
      Set<List<Integer>> cells = new HashSet<>();
      for (Box h : area.holes()) {
        for (int x = 0; x < h.length()[0]; x++) {
          for (int y = 0; y < (k > 1 ? h.length()[1] : 1); y++) {
            cells.add(List.of(h.offset()[0] + x, k > 1 ? h.offset()[1] + y : 0));
          }
        }
      }
      for (List<Integer> cell : cells) {
        IntVar[] r = new IntVar[4];
        for (int d = 0; d < 2; d++) {
          r[d] = new IntVar(store, cell.get(d), cell.get(d));
          r[d + 2] = one;
        }
        rects.add(List.of(r));
      }
    }
    Constraint c =
        switch (kind) {
          case DIFFN_STRICT -> new Diffn(rects, true);
          case DIFFN_NONSTRICT -> new Diffn(rects, false);
          case NOOVERLAP_STRICT -> new Nooverlap(rects, true);
          case DIFF2 -> new Diff2(rects);
        };
    if (impose && rects.size() > 1) {
      store.impose(c);
    }
    return new Posted(vars, c);
  }

  @Override
  public String toString() {
    return format();
  }
}
