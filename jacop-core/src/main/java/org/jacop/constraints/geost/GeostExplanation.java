/*
 * GeostExplanation.java
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

package org.jacop.constraints.geost;

import java.util.ArrayList;
import java.util.List;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Reasons of the pruning and failures of {@link Geost} under lazy clause generation.
 *
 * <p>Geost prunes by sweeping (Beldiceanu, Carlsson, Poder, Sadek and Truchet, "A Generic
 * Geometrical Constraint Kernel in Space and Time for Handling Polymorphic k-Dimensional Objects",
 * CP 2007): a bound of an object's coordinate moves past the points of its origin domain that lie
 * in forbidden regions, and a shape is removed when every point of the domain is forbidden for it.
 * A point is forbidden by the compulsory part of another object it must not overlap, or by an
 * {@link InArea} constraint. So an atom is implied by a set of forbidden boxes covering the swept
 * region, and its reason is the atoms those boxes come from, in the style of the explanations of
 * the sweep for non-overlapping rectangles by Schutt, Feydy and Stuckey ("Explaining
 * time-table-edge-finding propagation for the cumulative resource constraint", CPAIOR 2013, and the
 * diffn explanations of the same authors): the bounds of the explained object that delimit the
 * region, the shapes it may still take, and for each obstacle the bounds that make its compulsory
 * part.
 *
 * <p>The region is recomputed on the bounds just before the explained atom (or now, for a failure)
 * and covered by the forbidden boxes of:
 *
 * <ul>
 *   <li>each object it must not overlap ({@link NonOverlapping}) whose shape is fixed, or whose
 *       shapes are boxes, with times fixed from the start and overlapping when time is selected:
 *       for a fixed shape, the part of each of its boxes covered at every position of its origin
 *       domain; otherwise the part common to all its shapes' boxes;
 *   <li>the outside of the allowed area and the holes of each {@link InArea}, which need no atom.
 * </ul>
 *
 * Obstacles that the cover does not need are dropped, the latest first. A region that these boxes
 * do not cover (holes of the origin domains, lexicographic ordering, volume reasoning, times that
 * vary) is left to the generic reason.
 */
final class GeostExplanation {

  /** Work allowed to one cover test, in boxes split. */
  private static final int COVER_BUDGET = 20_000;

  private final Geost geost;
  private final int k;

  // for each object, the objects it must not overlap and the spatial dimensions in which
  private final int[][] obstacle;
  private final boolean[][][] obstacleDims;
  private final boolean[][] obstacleTime;

  // the forbidden origin boxes of each shape by InArea, inclusive bounds [lo, hi] per dimension
  private final List<long[][]>[] staticBoxes;

  private int budget;

  @SuppressWarnings("unchecked")
  private GeostExplanation(Geost geost) {
    this.geost = geost;
    this.k = geost.dimension;
    int n = geost.objects.length;
    List<Integer>[] obs = new List[n];
    List<boolean[]>[] dims = new List[n];
    List<Boolean>[] time = new List[n];
    for (int i = 0; i < n; i++) {
      obs[i] = new ArrayList<>();
      dims[i] = new ArrayList<>();
      time[i] = new ArrayList<>();
    }
    List<InArea> areas = new ArrayList<>();
    for (ExternalConstraint e : geost.externalConstraints) {
      if (e instanceof NonOverlapping no) {
        boolean[] sel = new boolean[k];
        boolean useTime = false;
        for (int d : no.selectedDimensions) {
          if (d == k) {
            useTime = true;
          } else {
            sel[d] = true;
          }
        }
        for (GeostObject a : no.objects) {
          int ia = index(a);
          for (GeostObject b : no.objects) {
            if (a != b) {
              obs[ia].add(index(b));
              dims[ia].add(sel);
              time[ia].add(useTime);
            }
          }
        }
      } else if (e instanceof InArea in) {
        areas.add(in);
      }
    }
    obstacle = new int[n][];
    obstacleDims = new boolean[n][][];
    obstacleTime = new boolean[n][];
    for (int i = 0; i < n; i++) {
      obstacle[i] = obs[i].stream().mapToInt(Integer::intValue).toArray();
      obstacleDims[i] = dims[i].toArray(new boolean[0][]);
      obstacleTime[i] = new boolean[time[i].size()];
      for (int t = 0; t < obstacleTime[i].length; t++) {
        obstacleTime[i][t] = time[i].get(t);
      }
    }
    staticBoxes = new List[geost.shapeRegister.length];
    for (int s = 0; s < staticBoxes.length; s++) {
      Shape shape = geost.shapeRegister[s];
      staticBoxes[s] = new ArrayList<>();
      if (shape == null) {
        continue;
      }
      for (InArea in : areas) {
        Dbox bb = shape.boundingBox();
        Dbox a = in.allowedArea;
        for (int i = 0; i < k; i++) {
          long lo = (long) a.origin[i] - bb.origin[i];
          long hi = (long) a.origin[i] + a.length[i] - bb.length[i] - bb.origin[i];
          staticBoxes[s].add(slab(i, Long.MIN_VALUE / 4, lo - 1));
          staticBoxes[s].add(slab(i, hi + 1, Long.MAX_VALUE / 4));
        }
        for (Dbox hole : in.holes) {
          for (Dbox p : shape.boxes) {
            long[][] box = new long[k][2];
            boolean empty = false;
            for (int i = 0; i < k; i++) {
              long len = (long) hole.length[i] + p.length[i] - 1;
              box[i][0] = (long) hole.origin[i] - (p.length[i] - 1) - p.origin[i];
              box[i][1] = box[i][0] + len - 1;
              empty |= len <= 0;
            }
            if (!empty) {
              staticBoxes[s].add(box);
            }
          }
        }
      }
    }
  }

  private long[][] slab(int dim, long lo, long hi) {
    long[][] box = new long[k][2];
    for (int i = 0; i < k; i++) {
      box[i][0] = Long.MIN_VALUE / 4;
      box[i][1] = Long.MAX_VALUE / 4;
    }
    box[dim][0] = lo;
    box[dim][1] = hi;
    return box;
  }

  private int index(GeostObject o) {
    for (int i = 0; i < geost.objects.length; i++) {
      if (geost.objects[i] == o) {
        return i;
      }
    }
    throw new IllegalStateException("object " + o + " is not in " + geost);
  }

  static GeostExplanation of(Geost geost) {
    return new GeostExplanation(geost);
  }

  /**
   * Adds the reason of an atom of a Geost constraint.
   *
   * @return false when no cover found here implies it
   */
  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    GeostObject[] objects = geost.objects;
    for (int o = 0; o < objects.length; o++) {
      GeostObject obj = objects[o];
      int mark = out.size();
      if (obj.shapeId == y) {
        if (explainShape(trail, o, entry, out)) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
      }
      for (int d = 0; d < k; d++) {
        if (obj.coords[d] != y) {
          continue;
        }
        long[][] region = box(trail, obj, entry);
        if (kind == AtomicTrail.GE) {
          region[d][1] = trail.value(entry) - 1L;
        } else if (kind == AtomicTrail.LE) {
          region[d][0] = trail.value(entry) + 1L;
        } else {
          region[d][0] = trail.value(entry);
          region[d][1] = trail.value(entry);
        }
        if (region[d][0] > region[d][1]) {
          // already outside the bounds before: nothing to cover beyond the bound itself
          if (kind == AtomicTrail.GE) {
            trail.addBoundReaching(obj.coords[d], entry, true, trail.value(entry), out);
          } else if (kind == AtomicTrail.LE) {
            trail.addBoundReaching(obj.coords[d], entry, false, trail.value(entry), out);
          } else {
            trail.excludedBefore(obj.coords[d], trail.value(entry), entry, out);
          }
          out.sortUnique(mark);
          return true;
        }
        if (coverAllShapes(trail, o, region, entry, out, kind == AtomicTrail.NE ? -1 : d)) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  /**
   * Adds the reason of a failure of a Geost constraint: an object none of whose shapes fits
   * anywhere in its origin domain.
   *
   * @return false when no object is found so
   */
  boolean explainFailure(AtomicTrail trail, EntryList out) {
    int position = trail.size();
    for (int o = 0; o < geost.objects.length; o++) {
      int mark = out.size();
      long[][] region = box(trail, geost.objects[o], position);
      if (coverAllShapes(trail, o, region, position, out, -1)) {
        out.sortUnique(mark);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  // the origin box of an object just before a position, inclusive bounds per dimension
  private long[][] box(AtomicTrail trail, GeostObject obj, int position) {
    long[][] region = new long[k][2];
    for (int i = 0; i < k; i++) {
      region[i][0] = trail.minBefore(obj.coords[i], position);
      region[i][1] = trail.maxBefore(obj.coords[i], position);
    }
    return region;
  }

  // the shapes removed by a shape atom must each be infeasible in the whole origin box
  private boolean explainShape(AtomicTrail trail, int o, int entry, EntryList out) {
    GeostObject obj = geost.objects[o];
    long[][] region = box(trail, obj, entry);
    int lo = Math.max(trail.removedMin(entry), trail.minBefore(obj.shapeId, entry));
    int hi = Math.min(trail.removedMax(entry), trail.maxBefore(obj.shapeId, entry));
    EntryList scratch = new EntryList();
    boolean any = false;
    for (int s = lo; s <= hi; s++) {
      scratch.clear();
      if (trail.excludedBefore(obj.shapeId, s, entry, scratch)) {
        continue;
      }
      if (!validShape(s) || !cover(trail, o, s, region, entry, out)) {
        return false;
      }
      any = true;
    }
    if (any) {
      citeRegion(trail, obj, region, entry, -1, out);
    }
    return any;
  }

  /**
   * Whether the region is forbidden for every shape the object may take before the position; if so,
   * adds the reason: the region's bounds (all but the lower and upper bound of the swept dimension,
   * which the explained atom replaces), the shapes excluded, and the obstacles used.
   */
  private boolean coverAllShapes(
      AtomicTrail trail, int o, long[][] region, int position, EntryList out, int swept) {
    GeostObject obj = geost.objects[o];
    IntVar shape = obj.shapeId;
    int sMin = trail.minBefore(shape, position);
    int sMax = trail.maxBefore(shape, position);
    EntryList scratch = new EntryList();
    for (int s = sMin; s <= sMax; s++) {
      scratch.clear();
      if (trail.excludedBefore(shape, s, position, scratch)) {
        continue;
      }
      if (!validShape(s) || !cover(trail, o, s, region, position, out)) {
        return false;
      }
    }
    // the shapes outside the domain
    trail.addBoundReaching(shape, position, true, sMin, out);
    trail.addBoundReaching(shape, position, false, sMax, out);
    for (int s = sMin + 1; s < sMax; s++) {
      trail.excludedBefore(shape, s, position, out);
    }
    citeRegion(trail, obj, region, position, swept, out);
    return true;
  }

  private boolean validShape(int s) {
    return s >= 0 && s < geost.shapeRegister.length && geost.shapeRegister[s] != null;
  }

  // the bounds of the object's origin that delimit the region; in the swept dimension only the
  // side the explained atom does not give
  private void citeRegion(
      AtomicTrail trail, GeostObject obj, long[][] region, int position, int swept, EntryList out) {
    for (int i = 0; i < k; i++) {
      IntVar x = obj.coords[i];
      boolean regionLow = region[i][0] == trail.minBefore(x, position);
      boolean regionHigh = region[i][1] == trail.maxBefore(x, position);
      if (regionLow) {
        trail.addBoundReaching(x, position, true, region[i][0], out);
      }
      if (regionHigh) {
        trail.addBoundReaching(x, position, false, region[i][1], out);
      }
      if (i == swept && !regionLow && !regionHigh) {
        throw new IllegalStateException("swept region not at a bound");
      }
    }
  }

  // an obstacle's forbidden boxes for one shape of the explained object
  // or a run of values removed from one coordinate of the explained object (object -1)
  private static final class Obstacle {
    final int object;
    final List<long[][]> boxes = new ArrayList<>();
    final boolean[] dims;
    int latest;
    IntVar holeVar;
    int holeFrom;
    int holeTo;

    Obstacle(int object, boolean[] dims) {
      this.object = object;
      this.dims = dims;
    }
  }

  /** The most values of one coordinate checked for holes in a region. */
  private static final int HOLE_SPAN = 256;

  // the runs of values removed from the object's coordinates inside the region, as slabs
  private void holes(
      AtomicTrail trail, GeostObject obj, long[][] region, int position, List<Obstacle> out) {
    EntryList scratch = new EntryList();
    for (int i = 0; i < k; i++) {
      IntVar x = obj.coords[i];
      if (region[i][1] - region[i][0] > HOLE_SPAN) {
        continue;
      }
      Obstacle run = null;
      for (int v = (int) region[i][0]; v <= region[i][1]; v++) {
        scratch.clear();
        boolean removed = trail.excludedBefore(x, v, position, scratch);
        if (!removed) {
          run = null;
          continue;
        }
        int latest = scratch.size() > 0 ? scratch.get(0) : -1;
        if (run == null) {
          run = new Obstacle(-1, null);
          run.holeVar = x;
          run.holeFrom = v;
          run.boxes.add(slab(i, v, v));
          out.add(run);
        }
        run.holeTo = v;
        run.boxes.get(0)[i][1] = v;
        run.latest = Math.max(run.latest, latest);
      }
    }
  }

  /**
   * Whether shape s of object o is forbidden everywhere in the region; if so, adds the atoms of the
   * obstacles needed.
   */
  private boolean cover(
      AtomicTrail trail, int o, int s, long[][] region, int position, EntryList out) {
    GeostObject obj = geost.objects[o];
    Shape shape = geost.shapeRegister[s];
    List<long[][]> fixed = new ArrayList<>();
    for (long[][] b : staticBoxes[s]) {
      if (intersects(b, region)) {
        fixed.add(b);
      }
    }
    List<Obstacle> obstacles = new ArrayList<>();
    for (int t = 0; t < obstacle[o].length; t++) {
      Obstacle ob = obstacle(trail, obj, shape, t, obstacle[o][t], region, position);
      if (ob != null) {
        obstacles.add(ob);
      }
    }
    holes(trail, obj, region, position, obstacles);
    if (!covered(region, fixed, obstacles, -1)) {
      return false;
    }
    // drop the obstacles the cover does not need, those with the latest atoms first
    obstacles.sort((p, q) -> Integer.compare(q.latest, p.latest));
    for (int t = 0; t < obstacles.size(); ) {
      if (covered(region, fixed, obstacles, t)) {
        obstacles.remove(t);
      } else {
        t++;
      }
    }
    for (Obstacle ob : obstacles) {
      citeObstacle(trail, ob, position, out);
    }
    return true;
  }

  private Obstacle obstacle(
      AtomicTrail trail,
      GeostObject obj,
      Shape shape,
      int t,
      int j,
      long[][] region,
      int position) {
    GeostObject other = geost.objects[j];
    if (other == obj) {
      return null;
    }
    if (obstacleTime[indexOf(obj)][t] && !timesOverlap(trail, obj, other)) {
      return null;
    }
    boolean[] dims = obstacleDims[indexOf(obj)][t];
    // the boxes of the obstacle present at every position of its origin domain
    List<long[][]> frames = frames(trail, other, position, dims);
    if (frames == null || frames.isEmpty()) {
      return null;
    }
    Obstacle ob = new Obstacle(j, dims);
    for (long[][] frame : frames) {
      for (Dbox p : shape.boxes) {
        long[][] box = new long[k][2];
        boolean empty = false;
        for (int i = 0; i < k; i++) {
          if (!dims[i]) {
            box[i][0] = Long.MIN_VALUE / 4;
            box[i][1] = Long.MAX_VALUE / 4;
            continue;
          }
          long len = frame[i][1] + p.length[i] - 1;
          box[i][0] = frame[i][0] - (p.length[i] - 1) - p.origin[i];
          box[i][1] = box[i][0] + len - 1;
          empty |= len <= 0;
        }
        if (!empty && intersects(box, region)) {
          ob.boxes.add(box);
        }
      }
    }
    if (ob.boxes.isEmpty()) {
      return null;
    }
    int latest = -1;
    for (int i = 0; i < k; i++) {
      if (dims[i]) {
        latest = Math.max(latest, trail.boundEntry(other.coords[i], position, true));
        latest = Math.max(latest, trail.boundEntry(other.coords[i], position, false));
      }
    }
    latest = Math.max(latest, trail.boundEntry(other.shapeId, position, true));
    latest = Math.max(latest, trail.boundEntry(other.shapeId, position, false));
    ob.latest = latest;
    return ob;
  }

  private int indexOf(GeostObject obj) {
    return obj.no >= 0 && obj.no < geost.objects.length && geost.objects[obj.no] == obj
        ? obj.no
        : index(obj);
  }

  /**
   * The compulsory parts of an object as {origin, length} per dimension (length may be 0, as in
   * Geost's frames, for a fixed shape), or null when its shapes are not handled here.
   */
  private List<long[][]> frames(
      AtomicTrail trail, GeostObject other, int position, boolean[] dims) {
    IntVar sv = other.shapeId;
    int sMin = trail.minBefore(sv, position);
    int sMax = trail.maxBefore(sv, position);
    if (sMin != sMax) {
      return commonFrames(trail, other, position, dims, sMin, sMax);
    }
    if (!validShape(sMin)) {
      return null;
    }
    List<long[][]> frames = new ArrayList<>();
    for (Dbox b : geost.shapeRegister[sMin].boxes) {
      long[][] frame = frame(trail, other, position, dims, b);
      if (frame != null) {
        frames.add(frame);
      }
    }
    return frames;
  }

  /** The most boxes kept while intersecting the compulsory parts of several shapes. */
  private static final int COMMON_LIMIT = 64;

  /**
   * The cells an object of several possible shapes covers whichever shape and origin it takes: the
   * intersection over its shapes of the union of the compulsory parts of each shape's boxes (only
   * parts of positive length), as {origin, length} per dimension.
   */
  private List<long[][]> commonFrames(
      AtomicTrail trail, GeostObject other, int position, boolean[] dims, int sMin, int sMax) {
    List<long[][]> common = null;
    EntryList scratch = new EntryList();
    for (int s = sMin; s <= sMax; s++) {
      scratch.clear();
      if (trail.excludedBefore(other.shapeId, s, position, scratch)) {
        continue;
      }
      if (!validShape(s)) {
        return null;
      }
      List<long[][]> own = new ArrayList<>();
      for (Dbox b : geost.shapeRegister[s].boxes) {
        long[][] frame = frame(trail, other, position, dims, b);
        if (frame != null && positive(frame, dims)) {
          own.add(frame);
        }
      }
      if (common == null) {
        common = own;
      } else {
        List<long[][]> next = new ArrayList<>();
        for (long[][] a : common) {
          for (long[][] b : own) {
            long[][] c = new long[k][2];
            boolean empty = false;
            for (int i = 0; i < k && !empty; i++) {
              if (!dims[i]) {
                continue;
              }
              long lo = Math.max(a[i][0], b[i][0]);
              long hi = Math.min(a[i][0] + a[i][1], b[i][0] + b[i][1]);
              c[i][0] = lo;
              c[i][1] = hi - lo;
              empty = hi <= lo;
            }
            if (!empty) {
              next.add(c);
            }
          }
        }
        if (next.size() > COMMON_LIMIT) {
          return null;
        }
        common = next;
      }
      if (common.isEmpty()) {
        return common;
      }
    }
    return common;
  }

  private boolean positive(long[][] frame, boolean[] dims) {
    for (int i = 0; i < k; i++) {
      if (dims[i] && frame[i][1] <= 0) {
        return false;
      }
    }
    return true;
  }

  // the compulsory part of one box of an object, {origin, length} per dimension (length may be 0,
  // as in Geost's frames), or null when it has none
  private long[][] frame(
      AtomicTrail trail, GeostObject other, int position, boolean[] dims, Dbox b) {
    long[][] frame = new long[k][2];
    for (int i = 0; i < k; i++) {
      if (!dims[i]) {
        continue;
      }
      long min = trail.minBefore(other.coords[i], position);
      long max = trail.maxBefore(other.coords[i], position);
      frame[i][0] = max + b.origin[i];
      frame[i][1] = min + b.length[i] - max;
      if (frame[i][1] < 0 || b.length[i] <= 0) {
        return null;
      }
    }
    return frame;
  }

  private void citeObstacle(AtomicTrail trail, Obstacle ob, int position, EntryList out) {
    if (ob.object < 0) {
      for (int v = ob.holeFrom; v <= ob.holeTo; v++) {
        trail.excludedBefore(ob.holeVar, v, position, out);
      }
      return;
    }
    GeostObject other = geost.objects[ob.object];
    for (int i = 0; i < k; i++) {
      if (ob.dims[i]) {
        IntVar x = other.coords[i];
        trail.addBoundReaching(x, position, true, trail.minBefore(x, position), out);
        trail.addBoundReaching(x, position, false, trail.maxBefore(x, position), out);
      }
    }
    IntVar sv = other.shapeId;
    int sMin = trail.minBefore(sv, position);
    int sMax = trail.maxBefore(sv, position);
    trail.addBoundReaching(sv, position, true, sMin, out);
    trail.addBoundReaching(sv, position, false, sMax, out);
    for (int s = sMin + 1; s < sMax; s++) {
      trail.excludedBefore(sv, s, position, out);
    }
  }

  // times fixed from the start of recording, of positive duration, and overlapping
  private static boolean timesOverlap(AtomicTrail trail, GeostObject a, GeostObject b) {
    if (!fixedFromStart(trail, a) || !fixedFromStart(trail, b)) {
      return false;
    }
    int sa = a.start.value();
    int ea = a.end.value();
    int sb = b.start.value();
    int eb = b.end.value();
    return a.duration.value() > 0
        && b.duration.value() > 0
        && sa + a.duration.value() == ea
        && sb + b.duration.value() == eb
        && sa < eb
        && sb < ea;
  }

  private static boolean fixedFromStart(AtomicTrail trail, GeostObject a) {
    return root(trail, a.start).singleton()
        && root(trail, a.duration).singleton()
        && root(trail, a.end).singleton();
  }

  private static IntDomain root(AtomicTrail trail, IntVar x) {
    return trail.rootDomain(x);
  }

  private static boolean intersects(long[][] a, long[][] b) {
    for (int i = 0; i < a.length; i++) {
      if (a[i][1] < b[i][0] || b[i][1] < a[i][0]) {
        return false;
      }
    }
    return true;
  }

  // whether the region is covered by the fixed boxes and the obstacles' boxes, leaving out
  // obstacle skip (-1 for none)
  private boolean covered(
      long[][] region, List<long[][]> fixed, List<Obstacle> obstacles, int skip) {
    List<long[][]> boxes = new ArrayList<>(fixed);
    for (int t = 0; t < obstacles.size(); t++) {
      if (t != skip) {
        boxes.addAll(obstacles.get(t).boxes);
      }
    }
    budget = COVER_BUDGET;
    return covered(region, boxes, 0);
  }

  private boolean covered(long[][] region, List<long[][]> boxes, int from) {
    if (--budget < 0) {
      return false;
    }
    int f = from;
    while (f < boxes.size() && !intersects(boxes.get(f), region)) {
      f++;
    }
    if (f == boxes.size()) {
      return false;
    }
    long[][] b = boxes.get(f);
    // the region minus b, as slabs below and above b in each dimension in turn
    long[][] rest = new long[k][];
    for (int i = 0; i < k; i++) {
      rest[i] = region[i].clone();
    }
    for (int i = 0; i < k; i++) {
      if (rest[i][0] < b[i][0]) {
        long[][] piece = copy(rest);
        piece[i][1] = b[i][0] - 1;
        if (!covered(piece, boxes, f + 1)) {
          return false;
        }
        rest[i][0] = b[i][0];
      }
      if (rest[i][1] > b[i][1]) {
        long[][] piece = copy(rest);
        piece[i][0] = b[i][1] + 1;
        if (!covered(piece, boxes, f + 1)) {
          return false;
        }
        rest[i][1] = b[i][1];
      }
    }
    return true;
  }

  private static long[][] copy(long[][] a) {
    long[][] c = new long[a.length][];
    for (int i = 0; i < a.length; i++) {
      c[i] = a[i].clone();
    }
    return c;
  }
}
