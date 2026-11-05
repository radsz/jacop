/*
 * VolumeCheck.java
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

import java.util.Arrays;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Volume reasoning for one non-overlapping group of geost objects, like SICStus's geost option
 * volume. It is an overload check in each dimension of the group: for every window [a, b) of a
 * dimension, the objects whose every placement lies inside the window must have a total volume no
 * larger than the window times the extent of their hull in the other dimensions.
 *
 * <p>Where an object may be is bounded by its coordinates and its possible shapes, and by the area
 * of the InArea constraints, which every object of the geost lies in.
 *
 * <p>The volume of an object is the smallest area of its possible shapes, times its smallest
 * duration when the group is non-overlapping in time too. It applies only to groups that select
 * every spatial dimension: objects of a group that leaves a dimension out may overlap in it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class VolumeCheck {

  final Geost geost;

  final GeostObject[] objects;

  /** The checked dimensions: the spatial ones, then time if the group selects it. */
  final int dims;

  final boolean useTime;

  /** Per object and dimension, the lowest and highest point an object may occupy (exclusive). */
  final long[] lo;

  final long[] hi;

  /** Per object, a lower bound of its volume. */
  final long[] vol;

  /** Object indices sorted by lo in the dimension checked, kept between calls. */
  final int[] byLo;

  /** The hi values of the dimension checked, sorted. */
  final long[] ends;

  final long[] hullLo;

  final long[] hullHi;

  /** The space every object lies in (the intersection of the InArea boxes), per dimension. */
  final long[] spaceLo;

  final long[] spaceHi;

  VolumeCheck(Geost geost, GeostObject[] objects, boolean useTime) {
    this.geost = geost;
    this.objects = objects;
    this.useTime = useTime;
    this.dims = geost.dimension + (useTime ? 1 : 0);
    int n = objects.length;
    lo = new long[n * dims];
    hi = new long[n * dims];
    vol = new long[n];
    byLo = new int[n];
    for (int i = 0; i < n; i++) {
      byLo[i] = i;
    }
    ends = new long[n];
    hullLo = new long[dims];
    hullHi = new long[dims];
    spaceLo = new long[dims];
    spaceHi = new long[dims];
    Arrays.fill(spaceLo, Long.MIN_VALUE);
    Arrays.fill(spaceHi, Long.MAX_VALUE);
    for (ExternalConstraint ec : geost.externalConstraints) {
      if (ec instanceof InArea in) {
        for (int i = 0; i < geost.dimension; i++) {
          spaceLo[i] = Math.max(spaceLo[i], in.allowedArea.origin[i]);
          spaceHi[i] =
              Math.min(spaceHi[i], (long) in.allowedArea.origin[i] + in.allowedArea.length[i]);
        }
      }
    }
  }

  /**
   * It checks the volume of the group.
   *
   * @throws org.jacop.core.FailException if some window holds objects of a larger volume.
   */
  void check() {
    if (!computeExtents()) {
      return;
    }
    for (int d = 0; d < dims; d++) {
      checkDimension(d);
    }
  }

  /** It computes the extents and volumes of the objects; false if no object has a volume. */
  private boolean computeExtents() {
    final int k = geost.dimension;
    long total = 0;
    for (int o = 0; o < objects.length; o++) {
      GeostObject obj = objects[o];
      int base = o * dims;
      for (int i = 0; i < k; i++) {
        lo[base + i] = Long.MAX_VALUE;
        hi[base + i] = Long.MIN_VALUE;
      }
      long area = Long.MAX_VALUE;
      ValueEnumeration sids = obj.shapeId.domain.valueEnumeration();
      while (sids.hasMoreElements()) {
        Shape shape = geost.getShape(sids.nextElement());
        Dbox bb = shape.boundingBox();
        for (int i = 0; i < k; i++) {
          lo[base + i] = Math.min(lo[base + i], (long) obj.coords[i].min() + bb.origin[i]);
          hi[base + i] =
              Math.max(hi[base + i], (long) obj.coords[i].max() + bb.origin[i] + bb.length[i]);
        }
        area = Math.min(area, shape.area());
      }
      // the coordinates are not bounded per shape: an InArea bounds the extent better
      for (int i = 0; i < k; i++) {
        lo[base + i] = Math.max(lo[base + i], spaceLo[i]);
        hi[base + i] = Math.min(hi[base + i], spaceHi[i]);
      }
      if (useTime) {
        lo[base + k] = obj.start.min();
        hi[base + k] = obj.end.max();
        area *= Math.max(obj.duration.min(), 0);
      }
      vol[o] = area;
      total += area;
    }
    return total > 0;
  }

  /** It checks every window of dimension d whose ends are an object's lo and another's hi. */
  private void checkDimension(int d) {
    final int n = objects.length;

    // insertion sort: the order changes little between calls
    for (int i = 1; i < n; i++) {
      int obj = byLo[i];
      long key = lo[obj * dims + d];
      int j = i - 1;
      while (j >= 0 && lo[byLo[j] * dims + d] > key) {
        byLo[j + 1] = byLo[j];
        j--;
      }
      byLo[j + 1] = obj;
    }
    for (int o = 0; o < n; o++) {
      ends[o] = hi[o * dims + d];
    }
    Arrays.sort(ends);

    for (int e = 0; e < n; e++) {
      long b = ends[e];
      if (e + 1 < n && ends[e + 1] == b) {
        continue;
      }
      Arrays.fill(hullLo, Long.MAX_VALUE);
      Arrays.fill(hullHi, Long.MIN_VALUE);
      long volume = 0;
      for (int p = n - 1; p >= 0; p--) {
        int obj = byLo[p];
        int base = obj * dims;
        if (hi[base + d] > b || vol[obj] == 0) {
          continue;
        }
        volume += vol[obj];
        for (int i = 0; i < dims; i++) {
          hullLo[i] = Math.min(hullLo[i], lo[base + i]);
          hullHi[i] = Math.max(hullHi[i], hi[base + i]);
        }
        if (volume > capacity(d, b - lo[base + d])) {
          throw Store.failException;
        }
      }
    }
  }

  /** The volume of the window of width w in dimension d and of the hull in the others. */
  private long capacity(int d, long w) {
    long cap = w;
    for (int i = 0; i < dims; i++) {
      if (i != d) {
        long len = hullHi[i] - hullLo[i];
        if (len <= 0) {
          return 0;
        }
        if (cap > Long.MAX_VALUE / len) {
          return Long.MAX_VALUE;
        }
        cap *= len;
      }
    }
    return cap;
  }

  @Override
  public String toString() {
    return "volume_check(" + objects.length + " objects, time " + useTime + ")";
  }

  /** It tells whether the group selects every spatial dimension and has two objects or more. */
  static boolean appliesTo(NonOverlapping no, int dimension) {
    boolean[] selected = new boolean[dimension + 1];
    for (int d : no.selectedDimensions) {
      if (d >= 0 && d <= dimension) {
        selected[d] = true;
      }
    }
    for (int d = 0; d < dimension; d++) {
      if (!selected[d]) {
        return false;
      }
    }
    return no.objects.length > 1;
  }

  /** It tells whether the group is non-overlapping in time too. */
  static boolean usesTime(NonOverlapping no, int dimension) {
    return Arrays.stream(no.selectedDimensions).anyMatch(d -> d == dimension);
  }
}
