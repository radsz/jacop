/*
 * DiffnKExplanation.java
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

package org.jacop.constraints.diffn;

import java.util.BitSet;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Reasons of the pruning and failures of {@link DiffnK} under lazy clause generation. The rules are
 * recomputed on the bounds just before the explained atom (or the failure), and a reason cites only
 * the boxes of the rule that implies it:
 *
 * <ul>
 *   <li>the pairwise rule: two boxes that must overlap in all dimensions but d are separated in d;
 *       the reason is the origins' bounds and the lengths' minimums of the two boxes;
 *   <li>the volume rule: a box and the boxes it may overlap, in index order, until their minimum
 *       volumes exceed their bounding box; the reason is their origins' and lengths' bounds;
 *   <li>non-strict only, the exclusion of a box that cannot be placed at its smallest positive
 *       lengths, by a present box it must overlap or by volume; its lengths are cited by all their
 *       atoms, since the smallest positive length reads the domain.
 * </ul>
 *
 * Anything else (the projection and slice layers, or a rule that this recomputation does not find)
 * is left to the generic reason.
 */
final class DiffnKExplanation {

  private final AtomicTrail trail;
  private final DiffnK c;
  private final Box[] box;
  private final int k;
  private final int position;
  private final long[][] oMin;
  private final long[][] oMax;
  private final long[][] lMin;
  private final long[][] lMax;

  private DiffnKExplanation(AtomicTrail trail, DiffnK c, int position) {
    this.trail = trail;
    this.c = c;
    this.box = c.box;
    this.k = c.k;
    this.position = position;
    int n = box.length;
    oMin = new long[n][k];
    oMax = new long[n][k];
    lMin = new long[n][k];
    lMax = new long[n][k];
    for (int i = 0; i < n; i++) {
      for (int d = 0; d < k; d++) {
        oMin[i][d] = trail.minBefore(box[i].origin[d], position);
        oMax[i][d] = trail.maxBefore(box[i].origin[d], position);
        lMin[i][d] = Math.max(0, trail.minBefore(box[i].length[d], position));
        lMax[i][d] = Math.max(0, trail.maxBefore(box[i].length[d], position));
      }
    }
  }

  /**
   * Adds the reason of an atom of a DiffnK constraint.
   *
   * @return false when no rule found here implies it
   */
  static boolean explain(AtomicTrail trail, DiffnK c, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    DiffnKExplanation e = null;
    int mark = out.size();
    for (int a = 0; a < c.box.length; a++) {
      Box b = c.box[a];
      boolean handle = !c.strict && c.handle != null && c.handle[a] == y;
      for (int d = 0; d < c.k; d++) {
        boolean origin = b.origin[d] == y;
        boolean length = b.length[d] == y;
        if (!origin && !length && !(handle && d == 0)) {
          continue;
        }
        if (e == null) {
          e = new DiffnKExplanation(trail, c, entry);
        }
        if ((origin || length) && e.pairwise(a, d, origin, entry, out)) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
        if (!c.strict && (length || handle) && e.exclusion(a, entry, out)) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  /**
   * Adds the reason of a failure of a DiffnK constraint.
   *
   * @return false when no rule found here fails
   */
  static boolean explainFailure(AtomicTrail trail, DiffnK c, EntryList out) {
    DiffnKExplanation e = new DiffnKExplanation(trail, c, trail.size());
    int mark = out.size();
    if (e.pairFailure(out) || e.volumeFailure(out)) {
      out.sortUnique(mark);
      return true;
    }
    out.truncate(mark);
    return false;
  }

  private boolean present(int i) {
    for (int d = 0; d < k; d++) {
      if (lMin[i][d] <= 0) {
        return false;
      }
    }
    return true;
  }

  private boolean takesPart(int i) {
    return c.strict || present(i);
  }

  private boolean apart(int a, int b) {
    for (int d = 0; d < k; d++) {
      if (oMax[a][d] + lMax[a][d] <= oMin[b][d] || oMax[b][d] + lMax[b][d] <= oMin[a][d]) {
        return true;
      }
      if (c.strict ? lMax[a][d] == 0 && lMax[b][d] == 0 : lMax[a][d] == 0 || lMax[b][d] == 0) {
        return true;
      }
    }
    return false;
  }

  private boolean mustOverlap(int a, long aLength, int b, long bLength, int d) {
    long aLst = oMax[a][d];
    long aEct = oMin[a][d] + aLength;
    long bLst = oMax[b][d];
    long bEct = oMin[b][d] + bLength;
    return (aLst < aEct || bLst < bEct) && bEct > aLst && aEct > bLst;
  }

  // the one dimension in which a and b may be apart, -1 if none (a failure), -2 if several
  private int free(int a, int b) {
    int free = -1;
    for (int d = 0; d < k; d++) {
      if (!mustOverlap(a, lMin[a][d], b, lMin[b][d], d)) {
        if (free >= 0) {
          return -2;
        }
        free = d;
      }
    }
    return free;
  }

  /**
   * The pruning of box a's origin (or length) in dimension d by the pairwise rule with some box b,
   * computed both ways (a with b and b with a, as the constraint runs them): whether it implies the
   * entry, and if so its reason.
   */
  private boolean pairwise(int a, int d, boolean origin, int entry, EntryList out) {
    if (!takesPart(a)) {
      return false;
    }
    for (int b = 0; b < box.length; b++) {
      if (b == a || !takesPart(b) || apart(a, b) || free(a, b) != d) {
        continue;
      }
      if (implied(a, b, d, origin, entry) || implied2(a, b, d, origin, entry)) {
        addPair(a, b, out);
        addSkipped(entry, out);
        return true;
      }
    }
    return false;
  }

  // separate(a, b, d) as the constraint computes it, seen from box a
  private boolean implied(int a, int b, int d, boolean origin, int entry) {
    long aLst = oMax[a][d];
    long aEct = oMin[a][d] + lMin[a][d];
    long bLst = oMax[b][d];
    long bEct = oMin[b][d] + lMin[b][d];
    if (aLst < bEct) {
      // a before b
      return origin
          ? impliesAtMost(entry, bLst - lMin[a][d])
          : impliesAtMost(entry, bLst - oMin[a][d]);
    } else if (bLst < aEct) {
      // b before a
      return origin && impliesAtLeast(entry, oMin[b][d] + lMin[b][d]);
    }
    return origin && bLst < bEct && impliesOut(entry, bLst - lMin[a][d] + 1, bEct - 1);
  }

  // separate(b, a, d) as the constraint computes it, seen from box a
  private boolean implied2(int a, int b, int d, boolean origin, int entry) {
    long aLst = oMax[a][d];
    long aEct = oMin[a][d] + lMin[a][d];
    long bLst = oMax[b][d];
    long bEct = oMin[b][d] + lMin[b][d];
    if (bLst < aEct) {
      // b before a
      return origin && impliesAtLeast(entry, oMin[b][d] + lMin[b][d]);
    } else if (aLst < bEct) {
      // a before b
      return origin
          ? impliesAtMost(entry, bLst - lMin[a][d])
          : impliesAtMost(entry, bLst - oMin[a][d]);
    }
    return origin && bLst < bEct && impliesOut(entry, bLst - lMin[a][d] + 1, bEct - 1);
  }

  // whether x <= bound, with the holes before the entry, implies the entry
  private boolean impliesAtMost(int entry, long bound) {
    return switch (trail.kind(entry)) {
      case AtomicTrail.LE -> bound <= trail.skippedBound(entry);
      case AtomicTrail.NE -> bound < trail.value(entry);
      default -> false;
    };
  }

  // whether x >= bound, with the holes before the entry, implies the entry
  private boolean impliesAtLeast(int entry, long bound) {
    return switch (trail.kind(entry)) {
      case AtomicTrail.GE -> bound >= trail.skippedBound(entry);
      case AtomicTrail.NE -> bound > trail.value(entry);
      default -> false;
    };
  }

  // whether x not in [from, to] implies the entry (only a != atom inside the interval)
  private boolean impliesOut(int entry, long from, long to) {
    return trail.kind(entry) == AtomicTrail.NE
        && from <= trail.value(entry)
        && trail.value(entry) <= to;
  }

  // the holes that a bound entry skipped past the computed bound, which the domain stepped over
  private void addSkipped(int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (kind != AtomicTrail.NE) {
      trail.addSkippedHoles(
          entry, kind == AtomicTrail.GE ? Integer.MIN_VALUE : Integer.MAX_VALUE, out);
    }
  }

  // the bounds the pairwise rule reads: origins and minimum lengths of both boxes
  private void addPair(int a, int b, EntryList out) {
    for (int i : new int[] {a, b}) {
      for (int d = 0; d < k; d++) {
        trail.addLowerBound(box[i].origin[d], position, out);
        trail.addUpperBound(box[i].origin[d], position, out);
        trail.addLowerBound(box[i].length[d], position, out);
      }
    }
  }

  // the bounds the volume rule reads
  private void addBox(int i, EntryList out) {
    for (int d = 0; d < k; d++) {
      trail.addLowerBound(box[i].origin[d], position, out);
      trail.addUpperBound(box[i].origin[d], position, out);
      trail.addLowerBound(box[i].length[d], position, out);
      trail.addUpperBound(box[i].length[d], position, out);
    }
  }

  // a pair of boxes that cannot be apart, or whose separation empties an origin or a length
  private boolean pairFailure(EntryList out) {
    int n = box.length;
    EntryList holes = new EntryList();
    for (int a = 0; a < n; a++) {
      if (!takesPart(a)) {
        continue;
      }
      for (int b = a + 1; b < n; b++) {
        if (!takesPart(b) || apart(a, b)) {
          continue;
        }
        int d = free(a, b);
        holes.clear();
        if (d == -1
            || d >= 0 && (separationEmpties(a, b, d, holes) || separationEmpties(b, a, d, holes))) {
          addPair(a, b, out);
          for (int i = 0; i < holes.size(); i++) {
            out.addFrom(holes, i);
          }
          return true;
        }
      }
    }
    return false;
  }

  // whether separate(a, b, d) on these bounds empties an origin or a length; holes gets the !=
  // atoms that the emptiness needs
  private boolean separationEmpties(int a, int b, int d, EntryList holes) {
    long aLst = oMax[a][d];
    long aEct = oMin[a][d] + lMin[a][d];
    long bLst = oMax[b][d];
    long bEct = oMin[b][d] + lMin[b][d];
    if (aLst < bEct) {
      return before(a, b, d, holes);
    } else if (bLst < aEct) {
      return before(b, a, d, holes);
    }
    return bLst < bEct
            && emptyOutside(box[a].origin[d], a, d, true, bLst - lMin[a][d] + 1, bEct - 1, holes)
        || aLst < aEct
            && emptyOutside(box[b].origin[d], b, d, true, aLst - lMin[b][d] + 1, aEct - 1, holes);
  }

  // whether a before b in d empties b's origin, a's origin or a's length
  private boolean before(int a, int b, int d, EntryList holes) {
    long aEst = oMin[a][d];
    long aMinLength = lMin[a][d];
    long bLst = oMax[b][d];
    // b's origin >= aEst + aMinLength, a's origin <= bLst - aMinLength, a's length <= bLst - aEst
    return emptyOutside(box[b].origin[d], b, d, true, Long.MIN_VALUE, aEst + aMinLength - 1, holes)
        || emptyOutside(box[a].origin[d], a, d, true, bLst - aMinLength + 1, Long.MAX_VALUE, holes)
        || emptyOutside(box[a].length[d], a, d, false, bLst - aEst + 1, Long.MAX_VALUE, holes);
  }

  /**
   * Whether removing [from, to] from x (box i's origin or length in d) leaves no value within its
   * bounds before the position; the != atoms of the values left are added to holes.
   */
  private boolean emptyOutside(
      IntVar x, int i, int d, boolean origin, long from, long to, EntryList holes) {
    long lo = origin ? oMin[i][d] : lMin[i][d];
    long hi = origin ? oMax[i][d] : lMax[i][d];
    if (from <= lo && hi <= to) {
      return true;
    }
    int mark = holes.size();
    long left = Math.min(hi, from - 1) - lo + 1;
    long right = hi - Math.max(lo, to + 1) + 1;
    if (Math.max(0, left) + Math.max(0, right) > 256) {
      return false;
    }
    for (long v = lo; v <= hi; v++) {
      if ((v < from || v > to) && !trail.excludedBefore(x, (int) v, position, holes)) {
        holes.truncate(mark);
        return false;
      }
    }
    return true;
  }

  // the volume rule: box b and the boxes it may overlap that take part
  private boolean volumeFailure(EntryList out) {
    int n = box.length;
    for (int b = 0; b < n; b++) {
      if (takesPart(b)
          && (volumeFails(b, c.candidates[b].value(), out) || volumeFails(b, null, out))) {
        return true;
      }
    }
    return false;
  }

  /**
   * The volume rule over box b and the boxes that take part among its candidates (the current ones
   * of the constraint at a failure, or else all boxes not apart from b), in index order: their
   * minimum volumes exceed their bounding box, or they are more than fit at their minimum lengths.
   */
  private boolean volumeFails(int b, BitSet candidates, EntryList out) {
    int n = box.length;
    long[] low = new long[k];
    long[] high = new long[k];
    long[] minLength = new long[k];
    for (int d = 0; d < k; d++) {
      low[d] = oMin[b][d];
      high[d] = oMax[b][d] + lMax[b][d];
      minLength[d] = lMin[b][d];
    }
    long volume = minVolume(b);
    int count = 1;
    int last = -1;
    for (int j = 0; j < n; j++) {
      if (j == b || !takesPart(j) || (candidates != null ? !candidates.get(j) : apart(b, j))) {
        continue;
      }
      for (int d = 0; d < k; d++) {
        low[d] = Math.min(low[d], oMin[j][d]);
        high[d] = Math.max(high[d], oMax[j][d] + lMax[j][d]);
        minLength[d] = Math.min(minLength[d], lMin[j][d]);
      }
      volume = DiffnK.add(volume, minVolume(j));
      count++;
      last = j;
      if (volume > space(low, high)) {
        addVolume(b, candidates, j, out);
        return true;
      }
    }
    long fit = 1;
    for (int d = 0; d < k && fit > 0; d++) {
      fit = minLength[d] > 0 ? DiffnK.multiply(fit, (high[d] - low[d]) / minLength[d]) : -1;
    }
    if (fit >= 0 && fit < count) {
      addVolume(b, candidates, last, out);
      return true;
    }
    return false;
  }

  private void addVolume(int b, BitSet candidates, int last, EntryList out) {
    addBox(b, out);
    for (int i = 0; i <= last; i++) {
      if (i != b && takesPart(i) && (candidates != null ? candidates.get(i) : !apart(b, i))) {
        addBox(i, out);
      }
    }
  }

  private long minVolume(int b) {
    long v = 1;
    for (int d = 0; d < k && v > 0; d++) {
      v = DiffnK.multiply(v, lMin[b][d]);
    }
    return v;
  }

  private long space(long[] low, long[] high) {
    long v = 1;
    for (int d = 0; d < k && v > 0; d++) {
      v = DiffnK.multiply(v, Math.max(0, high[d] - low[d]));
    }
    return v;
  }

  // the smallest positive value of box a's length in d before the position, or 0 if none
  private long minPositive(int a, int d) {
    if (lMin[a][d] > 0) {
      return lMin[a][d];
    }
    EntryList scratch = new EntryList();
    for (long v = 1; v <= lMax[a][d]; v++) {
      if (!trail.excludedBefore(box[a].length[d], (int) v, position, scratch)) {
        return v;
      }
    }
    return 0;
  }

  /**
   * Non-strict only: the entry sets a length or the presence handle of box a to 0 because box a, at
   * its smallest positive lengths, must overlap a present box or does not fit by volume with the
   * present boxes it may overlap.
   */
  private boolean exclusion(int a, int entry, EntryList out) {
    if (present(a) || !implies0(entry, a)) {
      return false;
    }
    long[] minLength = new long[k];
    for (int d = 0; d < k; d++) {
      minLength[d] = minPositive(a, d);
      if (minLength[d] == 0) {
        return false;
      }
    }
    long[] low = new long[k];
    long[] high = new long[k];
    long volume = 1;
    for (int d = 0; d < k; d++) {
      low[d] = oMin[a][d];
      high[d] = oMax[a][d] + lMax[a][d];
      volume = DiffnK.multiply(volume, minLength[d]);
    }
    int n = box.length;
    for (int j = 0; j < n; j++) {
      if (j == a || !present(j) || apart(a, j)) {
        continue;
      }
      boolean overlap = true;
      for (int d = 0; d < k && overlap; d++) {
        overlap = mustOverlap(a, minLength[d], j, lMin[j][d], d);
      }
      if (overlap) {
        addExcluded(a, out);
        addPair(j, j, out);
        return true;
      }
      for (int d = 0; d < k; d++) {
        low[d] = Math.min(low[d], oMin[j][d]);
        high[d] = Math.max(high[d], oMax[j][d] + lMax[j][d]);
      }
      volume = DiffnK.add(volume, minVolume(j));
      if (volume > space(low, high)) {
        addExcluded(a, out);
        for (int i = 0; i <= j; i++) {
          if (i != a && present(i) && !apart(a, i)) {
            addBox(i, out);
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the entry follows from box a being absent: the entry is on the presence handle, or on a
   * length of a whose other lengths are all positive, and it holds at 0.
   */
  private boolean implies0(int entry, int a) {
    IntVar y = trail.variable(entry);
    boolean handle = c.handle != null && c.handle[a] == y;
    for (int d = 0; d < k && !handle; d++) {
      if (box[a].length[d] != y && lMin[a][d] <= 0) {
        // another length may be the 0 one
        return false;
      }
    }
    int v = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.LE -> v >= 0;
      case AtomicTrail.GE -> v <= 0;
      default -> v != 0;
    };
  }

  // box a's origins by their bounds and its lengths by all their atoms
  private void addExcluded(int a, EntryList out) {
    for (int d = 0; d < k; d++) {
      trail.addLowerBound(box[a].origin[d], position, out);
      trail.addUpperBound(box[a].origin[d], position, out);
      trail.atomsBefore(box[a].length[d], position, out);
    }
  }
}
