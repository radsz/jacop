/*
 * Diffn.java
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Comparator;
import java.util.List;
import lombok.Builder;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Max;
import org.jacop.constraints.Min;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Diffn constraint assures that any two rectangles from a vector of rectangles does not overlap in
 * at least one direction. It is a simple implementation which does not use sophisticated techniques
 * for efficient backtracking.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class Diffn extends Nooverlap {

  // event type
  static final int PROFILE_SUBTRACT = 0;
  static final int PROFILE_ADD = 1;
  static final int PRUNE_START = 2;
  static final int PRUNE_END = 3;
  private static final boolean DEBUG = false;

  private static final boolean DEBUG_NARR = false;
  private static final String DEBUG_ARROW = " => {}";
  protected final List<Var> auxVar = new ArrayList<>();
  // for decomposed diffn
  protected List<Constraint> constraints;

  // compulsory parts of the rectangles per dimension, see buildParts
  private final long[][] parts = new long[2][];
  private final int[] partCount = new int[2];
  private final long[] partsStamp = {-1, -1};
  private final Event[][] addWithin = new Event[2][];
  private final Event[][] subtractWithin = new Event[2][];
  private final Event[][] addOutside = new Event[2][];
  private final Event[][] subtractOutside = new Event[2][];
  private final int[][] partEst = new int[2][];
  private final int[][] partLct = new int[2][];
  private Event[] sweepEvents;
  private static final Comparator<Event> EVENT_ORDER =
      (o1, o2) -> o1.date() == o2.date() ? o1.type() - o2.type() : o1.date() - o2.date();
  private boolean[] inProfile;
  private final List<Interval> sweepLine = new ArrayList<>();

  /**
   * It specifies a diff constraint.
   *
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   */
  public Diffn(IntVar[][] rectangles) {
    super(rectangles);
  }

  /**
   * It specifies a diff constraint.
   *
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   * @param strict true- zero size rectangles need to be between other rectangles; false- these
   *     rectangles can be anywhere
   */
  public Diffn(IntVar[][] rectangles, boolean strict) {
    super(rectangles, strict);
  }

  /**
   * It constructs a diff constraint.
   *
   * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
   * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
   * @param length1 list of variables denoting length of the rectangle in the first dimension.
   * @param length2 list of variables denoting length of the rectangle in the second dimension.
   */
  public Diffn(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {
    super(origin1, origin2, length1, length2);
  }

  /**
   * It constructs a diff constraint.
   *
   * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
   * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
   * @param length1 list of variables denoting length of the rectangle in the first dimension.
   * @param length2 list of variables denoting length of the rectangle in the second dimension.
   * @param strict true- zero size rectangles need to be between other rectangles; false- these
   *     rectangles can be anywhere
   */
  @Builder
  public Diffn(
      IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2, boolean strict) {
    super(origin1, origin2, length1, length2, strict);
  }

  /**
   * It specifies a diffn constraint.
   *
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   */
  public Diffn(List<? extends List<? extends IntVar>> rectangles) {
    super(rectangles);
  }

  /**
   * It specifies a diffn constraint.
   *
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   * @param strict true- zero size rectangles need to be between other rectangles; false- these
   *     rectangles can be anywhere
   */
  public Diffn(List<? extends List<? extends IntVar>> rectangles, boolean strict) {
    super(rectangles, strict);
  }

  /**
   * It constructs a diff constraint.
   *
   * @param o1 list of variables denoting origin of the rectangle in the first dimension.
   * @param o2 list of variables denoting origin of the rectangle in the second dimension.
   * @param l1 list of variables denoting length of the rectangle in the first dimension.
   * @param l2 list of variables denoting length of the rectangle in the second dimension.
   */
  public Diffn(
      List<? extends IntVar> o1,
      List<? extends IntVar> o2,
      List<? extends IntVar> l1,
      List<? extends IntVar> l2) {
    super(o1, o2, l1, l2);
  }

  /**
   * It constructs a diff constraint.
   *
   * @param o1 list of variables denoting origin of the rectangle in the first dimension.
   * @param o2 list of variables denoting origin of the rectangle in the second dimension.
   * @param l1 list of variables denoting length of the rectangle in the first dimension.
   * @param l2 list of variables denoting length of the rectangle in the second dimension.
   * @param strict true- zero size rectangles need to be between other rectangles; false- these
   *     rectangles can be anywhere
   */
  public Diffn(
      List<? extends IntVar> o1,
      List<? extends IntVar> o2,
      List<? extends IntVar> l1,
      List<? extends IntVar> l2,
      boolean strict) {
    super(o1, o2, l1, l2, strict);
  }

  /** {@inheritDoc} */
  @Override
  public void consistency(Store store) {

    this.store = store;

    store.propagationHasOccurred = false;

    pruning();

    profile();

    if (store.propagationHasOccurred) {
      store.addChanged(this);
    } else if (doAreaCheck) {
      areaCheck();
    }
  }

  private void areaCheck() {
    startPass(AREA_PASS);
    int n = rectangle.length;
    boolean read = false;
    for (int k = 0; k < n; k++) {
      BitSet o = overlapping[k].value();
      if (o.isEmpty() || !mustExamine(AREA_PASS, k, o)) {
        continue;
      }
      if (!read) {
        // the area check prunes nothing, so each rectangle's bounds are read once
        invalidateBounds();
        syncBounds();
        read = true;
      }
      bounds(k);
      int commonArea = 0;
      for (int j = o.nextSetBit(0); j >= 0; j = o.nextSetBit(j + 1)) {
        bounds(j);
        int partialCommonArea = partialCommonArea(k, j, 0) * partialCommonArea(k, j, 1);
        commonArea += partialCommonArea;
      }
      if (commonArea + lMin[X][k] * lMin[Y][k]
          > (lst[X][k] + lMax[X][k] - est[X][k]) * (lst[Y][k] + lMax[Y][k] - est[Y][k])) {
        throw Store.failException;
      }
    }
  }

  // the part of rectangle s that must lie within the extent of rectangle r in dimension d
  private int partialCommonArea(int r, int s, int d) {
    int rMin = est[d][r];
    int rMax = lst[d][r] + lMax[d][r];
    int sEst = est[d][s];
    int sLst = lst[d][s];
    int sLengthMin = lMin[d][s];
    if (sEst <= rMin) {
      if (sLst + sLengthMin <= rMax) {
        return Math.max(sEst + sLengthMin - rMin, 0);
      }
      int rmax = lst[d][r] + lMin[d][r];
      int distance1 = Math.min(sEst + sLengthMin - rMin, rmax - rMin);
      int distance2 = Math.min(-sLst + rmax, rmax - rMin);
      if (distance1 < distance2) {
        return Math.max(distance1, 0);
      } else if (distance2 > 0) {
        return distance2 < sLengthMin ? distance2 : sLengthMin;
      }
      return 0;
    } else if (sLst + sLengthMin > rMax) {
      int distance2 = -sLst + lst[d][r] + lMin[d][r];
      if (distance2 > 0 && distance2 < sLengthMin) {
        return distance2;
      } else if (distance2 <= 0) {
        return 0;
      }
    }
    return sLengthMin;
  }

  private void profile() {

    startPass(PROFILE_PASS);
    partsStamp[0] = -1;
    partsStamp[1] = -1;
    for (int i = 0; i < rectangle.length; i++) {
      Rectangle r = rectangle[i];
      BitSet o = overlapping[i].value();

      if (!o.isEmpty() && mustExamine(PROFILE_PASS, i, o)) {
        sweepPruning(r, o, 0);
        sweepPruning(r, o, 1);
      }
    }
  }

  private void sweepPruning(Rectangle r, BitSet o, int dim) {

    int oDim = dim == 0 ? 1 : 0;
    if (r.getLength(dim).max() == 0 || r.getLength(oDim).max() == 0) {
      return;
    }

    int[] limitOut = new int[1];
    int n = buildSweepEvents(r, o, dim, oDim, limitOut);
    if (n == 0) {
      return;
    }

    final int limit = limitOut[0];
    Event[] es = sweepEvents;

    if (DEBUG_NARR) {
      log.debug("===========================");
      log.debug("Profile in dimension {}", dim);
      log.debug("{}", Arrays.asList(es).subList(0, n));
      log.debug("limit = {}", limit);
      log.debug("===========================");
    }

    boolean[] inProfile = this.inProfile;
    Arrays.fill(inProfile, false);
    List<Interval> sweepLine = this.sweepLine;
    sweepLine.clear();
    int[] curProfile = new int[] {0};
    int[] startExcluded = new int[] {Integer.MAX_VALUE};
    int[] lastBarier = new int[] {Integer.MAX_VALUE};
    boolean[] considerR = new boolean[] {false};

    for (int i = 0; i < n; i++) {
      Event e = es[i];
      Event ne = (i < n - 1) ? es[i + 1] : null;

      switch (e.type()) {
        case PROFILE_SUBTRACT:
        case PROFILE_ADD:
          processProfileAddSubtract(
              e,
              ne,
              r,
              oDim,
              dim,
              limit,
              inProfile,
              sweepLine,
              curProfile,
              startExcluded,
              lastBarier,
              considerR[0]);
          break;
        case PRUNE_START:
          processPruneStart(e, oDim, dim, limit, inProfile, sweepLine, startExcluded, curProfile);
          considerR[0] = true;
          break;
        case PRUNE_END:
          processPruneEnd(e, oDim, dim, limit, inProfile, startExcluded, lastBarier, curProfile);
          startExcluded[0] = Integer.MAX_VALUE;
          considerR[0] = false;
          break;
        default:
          throw new RuntimeException("Internal error in " + getClass().getName());
      }
    }
  }

  /**
   * Collects the compulsory parts of all rectangles in dimension dim, sorted by date, then type,
   * then rectangle. It is done once per profile pass and dimension, and again only when a domain
   * changed since, so each rectangle's sweep only filters this list instead of sorting its own.
   */
  private void buildParts(int dim, int otherDim) {
    int n = rectangle.length;
    if (parts[dim] == null) {
      parts[dim] = new long[2 * n];
      addWithin[dim] = new Event[n];
      subtractWithin[dim] = new Event[n];
      addOutside[dim] = new Event[n];
      subtractOutside[dim] = new Event[n];
      partEst[dim] = new int[n];
      partLct[dim] = new int[n];
    }
    long[] keys = parts[dim];
    int m = 0;
    for (int i = 0; i < n; i++) {
      Rectangle rr = rectangle[i];
      int min = rr.lst(dim);
      int max = rr.ect(dim);
      int lMin = rr.getLength(otherDim).min();
      if (min >= max || lMin <= 0) {
        continue;
      }
      int oMin = rr.lst(otherDim);
      int oMax = rr.ect(otherDim);
      Interval block = oMin < oMax ? new Interval(oMin, oMax) : null;
      addWithin[dim][i] = new Event(PROFILE_ADD, rr, min, lMin, block);
      subtractWithin[dim][i] = new Event(PROFILE_SUBTRACT, rr, max, -lMin, block);
      // a rectangle reaching outside the swept one adds no height, only its compulsory part as a
      // block
      addOutside[dim][i] = block == null ? null : new Event(PROFILE_ADD, rr, min, 0, block);
      subtractOutside[dim][i] =
          block == null ? null : new Event(PROFILE_SUBTRACT, rr, max, 0, block);
      partEst[dim][i] = rr.est(otherDim);
      partLct[dim][i] = rr.lct(otherDim);
      keys[m++] = partKey(min, PROFILE_ADD, i);
      keys[m++] = partKey(max, PROFILE_SUBTRACT, i);
    }
    Arrays.sort(keys, 0, m);
    partCount[dim] = m;
    partsStamp[dim] = store.domainChanges();
  }

  /** buildSweepEvents from the rectangles that r may overlap only. */
  private int buildSweepEventsOf(Rectangle r, BitSet o, int dim, int otherDim, int[] limitOut) {
    Event[] es = sweepEvents;
    boolean mandatoryExists = false;
    int j = 0;
    int minLimit = r.est(otherDim);
    int maxLimit = r.lct(otherDim);
    for (int i = o.nextSetBit(0); i >= 0; i = o.nextSetBit(i + 1)) {
      Rectangle rr = rectangle[i];
      int min = rr.lst(dim);
      int max = rr.ect(dim);
      int lMin = rr.getLength(otherDim).min();
      if (min >= max || lMin <= 0) {
        continue;
      }
      int oMin = rr.lst(otherDim);
      int oMax = rr.ect(otherDim);
      boolean withinR = rr.est(otherDim) >= r.est(otherDim) && rr.lct(otherDim) <= r.lct(otherDim);
      if (withinR) {
        Interval block = oMin < oMax ? new Interval(oMin, oMax) : null;
        es[j++] = new Event(PROFILE_ADD, rr, min, lMin, block);
        es[j++] = new Event(PROFILE_SUBTRACT, rr, max, -lMin, block);
        // only rectangles within r in the other dimension widen the limit of the profile
        minLimit = Math.min(rr.est(otherDim), minLimit);
        maxLimit = Math.max(rr.lct(otherDim), maxLimit);
        mandatoryExists = true;
      } else if (oMin < oMax) {
        // a rectangle reaching outside r adds no height, only its compulsory part as a block
        Interval block = new Interval(oMin, oMax);
        es[j++] = new Event(PROFILE_ADD, rr, min, 0, block);
        es[j++] = new Event(PROFILE_SUBTRACT, rr, max, 0, block);
        mandatoryExists = true;
      }
    }
    if (!mandatoryExists) {
      return 0;
    }
    limitOut[0] = maxLimit - minLimit;
    es[j++] = new Event(PRUNE_START, r, r.est(dim), 0, null);
    es[j++] = new Event(PRUNE_END, r, r.lct(dim), 0, null);
    Arrays.sort(es, 0, j, EVENT_ORDER);
    return j;
  }

  // orders by date, then type, then rectangle index, as the stable sort of the events did
  private static long partKey(int date, int type, int index) {
    return ((long) date << 32) | ((long) type << 31) | index;
  }

  /**
   * Fills sweepEvents with the events of the sweep of r in dimension dim, sorted, and returns their
   * number, or 0 if no rectangle that r may overlap has a compulsory part. Sets limitOut[0] to the
   * limit.
   */
  private int buildSweepEvents(Rectangle r, BitSet o, int dim, int otherDim, int[] limitOut) {
    if (sweepEvents == null) {
      sweepEvents = new Event[2 * rectangle.length + 2];
      inProfile = new boolean[rectangle.length];
    }
    if (8 * o.cardinality() < rectangle.length) {
      // few rectangles may overlap r: sorting their events is cheaper than filtering all
      return buildSweepEventsOf(r, o, dim, otherDim, limitOut);
    }
    if (partsStamp[dim] != store.domainChanges()) {
      buildParts(dim, otherDim);
    }
    long[] keys = parts[dim];
    int m = partCount[dim];
    Event[] es = sweepEvents;
    int rEst = r.est(otherDim);
    int rLct = r.lct(otherDim);
    int minLimit = rEst;
    int maxLimit = rLct;
    int startDate = r.est(dim);
    int endDate = r.lct(dim);
    boolean startPlaced = false;
    boolean endPlaced = false;
    boolean mandatoryExists = false;
    int j = 0;
    for (int t = 0; t < m; t++) {
      long key = keys[t];
      int i = (int) (key & Integer.MAX_VALUE);
      if (!o.get(i)) {
        continue;
      }
      boolean add = (key & (1L << 31)) != 0;
      Event e;
      if (partEst[dim][i] >= rEst && partLct[dim][i] <= rLct) {
        e = add ? addWithin[dim][i] : subtractWithin[dim][i];
        // only rectangles within r in the other dimension widen the limit of the profile
        minLimit = Math.min(partEst[dim][i], minLimit);
        maxLimit = Math.max(partLct[dim][i], maxLimit);
      } else {
        e = add ? addOutside[dim][i] : subtractOutside[dim][i];
        if (e == null) {
          continue;
        }
      }
      mandatoryExists = true;
      // the prune events come after the profile events of the same date
      int date = (int) (key >> 32);
      if (!startPlaced && startDate < date) {
        es[j++] = new Event(PRUNE_START, r, startDate, 0, null);
        startPlaced = true;
      }
      if (!endPlaced && endDate < date) {
        es[j++] = new Event(PRUNE_END, r, endDate, 0, null);
        endPlaced = true;
      }
      es[j++] = e;
    }
    if (!mandatoryExists) {
      return 0;
    }
    if (!startPlaced) {
      es[j++] = new Event(PRUNE_START, r, startDate, 0, null);
    }
    if (!endPlaced) {
      es[j++] = new Event(PRUNE_END, r, endDate, 0, null);
    }
    limitOut[0] = maxLimit - minLimit;
    return j;
  }

  private void processProfileAddSubtract(
      Event e,
      Event ne,
      Rectangle r,
      int otherDim,
      int dim,
      int limit,
      boolean[] inProfile,
      List<Interval> sweepLine,
      int[] curProfile,
      int[] startExcluded,
      int[] lastBarier,
      boolean considerR) {
    curProfile[0] += e.value();
    inProfile[e.rect().index] = e.value() > 0;

    if (e.block() != null) {
      updateSweepLine(sweepLine, e);
    }

    boolean atPrunePoint = ne == null || ne.type() > PROFILE_ADD || e.date() < ne.date();
    if (!atPrunePoint) {
      return;
    }

    if (DEBUG) {
      log.debug("Profile at {}: {}", e.date(), curProfile[0]);
    }
    if (curProfile[0] > limit) {
      throw Store.failException;
    }

    if (!considerR) {
      return;
    }

    int ri = r.index;
    int profileValue = curProfile[0];
    if (inProfile[ri]) {
      profileValue -= r.getLength(otherDim).min();
    }

    boolean blocking =
        blocking(
            sweepLine,
            r.getOrigin(otherDim).min(),
            r.getOrigin(otherDim).max() + r.getLength(otherDim).min(),
            r.getLength(otherDim).min());

    if (r.exists()) {
      if (startExcluded[0] == Integer.MAX_VALUE) {
        if (limit - profileValue < r.getLength(otherDim).min() || blocking) {
          startExcluded[0] = e.date() - r.getLength(dim).min() + 1;
        }
      } else if (limit - profileValue >= r.getLength(otherDim).min() && !blocking) {
        if (startExcluded[0] <= r.lst(dim)) {
          if (DEBUG_NARR) {
            log.debug(
                ">>> Diffn ({}) Profile 1. Narrowed {} \\ {}",
                dim,
                r.getOrigin(dim),
                new IntervalDomain(startExcluded[0], e.date() - 1));
          }
          IntervalDomain update = new IntervalDomain(IntDomain.MIN_INT, startExcluded[0] - 1);
          update.unionAdapt(e.date(), IntDomain.MAX_INT);
          r.getOrigin(dim).domain.in(store.level, r.getOrigin(dim), update);
          if (DEBUG_NARR) {
            log.debug(DEBUG_ARROW, r.getOrigin(dim));
          }
        }
        startExcluded[0] = Integer.MAX_VALUE;
      }
    }

    if (lastBarier[0] == Integer.MAX_VALUE
        && e.date() >= r.lst(dim)
        && (limit - profileValue < r.getLength(otherDim).min() || blocking)) {
      lastBarier[0] = e.date();
    }

    if (r.lst(dim) <= e.date()
        && e.date() < r.ect(dim)
        && limit - profileValue < r.getLength(otherDim).max()) {
      r.getLength(otherDim).domain.inMax(store.level, r.getLength(otherDim), limit - profileValue);
    }
  }

  private void processPruneStart(
      Event e,
      int otherDim,
      int dim,
      int limit,
      boolean[] inProfile,
      List<Interval> sweepLine,
      int[] startExcluded,
      int[] curProfile) {
    Rectangle rr = e.rect();
    int ri = rr.index;
    int profileValue = curProfile[0];
    if (inProfile[ri]) {
      profileValue -= rr.getLength(otherDim).min();
    }
    if (rr.exists()
        && (limit - profileValue < rr.getLength(otherDim).min()
            || blocking(
                sweepLine,
                rr.getOrigin(otherDim).min(),
                rr.getOrigin(otherDim).max() + rr.getLength(otherDim).min(),
                rr.getLength(otherDim).min()))) {
      startExcluded[0] = e.date();
    }
    if (rr.lst(dim) <= e.date()
        && e.date() < rr.ect(dim)
        && limit - profileValue < rr.getLength(otherDim).max()) {
      rr.getLength(otherDim)
          .domain
          .inMax(store.level, rr.getLength(otherDim), limit - profileValue);
    }
  }

  private void processPruneEnd(
      Event e,
      int otherDim,
      int dim,
      int limit,
      boolean[] inProfile,
      int[] startExcluded,
      int[] lastBarier,
      int[] curProfile) {
    Rectangle rr = e.rect();
    int ri = rr.index;
    int profileValue = curProfile[0];
    if (inProfile[ri]) {
      profileValue -= rr.getLength(otherDim).min();
    }
    if (rr.exists()
        && startExcluded[0] != Integer.MAX_VALUE
        && startExcluded[0] - 1 <= rr.lst(dim)) {
      if (DEBUG_NARR) {
        log.debug(
            ">>> Diffn Profile 2. Narrowed {} \\ {}",
            rr.getOrigin(dim),
            new IntervalDomain(startExcluded[0], e.date()));
      }
      rr.getOrigin(dim).domain.inMax(store.level, rr.getOrigin(dim), startExcluded[0] - 1);
      if (DEBUG_NARR) {
        log.debug(DEBUG_ARROW, rr.getOrigin(dim));
      }
    }
    if (rr.lst(dim) <= e.date()
        && e.date() < rr.ect(dim)
        && limit - profileValue < rr.getLength(otherDim).max()) {
      rr.getLength(otherDim)
          .domain
          .inMax(store.level, rr.getLength(otherDim), limit - profileValue);
    }
    int maxDuration = IntDomain.subtractInt(lastBarier[0], rr.getOrigin(dim).min());
    if (maxDuration < rr.getLength(dim).max()) {
      if (DEBUG_NARR) {
        log.debug(
            ">>> {}, lastBarier = {}, e.date() = {}", rr.getOrigin(dim), lastBarier[0], e.date());
        log.debug(">>> Diffn Profile 3. Narrowed {} in -inf..{}", rr.getLength(dim), maxDuration);
      }
      rr.getLength(dim).domain.inMax(store.level, rr.getLength(dim), maxDuration);
      if (DEBUG_NARR) {
        log.debug(DEBUG_ARROW, rr.getLength(dim));
      }
    }
  }

  private void updateSweepLine(List<Interval> sweepLine, Event e) {
    Interval eBlock = e.block();
    if (sweepLine.isEmpty()) {
      sweepLine.add(eBlock);
      return;
    }
    if (e.type() == PROFILE_ADD) {
      addBlockToSweepLine(sweepLine, eBlock);
    } else {
      removeBlockFromSweepLine(sweepLine, eBlock);
    }
  }

  private void addBlockToSweepLine(List<Interval> sweepLine, Interval eventBlock) {
    Interval previous = new Interval(IntDomain.MIN_INT, IntDomain.MIN_INT);
    for (int i = 0; i < sweepLine.size(); i++) {
      Interval sweepLineElement = sweepLine.get(i);
      if ((eventBlock.max() > sweepLineElement.min() && eventBlock.max() <= sweepLineElement.max())
          || (eventBlock.min() >= sweepLineElement.min()
              && eventBlock.min() < sweepLineElement.max())) {
        throw Store.failException; // overlap
      }
      if (eventBlock.max() <= sweepLineElement.min() && eventBlock.min() >= previous.max()) {
        sweepLine.add(i, eventBlock);
        return;
      }
      previous = sweepLineElement;
    }
    if (sweepLine.getLast().max() <= eventBlock.min()) {
      sweepLine.add(eventBlock);
    }
  }

  private void removeBlockFromSweepLine(List<Interval> sweepLine, Interval eventBlock) {
    for (int i = 0; i < sweepLine.size(); i++) {
      Interval sweepLineElement = sweepLine.get(i);
      if (sweepLineElement.min() == eventBlock.min()
          && sweepLineElement.max() == eventBlock.max()) {
        sweepLine.remove(i);
        return;
      }
    }
  }

  private boolean blocking(List<Interval> sweepLine, int start, int end, int length) {

    if (sweepLine.isEmpty()) {
      return false;
    }

    int s = start;
    for (Interval sweepLineElement : sweepLine) {

      if (sweepLineElement.min() <= s) {
        s = Math.min(sweepLineElement.max(), end);
        continue;
      }
      if (sweepLineElement.min() - s >= length) {
        return false;
      }
      if (sweepLineElement.max() >= end) {
        return true;
      }
      s = Math.min(sweepLineElement.max(), end);
    }
    return end - s < length;
  }

  /**
   * It imposes DiffnDecomposed in a given store.
   *
   * @param store the constraint store to which the constraint is imposed to.
   */
  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }

  /** {@inheritDoc} */
  @Override
  public List<Constraint> decompose(Store store) {
    constraints = new ArrayList<>();

    IntVar[] x = new IntVar[rectangle.length];
    IntVar[] y = new IntVar[rectangle.length];
    IntVar[] lx = new IntVar[rectangle.length];
    IntVar[] ly = new IntVar[rectangle.length];

    for (int i = 0; i < rectangle.length; i++) {
      if (ASSERTS_ENABLED && rectangle[i] == null) {
        throw new IllegalStateException(String.valueOf(i + "-th rectangle in the list is null"));
      }

      x[i] = rectangle[i].getOrigin(0);
      y[i] = rectangle[i].getOrigin(1);
      lx[i] = rectangle[i].getLength(0);
      ly[i] = rectangle[i].getLength(1);
    }

    constraints.add(new Nooverlap(x, y, lx, ly, strict));

    // add cumulative in x direction
    IntVar[] ey = new IntVar[y.length];
    int yMin = IntDomain.MAX_INT;
    int yMax = IntDomain.MIN_INT;
    for (int i = 0; i < x.length; i++) {
      yMin = Math.min(yMin, y[i].min());
      yMax = Math.max(yMax, y[i].max() + ly[i].max());
      ey[i] = new IntVar(store, y[i].min() + ly[i].min(), y[i].max() + ly[i].max());
      constraints.add(new XplusYeqZ(y[i], ly[i], ey[i]));
      auxVar.add(ey[i]);
    }

    IntVar byMin = new IntVar(store, yMin, yMax);
    IntVar byMax = new IntVar(store, yMin, yMax);
    IntVar by = new IntVar(store, 0, yMax - yMin);
    auxVar.add(byMin);
    auxVar.add(byMax);
    auxVar.add(by);
    constraints.add(new Max(ey, byMax));
    constraints.add(new Min(y, byMin));
    constraints.add(new XplusYeqZ(byMin, by, byMax));
    CumulativeBasic ccx = new CumulativeBasic(x, lx, ly, by);
    constraints.add(ccx);

    // add cumulative in y direction
    IntVar[] ex = new IntVar[x.length];
    int xMin = IntDomain.MAX_INT;
    int xMax = IntDomain.MIN_INT;
    for (int i = 0; i < x.length; i++) {
      xMin = Math.min(xMin, x[i].min());
      xMax = Math.max(xMax, x[i].max() + lx[i].max());
      ex[i] = new IntVar(store, x[i].min() + lx[i].min(), x[i].max() + lx[i].max());
      constraints.add(new XplusYeqZ(x[i], lx[i], ex[i]));
      auxVar.add(ex[i]);
    }

    IntVar bxMin = new IntVar(store, "bxMin", xMin, xMax);
    IntVar bxMax = new IntVar(store, "bxMax", xMin, xMax);
    IntVar bx = new IntVar(store, 0, xMax - xMin);
    auxVar.add(bxMin);
    auxVar.add(bxMax);
    auxVar.add(bx);
    constraints.add(new Max(ex, bxMax));
    constraints.add(new Min(x, bxMin));
    constraints.add(new XplusYeqZ(bxMin, bx, bxMax));
    CumulativeBasic ccy = new CumulativeBasic(y, ly, lx, bx);
    constraints.add(ccy);

    return constraints;
  }

  /** {@inheritDoc} */
  @Override
  public List<Var> auxiliaryVariables() {
    return auxVar;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : diffn([");

    int i = 0;
    for (Rectangle r : rectangle) {
      result.append(r);
      if (i < rectangle.length - 1) {
        result.append(", ");
      }
      i++;
    }
    return result.append("], ").append(strict).append(")").toString();
  }

  private record Event(int type, Rectangle r, int date, int value, Interval block) {

    Rectangle rect() {
      return r;
    }

    @Override
    public String toString() {
      String result = "(";
      switch (type) {
        case PROFILE_SUBTRACT:
          result += "PROFILE_SUBTRACT, ";
          break;
        case PROFILE_ADD:
          result += "PROFILE_ADD, ";
          break;
        case PRUNE_START:
          result += "PRUNE_START, ";
          break;
        case PRUNE_END:
          result += "PRUNE_END, ";
          break;
        default:
          result += "--";
      }
      result += r + ", " + date + ", " + value + ", " + block + ")\n";
      return result;
    }
  }

  @Override
  public Diffn copy(VarMap map) {
    return new Diffn(rectangleVariables(map), strict);
  }
}
