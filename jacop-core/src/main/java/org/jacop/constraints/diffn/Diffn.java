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
  final Comparator<Event> eventComparator =
      (o1, o2) -> o1.date() == o2.date() ? o1.type() - o2.type() : o1.date() - o2.date();
  // for decomposed diffn
  protected List<Constraint> constraints;

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
    for (int k = 0; k < rectangle.length; k++) {
      Rectangle r = rectangle[k];
      BitSet o = overlapping[k].value();
      if (o.cardinality() == 0) {
        continue;
      }
      int commonArea = 0;
      for (int j = o.nextSetBit(0); j >= 0; j = o.nextSetBit(j + 1)) {
        Rectangle s = rectangle[j];
        int partialCommonArea =
            areaCheckPartialCommonForRectangle(r, s, 0)
                * areaCheckPartialCommonForRectangle(r, s, 1);
        commonArea += partialCommonArea;
      }
      if (commonArea + r.getLength(X).min() * r.getLength(Y).min()
          > (r.lct(X) - r.est(X)) * (r.lct(Y) - r.est(Y))) {
        throw Store.failException;
      }
    }
  }

  private int areaCheckPartialCommonForRectangle(Rectangle r, Rectangle s, int dim) {
    int rMin = r.est(dim);
    int rMax = r.lct(dim);
    int sLengthMin = s.getLength(dim).min();
    if (s.getOrigin(dim).min() <= rMin) {
      sLengthMin = areaCheckSOriginBeforeRMin(r, s, dim, rMin, rMax, sLengthMin);
    } else if (s.getOrigin(dim).max() + s.getLength(dim).min() > rMax) {
      sLengthMin = areaCheckSOriginAfterRMin(r, s, dim, rMax, sLengthMin);
    }
    return sLengthMin;
  }

  private int areaCheckSOriginBeforeRMin(
      Rectangle r, Rectangle s, int dim, int rMin, int rMax, int sLengthMin) {
    if (s.getOrigin(dim).max() + s.getLength(dim).min() <= rMax) {
      return Math.max(s.ect(dim) - rMin, 0);
    }
    int rmax = r.getOrigin(dim).max() + r.getLength(dim).min();
    int distance1 = Math.min(s.ect(dim) - rMin, rmax - rMin);
    int distance2 = Math.min(-s.getOrigin(dim).max() + rmax, rmax - rMin);
    if (distance1 < distance2) {
      return Math.max(distance1, 0);
    } else if (distance2 > 0) {
      return distance2 < s.getLength(dim).min() ? distance2 : s.getLength(dim).min();
    }
    return 0;
  }

  private int areaCheckSOriginAfterRMin(
      Rectangle r, Rectangle s, int dim, int rMax, int sLengthMin) {
    int distance2 = -s.getOrigin(dim).max() + r.origin[dim].max() + r.length[dim].min();
    if (distance2 > 0 && distance2 < s.getLength(dim).min()) {
      return distance2;
    } else if (distance2 <= 0) {
      return 0;
    }
    return sLengthMin;
  }

  private void profile() {

    for (int i = 0; i < rectangle.length; i++) {
      Rectangle r = rectangle[i];
      BitSet o = overlapping[i].value();

      if (o.cardinality() > 0) {
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
    Event[] es = buildSweepEvents(r, o, dim, oDim, limitOut);
    if (es == null) {
      return;
    }

    final int limit = limitOut[0];
    int n = es.length;
    Arrays.sort(es, 0, n, eventComparator);

    if (DEBUG_NARR) {
      log.debug("===========================");
      log.debug("Profile in dimension {}", dim);
      log.debug("{}", Arrays.asList(es));
      log.debug("limit = {}", limit);
      log.debug("===========================");
    }

    boolean[] inProfile = new boolean[rectangle.length];
    List<Interval> sweepLine = new ArrayList<>();
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

  /** Builds event array; returns null if no mandatory events. Sets limitOut[0] to limit. */
  private Event[] buildSweepEvents(Rectangle r, BitSet o, int dim, int oDim, int[] limitOut) {
    Event[] es = new Event[2 * o.cardinality() + 2];
    boolean mandatoryExists = false;
    int j = 0;
    int minLimit = r.est(oDim);
    int maxLimit = r.lct(oDim);
    for (int i = o.nextSetBit(0); i >= 0; i = o.nextSetBit(i + 1)) {
      Rectangle rr = rectangle[i];
      rr.index = i;
      int min = rr.lst(dim);
      int max = rr.ect(dim);
      int lMin = rr.getLength(oDim).min();
      if (min >= max || lMin <= 0) {
        continue;
      }
      int oMin = rr.lst(oDim);
      int oMax = rr.ect(oDim);
      boolean withinR = rr.est(oDim) >= r.est(oDim) && rr.lct(oDim) <= r.lct(oDim);
      int val = withinR ? lMin : 0;
      if (oMin < oMax) {
        Interval block = new Interval(oMin, oMax);
        es[j++] = new Event(PROFILE_ADD, rr, min, val, block);
        es[j++] = new Event(PROFILE_SUBTRACT, rr, max, -val, block);
      } else {
        es[j++] = new Event(PROFILE_ADD, rr, min, val, null);
        es[j++] = new Event(PROFILE_SUBTRACT, rr, max, -val, null);
      }
      minLimit = Math.min(rr.est(oDim), minLimit);
      maxLimit = Math.max(rr.lct(oDim), maxLimit);
      mandatoryExists = true;
    }
    if (!mandatoryExists) {
      return null;
    }
    limitOut[0] = maxLimit - minLimit;
    es[j++] = new Event(PRUNE_START, r, r.est(dim), 0, null);
    es[j++] = new Event(PRUNE_END, r, r.lct(dim), 0, null);
    return Arrays.copyOf(es, j);
  }

  private void processProfileAddSubtract(
      Event e,
      Event ne,
      Rectangle r,
      int oDim,
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
      profileValue -= r.getLength(oDim).min();
    }

    boolean blocking =
        blocking(
            sweepLine,
            r.getOrigin(oDim).min(),
            r.getOrigin(oDim).max() + r.getLength(oDim).min(),
            r.getLength(oDim).min());

    if (r.exists()) {
      if (startExcluded[0] == Integer.MAX_VALUE) {
        if (limit - profileValue < r.getLength(oDim).min() || blocking) {
          startExcluded[0] = e.date() - r.getLength(dim).min() + 1;
        }
      } else if (limit - profileValue >= r.getLength(oDim).min() && !blocking) {
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
        && (limit - profileValue < r.getLength(oDim).min() || blocking)) {
      lastBarier[0] = e.date();
    }

    if (r.lst(dim) <= e.date()
        && e.date() < r.ect(dim)
        && limit - profileValue < r.getLength(oDim).max()) {
      r.getLength(oDim).domain.inMax(store.level, r.getLength(oDim), limit - profileValue);
    }
  }

  private void processPruneStart(
      Event e,
      int oDim,
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
      profileValue -= rr.getLength(oDim).min();
    }
    if (rr.exists()
        && (limit - profileValue < rr.getLength(oDim).min()
            || blocking(
                sweepLine,
                rr.getOrigin(oDim).min(),
                rr.getOrigin(oDim).max() + rr.getLength(oDim).min(),
                rr.getLength(oDim).min()))) {
      startExcluded[0] = e.date();
    }
    if (rr.lst(dim) <= e.date()
        && e.date() < rr.ect(dim)
        && limit - profileValue < rr.getLength(oDim).max()) {
      rr.getLength(oDim).domain.inMax(store.level, rr.getLength(oDim), limit - profileValue);
    }
  }

  private void processPruneEnd(
      Event e,
      int oDim,
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
      profileValue -= rr.getLength(oDim).min();
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
        && limit - profileValue < rr.getLength(oDim).max()) {
      rr.getLength(oDim).domain.inMax(store.level, rr.getLength(oDim), limit - profileValue);
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

  private void addBlockToSweepLine(List<Interval> sweepLine, Interval eBlock) {
    Interval previous = new Interval(IntDomain.MIN_INT, IntDomain.MIN_INT);
    for (int i = 0; i < sweepLine.size(); i++) {
      Interval sweepLineElement = sweepLine.get(i);
      if ((eBlock.max() > sweepLineElement.min() && eBlock.max() <= sweepLineElement.max())
          || (eBlock.min() >= sweepLineElement.min() && eBlock.min() < sweepLineElement.max())) {
        throw Store.failException; // overlap
      }
      if (eBlock.max() <= sweepLineElement.min() && eBlock.min() >= previous.max()) {
        sweepLine.add(i, eBlock);
        return;
      }
      previous = sweepLineElement;
    }
    if (sweepLine.getLast().max() <= eBlock.min()) {
      sweepLine.add(eBlock);
    }
  }

  private void removeBlockFromSweepLine(List<Interval> sweepLine, Interval eBlock) {
    for (int i = 0; i < sweepLine.size(); i++) {
      Interval sweepLineElement = sweepLine.get(i);
      if (sweepLineElement.min() == eBlock.min() && sweepLineElement.max() == eBlock.max()) {
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
}
