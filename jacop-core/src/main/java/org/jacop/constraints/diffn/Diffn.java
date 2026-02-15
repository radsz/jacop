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

      if (o.cardinality() > 0) {

        // calculate area within rectangle r possible placement
        int commonArea = 0;
        for (int j = o.nextSetBit(0); j >= 0; j = o.nextSetBit(j + 1)) {
          int partialCommonArea = 1;
          Rectangle s = rectangle[j];

          for (int i = 0; i < 2; i++) {
            int r_min = r.est(i);
            int r_max = r.lct(i);
            int sLengthMin = s.getLength(i).min();

            if (s.getOrigin(i).min() <= r_min) {
              if (s.getOrigin(i).max() + s.getLength(i).min() <= r_max) {
                int distance1 = s.ect(i) - r_min;
                sLengthMin = Math.max(distance1, 0);
              } else {
                // s.getOrigin(i).max() + slength(i).min()> r_max)
                int rmax = r.getOrigin(i).max() + r.getLength(i).min();

                int distance1 = s.ect(i) - r_min;
                int distance2 = -s.getOrigin(i).max() + rmax;
                distance1 = Math.min(distance1, rmax - r_min);
                distance2 = Math.min(distance2, rmax - r_min);
                if (distance1 < distance2) {
                  sLengthMin = Math.max(distance1, 0);
                } else if (distance2 > 0) {
                  if (distance2 < s.getLength(i).min()) {
                    sLengthMin = distance2;
                  }
                } else {
                  sLengthMin = 0;
                }
              }
            } else // s.getOrigin(i).min() > r_min
            if (s.getOrigin(i).max() + s.getLength(i).min() > r_max) {
              int distance2 = -s.getOrigin(i).max() + r.origin[i].max() + r.length[i].min();
              if (distance2 > 0) {
                if (distance2 < s.getLength(i).min()) {
                  sLengthMin = distance2;
                }
              } else {
                sLengthMin = 0;
              }
            }
            partialCommonArea = partialCommonArea * sLengthMin;
          }
          commonArea += partialCommonArea;
        }
        if (commonArea + r.getLength(X).min() * r.getLength(Y).min()
            > (r.lct(X) - r.est(X)) * (r.lct(Y) - r.est(Y))) {
          throw Store.failException;
        }
      }
    }
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

    Event[] es = new Event[2 * o.cardinality() + 2];

    boolean mandatoryExists = false;
    int j = 0;
    int minLimit = r.est(oDim);
    int maxLimit = r.lct(oDim);
    for (int i = o.nextSetBit(0); i >= 0; i = o.nextSetBit(i + 1)) {
      Rectangle rr = rectangle[i];
      rr.index = i;

      // mandatory task parts to create profile
      int min = rr.lst(dim);
      int max = rr.ect(dim);
      int lMin = rr.getLength(oDim).min();
      if (min < max && lMin > 0) {
        if (rr.est(oDim) >= r.est(oDim) && rr.lct(oDim) <= r.lct(oDim)) {
          // for profile take only rectangles with their area laying within the considered rectangle
          int oMin = rr.lst(oDim);
          int oMax = rr.ect(oDim);
          if (oMin < oMax) {
            Interval block = new Interval(oMin, oMax);
            es[j++] = new Event(PROFILE_ADD, rr, min, lMin, block);
            es[j++] = new Event(PROFILE_SUBTRACT, rr, max, -lMin, block);
          } else {
            es[j++] = new Event(PROFILE_ADD, rr, min, lMin, null);
            es[j++] = new Event(PROFILE_SUBTRACT, rr, max, -lMin, null);
          }
          minLimit = Math.min(rr.est(oDim), minLimit);
          maxLimit = Math.max(rr.lct(oDim), maxLimit);
          mandatoryExists = true;
        } else {
          int oMin = rr.lst(oDim);
          int oMax = rr.ect(oDim);
          if (oMin < oMax) {
            Interval block = new Interval(oMin, oMax);
            es[j++] = new Event(PROFILE_ADD, rr, min, 0, block);
            es[j++] = new Event(PROFILE_SUBTRACT, rr, max, 0, block);
            mandatoryExists = true;
          }
        }
      }
    }
    if (!mandatoryExists) {
      return;
    }

    final int limit = maxLimit - minLimit;

    // overlapping rectangle for pruning
    // from start to end
    int min = r.est(dim);
    int max = r.lct(dim);
    es[j++] = new Event(PRUNE_START, r, min, 0, null);
    es[j++] = new Event(PRUNE_END, r, max, 0, null);

    int N = j;
    Arrays.sort(es, 0, N, eventComparator);

    if (DEBUG_NARR) {
      log.debug("===========================");
      log.debug("Profile in dimension {}", dim);
      log.debug("{}", Arrays.asList(es));
      log.debug("limit = {}", limit);
      log.debug("===========================");
    }

    boolean considerR = false;

    boolean[] inProfile = new boolean[rectangle.length];

    // current value of the profile for mandatory parts
    int curProfile = 0;
    // current value of the sweep line
    List<Interval> sweepLine = new ArrayList<>();

    // used for start variable pruning
    int startExcluded = Integer.MAX_VALUE;

    // used for duration variable pruning
    int lastBarier = Integer.MAX_VALUE;

    for (int i = 0; i < N; i++) {

      Event e = es[i];
      Event ne = null; // next event
      if (i < N - 1) {
        ne = es[i + 1];
      }

      switch (e.type()) {
        case PROFILE_SUBTRACT: // =========== PROFILE_SUBTRACT event ===========
        case PROFILE_ADD: // =========== PROFILE_ADD event ===========
          curProfile += e.value();
          inProfile[e.rect().index] = e.value() > 0;

          if (e.block() != null) {
            updateSweepLine(sweepLine, e);
          }

          if (ne == null
              || ne.type() > PROFILE_ADD
              || e.date < ne.date()) { // check the tasks for pruning only at the end of all profile
            // events

            if (DEBUG) {
              log.debug("Profile at {}: {}", e.date(), curProfile);
            }

            // fail if we go over limit limit variable
            if (curProfile > limit) {
              throw Store.failException;
            }

            if (considerR) {

              int ri = r.index;

              int profileValue = curProfile;
              if (inProfile[ri]) {
                profileValue -= r.getLength(oDim).min();
              }

              boolean blocking =
                  blocking(
                      sweepLine,
                      r.getOrigin(oDim).min(),
                      r.getOrigin(oDim).max() + r.getLength(oDim).min(),
                      r.getLength(oDim).min());

              // ========= Pruning start variable
              if (r.exists()) { // (r.getLength(oDim).min() > 0 && r.getLength(dim).min() > 0)
                if (startExcluded == Integer.MAX_VALUE) {
                  if (limit - profileValue < r.getLength(oDim).min() || blocking) {
                    startExcluded = e.date() - r.getLength(dim).min() + 1;
                  }
                } else // startExcluded != Integer.MAX_VALUE
                if (limit - profileValue >= r.getLength(oDim).min() && !blocking) {
                  // end of excluded interval

                  if (startExcluded <= r.lst(dim)) {

                    if (DEBUG_NARR) {
                      log.debug(
                          ">>> Diffn ({}) Profile 1. Narrowed {} \\ {}",
                          dim,
                          r.getOrigin(dim),
                          new IntervalDomain(startExcluded, e.date() - 1));
                    }

                    IntervalDomain update =
                        new IntervalDomain(IntDomain.MIN_INT, startExcluded - 1);
                    update.unionAdapt(e.date(), IntDomain.MAX_INT);
                    r.getOrigin(dim).domain.in(store.level, r.getOrigin(dim), update);

                    if (DEBUG_NARR) {
                      log.debug(DEBUG_ARROW, r.getOrigin(dim));
                    }
                  }
                  startExcluded = Integer.MAX_VALUE;
                }
              }

              // ========= for duration pruning
              if (lastBarier == Integer.MAX_VALUE
                  && e.date() >= r.lst(dim)
                  && (limit - profileValue < r.getLength(oDim).min() || blocking)) {
                lastBarier = e.date();
              }

              // ========= resource pruning
              if (r.lst(dim) <= e.date()
                  && e.date() < r.ect(dim)
                  && limit - profileValue < r.getLength(oDim).max()) {
                r.getLength(oDim)
                    .domain
                    .inMax(store.level, r.getLength(oDim), limit - profileValue);
              }
            }
          }

          break;

        case PRUNE_START: // =========== start of a task ===========
          int profileValue = curProfile;
          Rectangle rr = e.rect();
          int ri = rr.index;

          considerR = true;

          if (inProfile[ri]) {
            profileValue -= rr.getLength(oDim).min();
          }

          // ========= for start pruning
          if (rr.exists() // (rr.getLength(oDim).min() > 0 && rr.getLength(dim).min() > 0)
              && (limit - profileValue < rr.getLength(oDim).min()
                  || blocking(
                      sweepLine,
                      rr.getOrigin(oDim).min(),
                      rr.getOrigin(oDim).max() + rr.getLength(oDim).min(),
                      rr.getLength(oDim).min()))) {
            startExcluded = e.date();
          }

          // ========= resource pruning
          if (rr.lst(dim) <= e.date()
              && e.date() < rr.ect(dim)
              && limit - profileValue < rr.getLength(oDim).max()) {
            rr.getLength(oDim).domain.inMax(store.level, rr.getLength(oDim), limit - profileValue);
          }

          break;

        case PRUNE_END: // =========== end of a task ===========
          profileValue = curProfile;
          rr = e.rect();
          ri = rr.index;

          considerR = false;

          if (inProfile[ri]) {
            profileValue -= rr.getLength(oDim).min();
          }

          // ========= pruning start variable
          if (rr.exists()
              && startExcluded != Integer.MAX_VALUE
              && startExcluded - 1
                  <= rr.lst(dim)) { // (rr.getLength(oDim).min() > 0 && rr.getLength(dim).min() > 0)
            // task ends and we remove forbidden area
            if (DEBUG_NARR) {
              log.debug(
                  ">>> Diffn Profile 2. Narrowed {} \\ {}",
                  rr.getOrigin(dim),
                  new IntervalDomain(startExcluded, e.date()));
            }

            rr.getOrigin(dim).domain.inMax(store.level, rr.getOrigin(dim), startExcluded - 1);

            if (DEBUG_NARR) {
              log.debug(DEBUG_ARROW, rr.getOrigin(dim));
            }
          }

          startExcluded = Integer.MAX_VALUE;

          // ========= resource pruning
          if (rr.lst(dim) <= e.date()
              && e.date() < rr.ect(dim)
              && limit - profileValue < rr.getLength(oDim).max()) {
            rr.getLength(oDim).domain.inMax(store.level, rr.getLength(oDim), limit - profileValue);
          }

          // ========= duration pruning
          int maxDuration = IntDomain.subtractInt(lastBarier, rr.getOrigin(dim).min());

          if (maxDuration < rr.getLength(dim).max()) {
            if (DEBUG_NARR) {
              log.debug(
                  ">>> {}, lastBarier = {}, e.date() = {}",
                  rr.getOrigin(dim),
                  lastBarier,
                  e.date());
              log.debug(
                  ">>> Diffn Profile 3. Narrowed {} in -inf..{}", rr.getLength(dim), maxDuration);
            }

            rr.getLength(dim).domain.inMax(store.level, rr.getLength(dim), maxDuration);

            if (DEBUG_NARR) {
              log.debug(DEBUG_ARROW, rr.getLength(dim));
            }
          }

          break;
        default:
          throw new RuntimeException("Internal error in " + getClass().getName());
      }
    }
  }

  private void updateSweepLine(List<Interval> sweepLine, Event e) {

    Interval eBlock = e.block();

    if (sweepLine.isEmpty()) {
      sweepLine.add(eBlock);
      return;
    }

    if (e.type() == PROFILE_ADD) { // add
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

      // add at the end
      if (sweepLine.getLast().max() <= eBlock.min()) {
        sweepLine.add(eBlock);
      }
    } else { // e.type() == PROFILE_SUBTRACT; remove
      for (int i = 0; i < sweepLine.size(); i++) {
        Interval sweepLineElement = sweepLine.get(i);
        if (sweepLineElement.min() == eBlock.min() && sweepLineElement.max() == eBlock.max()) {
          sweepLine.remove(i);
          return;
        }
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
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }

  /** {@inheritDoc} */
  public List<Constraint> decompose(Store store) {
    constraints = new ArrayList<>();

    IntVar[] x = new IntVar[rectangle.length];
    IntVar[] y = new IntVar[rectangle.length];
    IntVar[] lx = new IntVar[rectangle.length];
    IntVar[] ly = new IntVar[rectangle.length];

    for (int i = 0; i < rectangle.length; i++) {
      assert rectangle[i] != null : i + "-th rectangle in the list is null";

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
