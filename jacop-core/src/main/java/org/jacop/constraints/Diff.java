/*
 * Diff.java
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import lombok.Builder;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Diff constraint assures that any two rectangles from a vector of rectangles does not overlap in
 * at least one direction. It is a simple implementation which does not use sophisticated techniques
 * for efficient backtracking.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Diff extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

  protected static final boolean TRACE = false;
  protected static boolean trace = TRACE;
  static final AtomicInteger idNumber = new AtomicInteger(0);
  private static final boolean TRACE_NARR = false;
  private static boolean traceNarr = TRACE_NARR;
  protected final Function<Integer, Comparator<IntRectangle>> dimIthMinComparator =
      dim ->
          (IntRectangle o1, IntRectangle o2) -> {
            int v1 = o1.origin[dim];
            int v2 = o2.origin[dim];
            return v1 - v2;
          };

  /** It specifies the list of rectangles which are of interest for this diff constraint. */
  public Rectangle[] rectangles;

  Store currentStore;
  int stamp;
  Set<IntVar> variableQueue = new HashSet<>();

  /** It specifies if the constraint should compute and use the profile. */
  boolean doProfile = true;

  private int minPosition;
  // use to collect information on possible length of rectangles for pruning
  private List<Integer> durMax;

  /** It constructs an empty Diff constraint. */
  protected Diff() {}

  /**
   * It specifies a diff constraint.
   *
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   * @param doProfile should the constraint compute and use the profile functionality.
   */
  public Diff(Rectangle[] rectangles, boolean doProfile) {

    checkInputForNullness("rectangles", rectangles);
    checkInput(rectangles, r -> r.dim == 2, "rectangle has to have exactly two dimensions");

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();

    this.rectangles = Arrays.copyOf(rectangles, rectangles.length);
    this.doProfile = doProfile;

    setScope(Rectangle.getStream(this.rectangles));
  }

  /**
   * It specifies a diff constraint.
   *
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   */
  public Diff(IntVar[][] rectangles) {

    assert rectangles != null : "Rectangles list is null";

    queueIndex = 2;
    this.rectangles = Rectangle.toArrayOf2dRectangles(rectangles);
    numberId = idNumber.incrementAndGet();
    setScope(Rectangle.getStream(this.rectangles));
  }

  /**
   * It constructs a diff constraint.
   *
   * @param o1 list of variables denoting origin of the rectangle in the first dimension.
   * @param o2 list of variables denoting origin of the rectangle in the second dimension.
   * @param l1 list of variables denoting length of the rectangle in the first dimension.
   * @param l2 list of variables denoting length of the rectangle in the second dimension.
   * @param profile it specifies if the profile should be computed and used.
   */
  @Builder
  public Diff(IntVar[] o1, IntVar[] o2, IntVar[] l1, IntVar[] l2, boolean profile) {
    this(o1, o2, l1, l2);
    doProfile = profile;
  }

  /**
   * It constructs a diff constraint.
   *
   * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
   * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
   * @param length1 list of variables denoting length of the rectangle in the first dimension.
   * @param length2 list of variables denoting length of the rectangle in the second dimension.
   */
  public Diff(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {

    checkInputForNullness(
        new String[] {"origin1", "origin2", "length1", "length2"},
        origin1,
        origin2,
        length1,
        length2);

    queueIndex = 2;
    this.rectangles = Rectangle.toArrayOf2dRectangles(origin1, origin2, length1, length2);
    numberId = idNumber.incrementAndGet();
    setScope(Rectangle.getStream(this.rectangles));
  }

  /**
   * It specifies a diffn constraint.
   *
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   */
  public Diff(List<? extends List<? extends IntVar>> rectangles) {

    queueIndex = 2;
    this.rectangles = Rectangle.toArrayOf2dRectangles(rectangles);
    numberId = idNumber.incrementAndGet();
    setScope(Rectangle.getStream(this.rectangles));
  }

  /**
   * It specifies a diff constraint.
   *
   * @param profile specifies is the profiles are used.
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   */
  public Diff(List<? extends List<? extends IntVar>> rectangles, boolean profile) {

    this(rectangles);
    doProfile = profile;
  }

  /**
   * It constructs a diff constraint.
   *
   * @param o1 list of variables denoting origin of the rectangle in the first dimension.
   * @param o2 list of variables denoting origin of the rectangle in the second dimension.
   * @param l1 list of variables denoting length of the rectangle in the first dimension.
   * @param l2 list of variables denoting length of the rectangle in the second dimension.
   */
  public Diff(
      List<? extends IntVar> o1,
      List<? extends IntVar> o2,
      List<? extends IntVar> l1,
      List<? extends IntVar> l2) {

    this(
        o1.toArray(new IntVar[0]),
        o2.toArray(new IntVar[0]),
        l1.toArray(new IntVar[0]),
        l2.toArray(new IntVar[0]));
  }

  /**
   * It constructs a diff constraint.
   *
   * @param o1 list of variables denoting origin of the rectangle in the first dimension.
   * @param o2 list of variables denoting origin of the rectangle in the second dimension.
   * @param l1 list of variables denoting length of the rectangle in the first dimension.
   * @param l2 list of variables denoting length of the rectangle in the second dimension.
   * @param profile it specifies if the profile should be computed and used.
   */
  public Diff(
      List<? extends IntVar> o1,
      List<? extends IntVar> o2,
      List<? extends IntVar> l1,
      List<? extends IntVar> l2,
      boolean profile) {
    this(o1, o2, l1, l2);
    doProfile = profile;
  }

  /**
   * It specifies a diff constraint.
   *
   * @param profile specifies is the profiles are used.
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   */
  public Diff(IntVar[][] rectangles, boolean profile) {
    this(rectangles);
    doProfile = profile;
  }

  @Override
  public void removeLevel(int level) {
    variableQueue.clear();
  }

  @Override
  public void consistency(Store store) {

    currentStore = store;

    do {

      store.propagationHasOccurred = false;

      Set<IntVar> fdvs = variableQueue;
      variableQueue = new HashSet<>();
      narrowRectangles(fdvs);

    } while (store.propagationHasOccurred);
  }

  boolean containsChangedVariable(Rectangle r, Set<IntVar> fdvQueue) {
    boolean contains = false;
    int dim = r.dim;
    int i = 0;
    while (!contains && i < dim) {
      contains = fdvQueue.contains(r.origin[i]) || fdvQueue.contains(r.length[i]);
      i++;
    }
    return contains;
  }

  private boolean findRectangles(
      Rectangle r,
      List<IntRectangle> usedRect,
      List<Rectangle> profileCandidates,
      Set<IntVar> fdvQueue) {

    boolean contains = false;
    boolean checkArea = false;

    long area = 0;
    long commonArea = 0;
    int totalNumberOfRectangles = 0;
    int dim = r.dim;
    int[] startMin = new int[dim];
    int[] stopMax = new int[dim];
    int[] minLength = new int[dim];
    int[] r_min = new int[dim];
    int[] r_max = new int[dim];
    for (int i = 0; i < startMin.length; i++) {
      startMin[i] = IntDomain.MaxInt;
      stopMax[i] = 0;
      minLength[i] = r.length[i].min();

      IntDomain rOriginDom = r.origin[i].dom();
      r_min[i] = rOriginDom.min();
      r_max[i] = rOriginDom.max() + r.length[i].max();
    }

    int[] sOriginMin = new int[dim];
    int[] sOriginMax = new int[dim];
    int[] sLengthMin = new int[dim];

    for (Rectangle s : rectangles) {

      boolean overlap = true;

      if (r != s) {
        boolean sChanged = containsChangedVariable(s, fdvQueue);

        IntRectangle Use = new IntRectangle(dim);
        long sArea = 1;
        long partialCommonArea = 1;

        boolean use = true;
        boolean minLength0 = false;
        int s_min;
        int s_max;
        int start;
        int stop;
        int m = 0;
        int j = 0;

        while (overlap && m < dim) {
          // check if domains of r and s overlap
          IntDomain sOriginIdom = s.origin[m].dom();
          IntDomain sLengthIdom = s.length[m].dom();
          final int sLengthiMin = sLengthIdom.min();
          int sOriginiMax = sOriginIdom.max();
          s_min = sOriginIdom.min();
          s_max = sOriginiMax + sLengthIdom.max();

          overlap = intervalOverlap(r_min[m], r_max[m], s_min, s_max);

          // min start, max stop and min length
          sOriginMin[m] = s_min;
          sOriginMax[m] = sOriginiMax + sLengthiMin;
          sLengthMin[m] = sLengthiMin;

          // check if s occupies some space
          start = sOriginiMax;
          stop = s_min + sLengthiMin;
          if (start < stop) {
            Use.add(start, stop - start);
            j++;
          } else {
            use = false;
          }

          // min length == 0
          minLength0 = minLength0 || (sLengthMin[m] <= 0);

          m++;
        }

        if (overlap) {
          if (use) { // rectangles taking space
            usedRect.add(Use);
            contains = contains || sChanged;
          }

          if (!minLength0) { // profile candiates
            if (j > 0) {
              profileCandidates.add(s);
              contains = contains || sChanged;
            }

            checkArea = true;
            totalNumberOfRectangles++;
            for (int i = 0; i < dim; i++) {
              if (sOriginMin[i] < startMin[i]) {
                startMin[i] = sOriginMin[i];
              }
              if (sOriginMax[i] > stopMax[i]) {
                stopMax[i] = sOriginMax[i];
              }
              if (minLength[i] > sLengthMin[i]) {
                minLength[i] = sLengthMin[i];
              }

              sArea *= sLengthMin[i];
            }
            area += sArea;
          } // profile candidate end

          // calculate area within rectangle r possible placement
          for (int i = 0; i < dim; i++) {
            if (sOriginMin[i] <= r_min[i]) {
              if (sOriginMax[i] <= r_max[i]) {
                int distance1 = sOriginMin[i] + sLengthMin[i] - r_min[i];
                sLengthMin[i] = Math.max(distance1, 0);
              } else {
                // sOriginMax[i] > r_max[i])
                int rmax = r.origin[i].max() + r.length[i].min();

                int distance1 = sOriginMin[i] + sLengthMin[i] - r_min[i];
                int distance2 = sLengthMin[i] - (sOriginMax[i] - rmax);
                if (distance1 > rmax - r_min[i]) {
                  distance1 = rmax - r_min[i];
                }
                if (distance2 > rmax - r_min[i]) {
                  distance2 = rmax - r_min[i];
                }
                if (distance1 < distance2) {
                  sLengthMin[i] = Math.max(distance1, 0);
                } else if (distance2 > 0) {
                  if (distance2 < sLengthMin[i]) {
                    sLengthMin[i] = distance2;
                  }
                } else {
                  sLengthMin[i] = 0;
                }
              }
            } else // sOriginMin[i] > r_min[i]
            if (sOriginMax[i] > r_max[i]) {
              int distance2 =
                  sLengthMin[i] - (sOriginMax[i] - (r.origin[i].max() + r.length[i].min()));
              if (distance2 > 0) {
                if (distance2 < sLengthMin[i]) {
                  sLengthMin[i] = distance2;
                }
              } else {
                sLengthMin[i] = 0;
              }
            }

            partialCommonArea = partialCommonArea * sLengthMin[i];
          }
          // end for
          commonArea += partialCommonArea;
        }
        if (commonArea + r.minArea() > (long) (r_max[0] - r_min[0]) * (r_max[1] - r_min[1])) {
          throw Store.failException;
        }
      }
    }

    if (checkArea) { // check whether there is
      // enough room for all rectangles
      area += r.minArea();
      long availArea = 1;
      long rectNumber = 1;
      for (int i = 0; i < startMin.length; i++) {
        IntDomain rOriginIdom = r.origin[i].dom();
        IntDomain rLengthIdom = r.length[i].dom();
        int rOriginiMin = rOriginIdom.min();
        int rOriginiMax = rOriginIdom.max();
        int rLengthiMin = rLengthIdom.min();
        if (rOriginiMin < startMin[i]) {
          startMin[i] = rOriginiMin;
        }
        if (rOriginiMax + rLengthiMin > stopMax[i]) {
          stopMax[i] = rOriginiMax + rLengthiMin;
        }
      }
      boolean checkRectNumber = true;
      for (int i = 0; i < startMin.length; i++) {
        availArea *= stopMax[i] - startMin[i];
        if (minLength[i] != 0) {
          rectNumber *= (stopMax[i] - startMin[i]) / minLength[i];
        } else {
          checkRectNumber = false;
        }
      }

      if (availArea < area) {
        throw Store.failException;
      } else
      // check whether there is enough room for
      // all minimal rectangles
      if (checkRectNumber && rectNumber < (totalNumberOfRectangles + 1)) {
        throw Store.failException;
      }
    }

    return contains;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  /**
   * Returns the array of rectangles constrained by this diff constraint.
   *
   * @return the array of rectangles.
   */
  Rectangle[] getRectangles() {
    return rectangles;
  }

  boolean intervalOverlap(int min1, int max1, int min2, int max2) {
    return !(min1 >= max2 || max1 <= min2);
  }

  private Pair minForbiddenInterval(
      int start, int i, Rectangle r, List<IntRectangle> consideredRect) {

    if (notFit(i, r, consideredRect, start)) {
      return new Pair(start, start + minPosition);
    } else {
      return new Pair(-1, -1);
    }
  }

  private void narrowIth(
      int i, Rectangle r, List<IntRectangle> usedRect, List<Rectangle> profileCandidates) {
    final int rLengthiMin = r.length[i].min();

    durMax = new ArrayList<>();
    durMax.add(IntDomain.MaxInt);

    if (!profileCandidates.isEmpty() && doProfile) {
      profileNarrowing(i, r, profileCandidates);
    }

    durMax = new ArrayList<>();
    durMax.add(IntDomain.MaxInt);

    if (!usedRect.isEmpty()) {

      IntRectangle[] usedRectArray = new IntRectangle[usedRect.size()];

      usedRectArray = usedRect.toArray(usedRectArray);

      TreeSet<IntRectangle> starts = new TreeSet<>(dimIthMinComparator.apply(i));

      Collections.addAll(starts, usedRectArray);

      int sizeOfstartsOfR =
          Math.max(r.origin[0].domain.noIntervals(), r.origin[1].domain.noIntervals());

      IntRectangle[] startsOfR = new IntRectangle[sizeOfstartsOfR];

      for (int k = 0; k < sizeOfstartsOfR; k++) {
        startsOfR[k] = new IntRectangle(r.dim);
      }

      for (int k = 0; k < r.dim; k++) {
        IntDomain rOrigin = r.origin[k].dom();
        int rOriginSize = rOrigin.noIntervals();
        for (int n = 0; n < sizeOfstartsOfR; n++) {
          if (n < rOriginSize) {
            startsOfR[n].add(rOrigin.leftElement(n), 0);
          } else {
            startsOfR[n].add(rOrigin.min(), 0);
          }
        }
      }
      Collections.addAll(starts, startsOfR);

      List<IntRectangle> consideredRect = new ArrayList<>();
      for (IntRectangle ir : starts) {
        int s = ir.origin[i];

        consideredRect.clear();

        for (IntRectangle t : usedRectArray) {
          int tCompletion = t.origin[i] + t.length[i];

          if (t.origin[i] <= s && s - rLengthiMin < tCompletion) {
            consideredRect.add(t);
            // rectSize += t.length[j];
          }
        }

        if (!consideredRect.isEmpty()
        // && rSize < (rectSize + (rLengthjMin - 1) *
        // consideredRect.size())
        ) {

          IntDomain rIdom = r.origin[i].dom();
          if (s >= rIdom.min() && s <= rIdom.max()) {
            // "+i+
            // " starting at time interval "+ s + ".."
            // +(int)(s+r.length(i).min()-1)+
            // "\nCosideredRect =" + consideredRect);

            Pair exclude = minForbiddenInterval(s, i, r, consideredRect);

            if (exclude.max != -1) {
              IntervalDomain Update =
                  new IntervalDomain(IntDomain.MinInt, exclude.min - r.length[i].min());
              Update.unionAdapt(exclude.max, IntDomain.MaxInt);

              if (traceNarr) {
                log.debug(
                    "7. Obligatory rectangles Narrow {} in {} --> {}",
                    r.origin[i],
                    Update,
                    r.origin[i]);
              }

              r.origin[i].domain.in(currentStore.level, r.origin[i], Update);

              computeNewMaxDuration(r.origin[i], exclude.min, exclude.max);
            }
          }
        }
      }

      // Update rectangles length in direction i
      // sort rectangles on increasing origin i
      if (trace) {
        log.debug("10. length = {}", durMax);
      }

      int lengthLimit = 0;
      for (int l : durMax) {
        if (lengthLimit < l) {
          lengthLimit = l;
        }
      }

      if (traceNarr) {
        log.debug("10. Duration {} <-- 0..{}", r.length[i], lengthLimit);
      }

      r.length[i].domain.in(currentStore.level, r.length[i], 0, lengthLimit);
    }
  }

  private void computeNewMaxDuration(IntVar start, int excludeMin, int excludeMax) {

    int dMax = IntDomain.MaxInt;

    for (IntervalEnumeration ie = start.dom().intervalEnumeration(); ie.hasMoreElements(); ) {
      Interval i = ie.nextElement();

      if (excludeMax >= i.min() && excludeMin <= i.max()) {
        dMax = excludeMin - i.min();
        break;
      }
    }
    if (dMax < durMax.getLast()) {
      durMax.set(durMax.size() - 1, dMax);
    }

    if (start.dom().contains(excludeMax)) {
      durMax.add(IntDomain.MaxInt);
    }

    if (trace) {
      log.debug("+++ {}", durMax);
    }
  }

  void narrowRectangle(
      Rectangle r, List<IntRectangle> usedRect, List<Rectangle> profileCandidates) {

    if (trace) {
      log.debug("Narrowing {}", r);
      log.debug("{}", usedRect);
    }

    for (int i = 0; i < r.dim; i++) {
      // narrow in i-th dimension
      narrowIth(i, r, usedRect, profileCandidates);
    }
  }

  void narrowRectangles(Set<IntVar> fdvQueue) {
    boolean needToNarrow = false;
    List<IntRectangle> usedRect = new ArrayList<>();
    List<Rectangle> profileCandidates = new ArrayList<>();

    for (Rectangle r : rectangles) {
      boolean settled = true;
      boolean minLengthEq0 = false;
      int maxLevel = 0;
      for (int i = 0; i < r.dim; i++) {
        IntDomain rOrigin = r.origin[i].dom();
        IntDomain rLength = r.length[i].dom();
        settled = settled && rOrigin.singleton() && rLength.singleton();

        minLengthEq0 = minLengthEq0 || (rLength.min() <= 0);

        int originStamp = rOrigin.stamp;
        int lengthStamp = rLength.stamp;
        if (maxLevel < originStamp) {
          maxLevel = originStamp;
        }
        if (maxLevel < lengthStamp) {
          maxLevel = lengthStamp;
        }
      }

      if (!(settled && maxLevel < currentStore.level)) {

        needToNarrow = needToNarrow || containsChangedVariable(r, fdvQueue);

        usedRect.clear();
        profileCandidates.clear();
        boolean ntN = findRectangles(r, usedRect, profileCandidates, fdvQueue);
        needToNarrow = needToNarrow || ntN;

        if (needToNarrow) {
          narrowRectangle(r, usedRect, profileCandidates);
        }
      }
    }
  }

  private boolean notFit(
      int i, Rectangle r, List<IntRectangle> consideredRect, int barierPosition) {
    Profile barrier = new Profile((short) Profile.diffn);
    int minimalAfter = 0;
    int j = 0;
    boolean excludedState = true;
    while (excludedState && j < r.dim) {
      if (i != j) {
        IntDomain rOriginJdom = r.origin[j].dom();
        IntDomain rLengthJdom = r.length[j].dom();
        int minJ = rOriginJdom.min();
        final int maxJ = rOriginJdom.max() + rLengthJdom.min();
        int durJ = rLengthJdom.min();

        int currentJposition = minJ;
        barrier.clear();
        for (IntRectangle hinder : consideredRect) {
          int hinderJ = hinder.origin[j];
          int hinderValue = hinder.origin[i] + hinder.length[i] - barierPosition;
          if (hinderValue > 0) {
            barrier.addToProfile(hinderJ, hinderJ + hinder.length[j], hinderValue);
          }
        }

        int k = 0;
        int barrierSize = barrier.size();
        while (k < barrierSize && excludedState) {
          ProfileItem p = barrier.get(k);
          int hinderStart = p.min;
          int hinderStop = p.max;
          if (hinderStart - currentJposition >= durJ) {
            excludedState = false;
          }
          currentJposition = hinderStop;
          k++;
        }
        if (excludedState && maxJ - currentJposition >= durJ) {
          excludedState = false;
        }

        if (excludedState) {
          ProfileItem first = barrier.getFirst();
          ProfileItem last = barrier.getLast();
          if (minJ < first.min) { // exist free space before first
            // obstacle
            barrier.addToProfile(minJ, first.min, minimalAfter);
          }
          if (maxJ > last.max) { // exist free space after last
            // obstacle
            barrier.addToProfile(last.max, maxJ, minimalAfter);
          }
          List<Interval> toAdd = new ArrayList<>();
          for (int m = 0; m < barrier.size() - 1; m++) {
            ProfileItem p = barrier.get(m);
            ProfileItem pNext = barrier.get(m + 1);
            if (p.max != pNext.min) {
              toAdd.add(new Interval(p.max, pNext.min));
            }
          }
          for (Interval v : toAdd) {
            barrier.addToProfile(v.min(), v.max(), minimalAfter);
          }

          int minSizeAfterBarier = IntDomain.MaxInt;
          for (ProfileItem p : barrier) {
            if (p.value < minSizeAfterBarier) {
              if (p.value == minimalAfter && p.max - p.min >= durJ) {
                minSizeAfterBarier = minimalAfter;
                break;
              }
              if (p.value > minimalAfter) {
                minSizeAfterBarier = p.value;
              }
            }
          }
          minPosition = minSizeAfterBarier;
        }
      }
      j++;
    }

    return excludedState;
  }

  private void profileCheckInterval(
      Store store,
      DiffnProfile profile,
      int limit,
      IntVar start,
      IntVar duration,
      int imin,
      int imax,
      IntVar resources) {

    int dur = duration.min();
    int intervalEnd = imax + dur;
    for (ProfileItem p : profile) {
      if (trace) {
        log.debug("Comparing [{}, {}] with profile item {}", imin, imax, p);
      }

      if (intervalOverlap(imin, intervalEnd, p.min, p.max)) {
        if (limit - p.value < resources.min()) {
          // Check for possible narrowing of start or fail
          IntDomain startDom = start.dom();
          int updateMin = p.min - dur + 1;
          int updateMax = p.max - 1;

          if (!(updateMin > startDom.max() || updateMax < startDom.min())) {

            IntervalDomain update = new IntervalDomain(IntDomain.MinInt, p.min - dur);
            update.unionAdapt(p.max, IntDomain.MaxInt);

            if (traceNarr) {
              log.debug("6. Profile Narrowed {} \\ {} => {}", start, update, start);
            }

            start.domain.in(store.level, start, update);

            computeNewMaxDuration(start, p.min, p.max);

            int lengthLimit = 0;
            for (int l : durMax) {
              if (lengthLimit < l) {
                lengthLimit = l;
              }
            }

            if (traceNarr) {
              log.debug("6b. Length {} <-- 0..{}", duration, lengthLimit);
            }

            duration.domain.in(currentStore.level, duration, 0, lengthLimit);
          }
        } else {
          IntDomain startDom = start.dom();
          int startVal = startDom.max();
          int stop = startDom.min() + dur;
          if (startVal < stop && intervalOverlap(startVal, stop, p.min, p.max)) {
            int updateMax = limit - p.value;
            if (updateMax < resources.max()) {
              IntervalDomain update = new IntervalDomain(0, updateMax);

              if (traceNarr) {
                log.debug("8. Profile Narrowed {} in {} => {}", resources, update, resources);
              }

              resources.domain.in(store.level, resources, update);
            }
          }
        }
      }
    }
  }

  void profileCheckRectangle(DiffnProfile profile, Rectangle r, int i, int j) {

    IntVar s = r.origin[i];
    IntVar dur = r.length[i];
    IntVar resUse = r.length[j];
    IntDomain rOriginJdom = r.origin[j].dom();
    int limit = rOriginJdom.max() + resUse.max() - rOriginJdom.min();

    if (trace) {
      log.debug("Start time = {}, resource use = {}", s, resUse);
    }

    IntDomain sDom = s.dom();

    for (int m = 0; m < sDom.noIntervals(); m++) {
      profileCheckInterval(
          currentStore, profile, limit, s, dur, sDom.leftElement(m), sDom.rightElement(m), resUse);
    }
  }

  void profileNarrowing(int i, Rectangle r, List<Rectangle> profileCandidates) {
    // check profile first

    IntDomain rOriginIdom = r.origin[i].dom();
    int rOriginIdomMin = rOriginIdom.min();
    int rOriginIdomMax = rOriginIdom.max();
    DiffnProfile profile = new DiffnProfile();

    for (int j = 0; j < r.dim; j++) {
      if (j != i) {
        profile.make(
            j, i, r, rOriginIdomMin, rOriginIdomMax + r.length[i].min(), profileCandidates);

        if (!profile.isEmpty()) {
          if (trace) {
            log.debug("{}\n{}", r, profileCandidates);
            log.debug("Profile in dimension {} and {}\n{}", i, j, profile);
          }

          profileCheckRectangle(profile, r, i, j);
        }
      }
    }
  }

  @Override
  public void queueVariable(int level, Var var) {
    if (level == stamp) {
      variableQueue.add((IntVar) var);
    } else {
      variableQueue.clear();
      stamp = level;
      variableQueue.add((IntVar) var);
    }
  }

  @Override
  public boolean satisfied() {
    boolean sat = true;

    Rectangle recti;
    Rectangle rectj;
    int i = 0;
    while (sat && i < rectangles.length) {
      recti = rectangles[i];
      int j = i + 1;
      while (sat && j < rectangles.length) {
        rectj = rectangles[j];
        sat = !recti.domOverlap(rectj);
        j++;
      }
      i++;
    }
    return sat;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : diff (");

    int i = 0;
    for (Rectangle R : rectangles) {
      result.append(R);
      if (i < rectangles.length - 1) {
        result.append(", ");
      }
      i++;
    }
    return result.append(")").toString();
  }

  record Pair(int min, int max) {}
}
