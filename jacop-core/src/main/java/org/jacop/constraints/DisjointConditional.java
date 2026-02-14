/*
 * DisjointConditional.java
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
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * DisjointConditional constraint assures that any two rectangles from a vector of rectangles does
 * not overlap in at least one direction. The execption from this rule is specified on the list of
 * tuple [recti, rectj, C], where recti and rectj are integers representing given rectangles
 * positions on the list of rectangles (starting from 1) and C is FDV 0..1. When C=1 then rectnagles
 * must not overlap otherwise the overlaping is not checked.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class DisjointConditional extends Diff {

  static final boolean TRACE = false;
  static final boolean TRACE_NARR = false;
  static boolean traceOn = TRACE;
  static boolean traceNarrOn = TRACE_NARR;
  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies what rectangles can conditionally overlap. */
  private ExclusiveList exclusionList = new ExclusiveList();

  List<IntVar>[] condVariables;
  DisjointCondVar[] evalRects;

  /**
   * It specifies a diff constraint.
   *
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   * @param exclusionList it is a list of exclusive items. Each item consists of two ints and a
   *     variable.
   * @param doProfile should the constraint compute and use the profile functionality.
   */
  public DisjointConditional(
      Rectangle[] rectangles, ExclusiveList exclusionList, boolean doProfile) {

    checkInputForNullness(
        new String[] {"rectangles", "exclusionList"}, rectangles, new Object[] {exclusionList});
    checkInput(rectangles, i -> i.dim == 2, "rectangle needs to have exactly two dimensions");

    this.queueIndex = 2;

    this.rectangles = Arrays.copyOf(rectangles, rectangles.length);

    this.doProfile = doProfile;
    this.exclusionList = new ExclusiveList();
    this.exclusionList.addAll(exclusionList);

    this.numberId = idNumber.incrementAndGet();

    setScope(
        Stream.concat(
            Rectangle.getStream(this.rectangles), exclusionList.stream().map(ExclusiveItem::cond)));
  }

  /**
   * It creates Disjoint conditional constraint.
   *
   * @param rectangles the rectangles within a constraint.
   * @param exceptionIndices a list of pairs of conditionally overlaping rectangles.
   * @param exceptionCondition a variable specifying if a corresponding pair is nonoverlapping.
   */
  public DisjointConditional(
      List<List<? extends IntVar>> rectangles,
      List<List<Integer>> exceptionIndices,
      List<? extends IntVar> exceptionCondition) {

    queueIndex = 2;

    int size = rectangles.getFirst().size();
    this.rectangles = new Rectangle[rectangles.size()];

    int i = 0;

    for (List<? extends IntVar> R : rectangles) {
      if (R.size() == size) {
        Rectangle rect = new Rectangle(R);
        this.rectangles[i] = rect;
        i++;
      } else {
        String s = "\nNot equal sizes of rectangle vectors in Diff";
        throw new IllegalArgumentException(s);
      }
    }
    if (size / 2 != 2) {
      String s = "\nRectangles of size > 2 not currently supported by Diff";
      throw new IllegalArgumentException(s);
    }

    for (i = 0; i < exceptionIndices.size(); i++) {
      int item1 = exceptionIndices.get(i).getFirst();
      int item2 = exceptionIndices.get(i).get(1);
      IntVar condition = exceptionCondition.get(i);
      exclusionList.add(new ExclusiveItem(item1, item2, condition));
    }

    numberId = idNumber.incrementAndGet();
    setScope(Stream.concat(Rectangle.getStream(this.rectangles), exceptionCondition.stream()));
  }

  /**
   * It creates Disjoint conditional constraint.
   *
   * @param rectangles the rectangles within a constraint.
   * @param exceptionIndices it specifies a list of pairs, where each pair specifies two rectangles
   *     which conditionally overlap.
   * @param exceptionCondition a variable specifying if a corresponding pair is nonoverlapping.
   * @param profile it specifies if the profiles are used and computed within the constraint.
   */
  public DisjointConditional(
      List<List<? extends IntVar>> rectangles,
      List<List<Integer>> exceptionIndices,
      List<? extends IntVar> exceptionCondition,
      boolean profile) {

    this(rectangles, exceptionIndices, exceptionCondition);
    doProfile = profile;
  }

  /**
   * It constructs a disjoint conditional constraint.
   *
   * @param o1 variables specifying the origin in the first dimension.
   * @param o2 variables specifying the origin in the second dimension.
   * @param l1 variables specifying the length in the first dimension.
   * @param l2 variables specifying the length in the second dimension.
   * @param exceptionIndices it specifies a list of pairs, where each pair specifies two rectangles
   *     which conditionally overlap.
   * @param exceptionCondition a variable specifying if a corresponding pair is nonoverlapping.
   */
  public DisjointConditional(
      List<? extends IntVar> o1,
      List<? extends IntVar> o2,
      List<? extends IntVar> l1,
      List<? extends IntVar> l2,
      List<List<Integer>> exceptionIndices,
      List<? extends IntVar> exceptionCondition) {

    this(
        o1.toArray(new IntVar[0]),
        o2.toArray(new IntVar[0]),
        l1.toArray(new IntVar[0]),
        l2.toArray(new IntVar[0]),
        exceptionIndices,
        exceptionCondition);
  }

  /**
   * It constructs a disjoint conditional constraint.
   *
   * @param o1 variables specifying the origin in the first dimension.
   * @param o2 variables specifying the origin in the second dimension.
   * @param l1 variables specifying the length in the first dimension.
   * @param l2 variables specifying the length in the second dimension.
   * @param exceptionIndices it specifies a list of pairs, where each pair specifies two rectangles
   *     which conditionally overlap.
   * @param exceptionCondition a variable specifying if a corresponding pair is nonoverlapping.
   * @param profile it specifies if the profiles are being computed and used within a constraint.
   */
  public DisjointConditional(
      List<? extends IntVar> o1,
      List<? extends IntVar> o2,
      List<? extends IntVar> l1,
      List<? extends IntVar> l2,
      List<List<Integer>> exceptionIndices,
      List<? extends IntVar> exceptionCondition,
      boolean profile) {

    this(o1, o2, l1, l2, exceptionIndices, exceptionCondition);
    doProfile = profile;
  }

  /**
   * It constructs a disjoint conditional constraint.
   *
   * @param origin1 variables specifying the origin in the first dimension.
   * @param origin2 variables specifying the origin in the second dimension.
   * @param length1 variables specifying the length in the first dimension.
   * @param length2 variables specifying the length in the second dimension.
   * @param exceptionIndices it specifies a list of pairs, where each pair specifies two rectangles
   *     which conditionally overlap.
   * @param exceptionCondition a variable specifying if a corresponding pair is nonoverlapping.
   */
  public DisjointConditional(
      IntVar[] origin1,
      IntVar[] origin2,
      IntVar[] length1,
      IntVar[] length2,
      List<List<Integer>> exceptionIndices,
      List<? extends IntVar> exceptionCondition) {

    checkInputForNullness(
        new String[] {
          "origin1", "origin2", "length1", "length2", "exceptionIndices", "exceptionCondition"
        },
        origin1,
        origin2,
        length1,
        length2,
        new Object[] {exceptionIndices},
        new Object[] {exceptionCondition});

    this.queueIndex = 2;

    int size = origin1.length;
    if (size == origin2.length && size == length1.length && size == length2.length) {

      this.rectangles = new Rectangle[size];
      for (int i = 0; i < size; i++) {
        this.rectangles[i] =
            new Rectangle(new IntVar[] {origin1[i], origin2[i], length1[i], length2[i]});
      }

    } else {
      throw new IllegalArgumentException(
          "DisjointConditional does not have equal sizes of length and origin vectors.");
    }

    for (int i = 0; i < exceptionIndices.size(); i++) {
      int item1 = exceptionIndices.get(i).getFirst();
      int item2 = exceptionIndices.get(i).get(1);
      IntVar condition = exceptionCondition.get(i);
      exclusionList.add(new ExclusiveItem(item1, item2, condition));
    }

    this.numberId = idNumber.incrementAndGet();

    setScope(Stream.concat(Rectangle.getStream(this.rectangles), exceptionCondition.stream()));
  }

  /**
   * It constructs a disjoint conditional constraint.
   *
   * @param o1 variables specifying the origin in the first dimension.
   * @param o2 variables specifying the origin in the second dimension.
   * @param l1 variables specifying the length in the first dimension.
   * @param l2 variables specifying the length in the second dimension.
   * @param exceptionIndices list of rectangles that may not be considered
   * @param exceptionCondition conditions for rectangles that may not be considered
   * @param profile it specifies if the profiles are being used and computed within that constraint.
   */
  public DisjointConditional(
      IntVar[] o1,
      IntVar[] o2,
      IntVar[] l1,
      IntVar[] l2,
      List<List<Integer>> exceptionIndices,
      List<? extends IntVar> exceptionCondition,
      boolean profile) {
    this(o1, o2, l1, l2, exceptionIndices, exceptionCondition);
    doProfile = profile;
  }

  /**
   * It creates Disjoint conditional constraint.
   *
   * @param rectangles the rectangles within a constraint.
   * @param exceptionIndices list of rectangles that may not be considered
   * @param exceptionCondition conditions for rectangles that may not be considered
   */
  public DisjointConditional(
      IntVar[][] rectangles,
      List<List<Integer>> exceptionIndices,
      List<? extends IntVar> exceptionCondition) {

    if (rectangles == null) {
      throw new IllegalArgumentException("Rectangles list is null");
    }

    queueIndex = 2;
    IntVar[] R;

    int size = rectangles[0].length;
    this.rectangles = new Rectangle[rectangles.length];

    for (int i = 0; i < rectangles.length; i++) {
      if (rectangles[i] == null) {
        throw new IllegalArgumentException(i + "-th list within rectangles list is null");
      }
      R = rectangles[i];
      if (R.length == size) {
        Rectangle rect = new Rectangle(R);
        this.rectangles[i] = rect;
      } else {
        String s = "\nNot equal sizes of rectangle vectors in Diff";
        throw new IllegalArgumentException(s);
      }
    }
    if (size / 2 != 2) {
      String s = "\nRectangles of size > 2 not currently supported by Diff";
      throw new IllegalArgumentException(s);
    }

    for (int i = 0; i < exceptionIndices.size(); i++) {
      int item1 = exceptionIndices.get(i).getFirst();
      int item2 = exceptionIndices.get(i).get(1);
      IntVar condition = exceptionCondition.get(i);
      exclusionList.add(new ExclusiveItem(item1, item2, condition));
    }

    numberId = idNumber.incrementAndGet();

    setScope(Stream.concat(Rectangle.getStream(this.rectangles), exceptionCondition.stream()));
  }

  /**
   * It creates Disjoint conditional constraint.
   *
   * @param rectangles the rectangles within a constraint.
   * @param exceptionIndices list of rectangles that may not be considered
   * @param exceptionCondition conditions for rectangles that may not be considered
   * @param profile it specifies if the profiles are being computed and used within that constraint.
   */
  public DisjointConditional(
      IntVar[][] rectangles,
      List<List<Integer>> exceptionIndices,
      List<? extends IntVar> exceptionCondition,
      boolean profile) {

    this(rectangles, exceptionIndices, exceptionCondition);
    doProfile = profile;
  }

  boolean checkRect(RectangleWithCondition r) {
    return r.condition() == null || (r.condition().min() == 1);
  }

  boolean conditionChanged(Set<IntVar> fdvQueue, int j) {
    boolean changed = false;
    List<IntVar> el = condVariables[j];
    int i = 0;
    while (!changed && i < el.size()) {
      changed = fdvQueue.contains(el.get(i));
      i++;
    }
    return changed;
  }

  boolean doesNotFit(int j, Rectangle r, Profile barrier) {
    boolean excludedState = true;

    IntDomain rOriginJdom = r.origin[j].dom();
    IntDomain rLengthJdom = r.length[j].dom();
    int minJ = rOriginJdom.min();
    int maxJ = rOriginJdom.max() + rLengthJdom.min();
    int durJ = rLengthJdom.min();
    int currentJposition = minJ;
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
    return excludedState;
  }

  int findMaxLength(int i, int length, Rectangle r) {

    int maxLength = length;
    IntDomain origin = r.origin[i].dom();
    int dur = r.length[i].min();

    for (int m = 0; m < origin.noIntervals(); m++) {
      int intervalLength = origin.rightElement(m) - origin.leftElement(m) + dur;
      if (maxLength < intervalLength) {
        maxLength = intervalLength;
      }
    }
    return maxLength;
  }

  boolean findRectangles(
      Rectangle r,
      int index,
      List<IntRectangle> usedRect,
      List<RectangleWithCondition> profileCandidates,
      List<RectangleWithCondition> overlappingRects,
      Set<IntVar> fdvQueue) {
    // Variable condition;
    boolean contains = false;
    boolean checkArea = false;

    long area = 0;
    int totalNumberOfRectangles = 0;
    int dim = r.dim();
    int[] startMin = new int[dim];
    int[] stopMax = new int[dim];
    int[] minLength = new int[dim];
    int[] r_min = new int[dim];
    int[] r_max = new int[dim];
    for (int i = 0; i < startMin.length; i++) {
      IntDomain rLengthDom = r.length[i].dom();
      startMin[i] = IntDomain.MAX_INT;
      stopMax[i] = 0;
      minLength[i] = rLengthDom.min();

      IntDomain rOriginDom = r.origin[i].dom();
      r_min[i] = rOriginDom.min();
      r_max[i] = rOriginDom.max() + rLengthDom.max();
    }

    for (RectangleWithCondition s : ((DisjointCondVarValue) evalRects[index].value()).rects) {
      boolean overlap = true;

      boolean sChanged =
          containsChangedVariable(s, fdvQueue) || conditionChanged(fdvQueue, s.index);

      IntRectangle Use = new IntRectangle(dim);
      long sArea = 1;

      boolean use = true;
      boolean minLength0 = false;
      int s_min;
      int s_max;
      int start;
      int stop;
      int m = 0;
      int j = 0;
      int[] sOriginMin = new int[dim];
      int[] sOriginMax = new int[dim];
      int[] sLengthMin = new int[dim];

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
        if (start <= stop) { // we allow length=0 for rectangles
          // to occupy o length space !!!
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
        if (s.condition() == null || s.condition().max() != 0) {
          overlappingRects.add(s);
        }

        if (checkRect(s)) {
          if (use) {
            usedRect.add(Use);
            contains = contains || sChanged;
          }

          if (!minLength0) { // profile candiates
            if (j > 0) {
              profileCandidates.add(s);
              contains = contains || sChanged;
            }

            if (!exclusionList.onList(s.index)) {
              // simplification - considers only rectangles
              // which cannot be exclusive !!!
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

                sArea = sArea * sLengthMin[i];
              }
              area += sArea;
            }
          }
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
      boolean minEqZero = false;
      for (int i = 0; i < startMin.length; i++) {
        availArea = availArea * (stopMax[i] - startMin[i]);
        if (minLength[i] == 0) {
          minEqZero = true;
        } else {
          rectNumber = rectNumber * ((stopMax[i] - startMin[i]) / minLength[i]);
        }
      }
      if (minEqZero) {
        rectNumber = Long.MAX_VALUE;
      }

      if (availArea < area || rectNumber < (totalNumberOfRectangles + 1)) {
        throw Store.failException;
      }
    }

    return contains;
  }

  @SuppressWarnings("unchecked")
  @Override
  public void impose(Store store) {

    super.impose(store);

    condVariables = new ArrayList[rectangles.length + 1];

    evalRects = new DisjointCondVar[rectangles.length];
    for (int i = 0; i < rectangles.length; i++) {
      condVariables[i + 1] = exclusionList.fdvs(i + 1);

      List<RectangleWithCondition> rectsC = new ArrayList<>();
      for (int j = 0; j < rectangles.length; j++) {
        if (i != j) {
          IntVar c = exclusionList.condition(i, j);
          rectsC.add(new RectangleWithCondition(j + 1, rectangles[j], c));
        }
      }
      evalRects[i] = new DisjointCondVar(store, rectsC);
    }

    for (ExclusiveItem ei : exclusionList) {
      IntVar v = ei.cond();
      if (!v.singleton()) {
        queueVariable(store.level, v);
      }
    }
  }

  Interval minForbiddenInterval(
      int start, int i, Rectangle r, List<IntRectangle> consideredRect, int minI) {

    if (notFit(i, r, consideredRect)) {
      return new Interval(start, minI);
    } else {
      return new Interval(-1, -1);
    }
  }

  void narrowIthCondition(
      int i,
      Rectangle r,
      List<IntRectangle> usedRect,
      List<RectangleWithCondition> profileCandidates) {
    Interval exclude;
    int s;
    int j = i == 0 ? 1 : 0;
    int rSize = r.origin[j].max() - r.origin[j].min();
    int rLengthjMin = r.length[j].min();
    int rLengthiMin = r.length[i].min();
    int barierSize = 0;

    if (!profileCandidates.isEmpty() && doProfile) {
      profileNarrowingCondition(i, r, profileCandidates);
    }

    if (!usedRect.isEmpty()) {

      IntRectangle[] usedRectArray = new IntRectangle[usedRect.size()];

      usedRectArray = usedRect.toArray(usedRectArray);

      TreeSet<IntRectangle> starts = new TreeSet<>(dimIthMinComparator.apply(i));
      Collections.addAll(starts, usedRectArray);

      IntRectangle strtR = new IntRectangle(r.dim);
      IntRectangle maxRect = new IntRectangle(r.dim);
      for (int k = 0; k < r.dim; k++) {
        IntDomain rOrigin = r.origin[k].dom();
        IntDomain rLength = r.length[k].dom();
        strtR.add(rOrigin.min(), rLength.min());
        if (k == i) {
          maxRect.add(rOrigin.max(), rLength.max());
        } else {
          maxRect.add(rOrigin.min(), rLength.min());
        }
      }
      starts.add(strtR);

      List<IntRectangle> consideredRect = new ArrayList<>();
      for (IntRectangle ir : starts) {
        s = ir.origins[i];

        consideredRect.clear();
        int minI = IntDomain.MAX_INT;
        long rectSize = 0;
        for (IntRectangle t : usedRectArray) {
          int tempMin = t.origins[i] + t.lengths[i];

          if (t.origins[i] - s < rLengthiMin && s < tempMin) {
            consideredRect.add(t);
            rectSize += t.lengths[j];
            // Determine minimum length in direction i
            // (possibly new start time)
            if (tempMin < minI) {
              minI = tempMin;
            }
          }
        }

        if (!consideredRect.isEmpty()
            && rSize < (rectSize + (long) (rLengthjMin - 1) * consideredRect.size())) {

          IntDomain rOriginDom = r.origin[i].dom();
          int m = 0;
          for (; m < rOriginDom.noIntervals(); m++) {
            if (s >= rOriginDom.leftElement(m) && s <= rOriginDom.rightElement(m)) {
              exclude = minForbiddenInterval(s, i, r, consideredRect, minI);

              if (exclude.max() != -1) {
                int min = exclude.min() - r.length[i].min();
                if (min + 1 < exclude.max()) {
                  IntervalDomain Update = new IntervalDomain(IntDomain.MIN_INT, min);
                  Update.unionAdapt(exclude.max(), IntDomain.MAX_INT);

                  if (traceNarrOn) {
                    log.debug(
                        "7. Obligatory rectangles Narrow {}\n{}\n{} in {}length={}\n --> {}",
                        consideredRect,
                        r,
                        r.origin[i],
                        Update,
                        r.length[i].min(),
                        r.origin[i]);
                  }

                  r.origin[i].domain.in(currentStore.level, r.origin[i], Update);
                }
              }
            }
          }
        }
      }

      // Update rectangles length in direction i
      // sort rectangles on increasing origin i
      List<IntRectangle> consideredRectDur = new ArrayList<>();
      for (IntRectangle t : usedRectArray) {
        if (t.overlap(maxRect)) {
          consideredRectDur.add(t);
          barierSize += t.lengths[j];
        }
      }

      if (!consideredRectDur.isEmpty()
          && rSize < (barierSize + (rLengthjMin - 1) * consideredRectDur.size())) {

        IntRectangle[] rects = new IntRectangle[consideredRectDur.size()];
        rects = consideredRectDur.toArray(rects);
        Arrays.sort(rects, dimIthMinComparator.apply(i));

        Profile barrier = new Profile();
        boolean lengthOk = true;
        int newMaxLength = 0;
        int n = 0;
        while (n < rects.length && lengthOk) {
          IntRectangle hinder = rects[n];
          barrier.addToProfile(hinder.origins[j], hinder.origins[j] + hinder.lengths[j], 1);
          if (doesNotFit(j, r, barrier)) {
            lengthOk = false;
            newMaxLength = hinder.origins[i] - r.origin[i].min();
          }
          n++;
        }
        if (!lengthOk) {
          // update length in dimension j
          int maxLength = findMaxLength(i, newMaxLength, r);

          if (maxLength < r.length[i].max()) {
            if (traceNarrOn) {
              log.debug(
                  "9. Obligatory rectangles Narrow {} in {}..{}",
                  r.length[i],
                  IntDomain.MIN_INT,
                  maxLength);
            }
            r.length[i].domain.inMax(currentStore.level, r.length[i], maxLength);
          }
        }
      }
    }
  }

  void narrowRectangleCondition(
      Rectangle r, List<IntRectangle> usedRect, List<RectangleWithCondition> profileCandidates) {

    if (traceOn) {
      log.debug("Narrowing {}", r);
      log.debug("{}", profileCandidates);
    }

    for (int i = 0; i < r.dim; i++) {
      // narrow in i-th dimension
      narrowIthCondition(i, r, usedRect, profileCandidates);
    }
  }

  @Override
  void narrowRectangles(Set<IntVar> fdvQueue) {
    Rectangle r;
    boolean needToNarrow = false;

    for (int l = 0; l < rectangles.length; l++) {
      r = rectangles[l];

      boolean minLengthLt0 = false;
      for (int i = 0; i < r.dim(); i++) {
        minLengthLt0 = minLengthLt0 || (r.length[i].min() < 0);
      }

      if (!minLengthLt0 // Check for rectangle r which has
      // all lengths > 0
      ) {
        // and are not fixed already

        needToNarrow = needToNarrow || containsChangedVariable(r, fdvQueue);

        List<IntRectangle> usedRect = new ArrayList<>();
        List<RectangleWithCondition> profileCandidates = new ArrayList<>();
        List<RectangleWithCondition> overlappingRects = new ArrayList<>();
        boolean ntN = findRectangles(r, l, usedRect, profileCandidates, overlappingRects, fdvQueue);

        needToNarrow = needToNarrow || ntN || conditionChanged(fdvQueue, l + 1);

        if (needToNarrow) {

          if (overlappingRects.size()
              != ((DisjointCondVarValue) evalRects[l].value()).rects.length) {
            DisjointCondVarValue newRects = new DisjointCondVarValue();
            newRects.setValue(overlappingRects);
            evalRects[l].update(newRects);
          }

          // Checking r against all s with minUse in the domain of r
          narrowRectangleCondition(r, usedRect, profileCandidates);
        }
      }
    }
  }

  boolean notFit(int i, Rectangle r, List<IntRectangle> consideredRect) {
    boolean excludedState = true;
    Profile barrier = new Profile();

    int j = 0;
    while (excludedState && j < r.dim) {
      if (i != j) {
        IntDomain rOriginJdom = r.origin[j].dom();
        IntDomain rLengthJdom = r.length[j].dom();
        int minJ = rOriginJdom.min();
        final int maxJ = rOriginJdom.max() + rLengthJdom.min();
        int durJ = rLengthJdom.min();

        barrier.clear();
        for (IntRectangle hinder : consideredRect) {
          int hinderJ = hinder.origins[j];
          barrier.addToProfile(hinderJ, hinderJ + hinder.lengths[j], 1);
        }

        int currentJposition = minJ;
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
      }
      j++;
    }
    return excludedState;
  }

  void profileCheckInterval(
      Store store,
      DisjointConditionalProfile profile,
      int limit,
      IntVar start,
      IntVar duration,
      int minVal,
      int maxVal,
      IntVar resources) {

    int dur = duration.min();
    for (ProfileItem p : profile) {
      if (traceOn) {
        log.debug("Comparing [{} {}] with profile item {}", minVal, maxVal, p);
      }
      if (intervalOverlap(minVal, maxVal + dur, p.min, p.max)) {
        if (limit - p.value < resources.min()) {
          // Check for possible narrowing of start or fail
          IntDomain startDom = start.dom();
          int updateMin = p.min - dur + 1;
          int updateMax = p.max - 1;
          if (!(updateMin > startDom.max() || updateMax < startDom.min())) {
            IntervalDomain update = new IntervalDomain(IntDomain.MIN_INT, p.min - dur);
            update.unionAdapt(p.max, IntDomain.MAX_INT);

            if (traceNarrOn) {
              log.debug(
                  "6. Profile Narrowed {} \\ {}; duration={}; resources={}, limit={}\n{}\n => {}",
                  start,
                  update,
                  duration,
                  resources,
                  limit,
                  profile,
                  start);
            }

            start.domain.in(store.level, start, update);
          }
        } else {
          IntDomain startDom = start.dom();
          int startVal = startDom.max();
          int stop = startDom.min() + dur;
          if (startVal < stop && intervalOverlap(startVal, stop, p.min, p.max)) {
            int updateMax = limit - p.value;
            IntervalDomain update = new IntervalDomain(0, updateMax);
            if (updateMax < resources.max()) {
              if (traceNarrOn) {
                log.debug("8. Profile Narrowed {} in {} => {}", resources, update, resources);
              }

              resources.domain.in(store.level, resources, update);
            }
          }
        }
      }
    }
  }

  void profileCheckRectangle(DisjointConditionalProfile profile, Rectangle r, int i, int j) {

    IntVar s = r.origin[i];
    IntVar dur = r.length[i];
    IntVar resUse = r.length[j];
    IntDomain rOriginJdom = r.origin[j].dom();
    int limit = rOriginJdom.max() + resUse.max() - rOriginJdom.min();

    if (traceOn) {
      log.debug("Start time = {}, resource use = {}", s, resUse);
    }

    IntDomain d = s.dom();
    for (int m = 0; m < d.noIntervals(); m++) {
      profileCheckInterval(
          currentStore, profile, limit, s, dur, d.leftElement(m), d.rightElement(m), resUse);
    }
  }

  void profileNarrowingCondition(
      int i, Rectangle r, List<RectangleWithCondition> profileCandidates) {
    // check profile first

    DisjointConditionalProfile profile = new DisjointConditionalProfile();

    for (int j = 0; j < r.dim; j++) {
      if (j != i && r.length[i].min() != 0) {

        profile.make(j, i, r, profileCandidates, exclusionList);

        if (!profile.isEmpty()) {
          if (traceOn) {
            log.debug(" *** {}\n{}", r, profileCandidates);
            log.debug("Profile in dimension {} and {}\n{}", i, j, profile);
          }

          profileCheckRectangle(profile, r, i, j);
        }
      }
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
      int j = 0;
      Rectangle[] toEvaluate = ((DisjointCondVarValue) evalRects[i].value()).rects;
      while (sat && j < toEvaluate.length) {
        rectj = toEvaluate[j];
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

    result.append(" : disjointConditional( ");

    int i = 0;
    for (Rectangle rectangle : rectangles) {
      result.append(rectangle);
      if (i < rectangles.length - 1) {
        result.append(", ");
      }
      i++;
    }

    result.append(", ").append(exclusionList).append(")");

    return result.toString();
  }
}
