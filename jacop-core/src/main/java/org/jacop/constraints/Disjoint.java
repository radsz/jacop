/*
 * Disjoint.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.Builder;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Disjoint constraint assures that any two rectangles from a vector of rectangles does not overlap
 * in at least one direction.
 *
 * <p>Zero-width rectangles does not overlap with any other rectangle.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
@Slf4j
public class Disjoint extends Diff {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  Diff2Var[] evalRects;

  /**
   * @param rectangles a list of rectangles.
   * @param doProfile should profile be computed and used.
   */
  public Disjoint(Rectangle[] rectangles, boolean doProfile) {

    checkInputForNullness("rectangles", rectangles);
    checkInput(rectangles, r -> r.dim == 2, "rectangle has to have exactly two dimensions");

    this.queueIndex = 2;

    this.rectangles = Arrays.copyOf(rectangles, rectangles.length);
    this.doProfile = doProfile;
    this.numberId = idNumber.incrementAndGet();

    setScope(Rectangle.getStream(this.rectangles));
  }

  /**
   * It creates a diff2 constraint.
   *
   * @param o1 list of variables denoting the origin in the first dimension.
   * @param o2 list of variables denoting the origin in the second dimension.
   * @param l1 list of variables denoting the length in the first dimension.
   * @param l2 list of variables denoting the length in the second dimension.
   * @param profile specifies if the profile should be computed.
   */
  public Disjoint(
      List<? extends IntVar> o1,
      List<? extends IntVar> o2,
      List<? extends IntVar> l1,
      List<? extends IntVar> l2,
      boolean profile) {
    this(o1, o2, l1, l2);
    doProfile = profile;
  }

  /**
   * It creates a diff2 constraint.
   *
   * @param rectangles list of rectangles with origins and lengths in both dimensions.
   */
  public Disjoint(List<? extends List<? extends IntVar>> rectangles) {

    queueIndex = 2;
    this.rectangles = Rectangle.toArrayOf2dRectangles(rectangles);
    numberId = idNumber.incrementAndGet();

    setScope(Rectangle.getStream(this.rectangles));
  }

  /**
   * It creates a diff2 constraint.
   *
   * @param rectangles list of rectangles with origins and lengths in both dimensions.
   * @param profile specifies if the profile is computed and used.
   */
  public Disjoint(List<? extends List<? extends IntVar>> rectangles, boolean profile) {
    this(rectangles);
    doProfile = profile;
  }

  /**
   * It creates a diff2 constraint.
   *
   * @param o1 list of variables denoting the origin in the first dimension.
   * @param o2 list of variables denoting the origin in the second dimension.
   * @param l1 list of variables denoting the length in the first dimension.
   * @param l2 list of variables denoting the length in the second dimension.
   */
  public Disjoint(
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
   * It creates a diff2 constraint.
   *
   * @param origin1 list of variables denoting the origin in the first dimension.
   * @param origin2 list of variables denoting the origin in the second dimension.
   * @param length1 list of variables denoting the length in the first dimension.
   * @param length2 list of variables denoting the length in the second dimension.
   */
  public Disjoint(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {

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
   * It creates a diff2 constraint.
   *
   * @param o1 list of variables denoting the origin in the first dimension.
   * @param o2 list of variables denoting the origin in the second dimension.
   * @param l1 list of variables denoting the length in the first dimension.
   * @param l2 list of variables denoting the length in the second dimension.
   * @param profile specifies if the profile should be computed.
   */
  @Builder(builderMethodName = "disjointBuilder")
  public Disjoint(IntVar[] o1, IntVar[] o2, IntVar[] l1, IntVar[] l2, boolean profile) {
    this(o1, o2, l1, l2);
    doProfile = profile;
  }

  /**
   * It creates a diff2 constraint.
   *
   * @param rectangles list of rectangles with origins and lengths in both dimensions.
   */
  public Disjoint(IntVar[][] rectangles) {

    assert (rectangles != null) : "Rectangles list is null";

    queueIndex = 2;
    this.rectangles = Rectangle.toArrayOf2dRectangles(rectangles);
    numberId = idNumber.incrementAndGet();

    setScope(Rectangle.getStream(this.rectangles));
  }

  /**
   * It creates a diff2 constraint.
   *
   * @param rectangles list of rectangles with origins and lengths in both dimensions.
   * @param profile specifies if the profile is computed and used.
   */
  public Disjoint(IntVar[][] rectangles, boolean profile) {
    this(rectangles);
    doProfile = profile;
  }

  public void impose(Store store) {

    super.impose(store);

    evalRects = new Diff2Var[rectangles.length];

    for (int j = 0; j < evalRects.length; j++) {
      evalRects[j] = new Diff2Var(store, rectangles);
    }
  }

  @Override
  void narrowRectangles(Set<IntVar> fdvQueue) {

    boolean needToNarrow = false;

    for (int l = 0; l < rectangles.length; l++) {
      Rectangle r = rectangles[l];

      boolean settled = true;
      boolean minLengthEq0 = false;
      int maxLevel = 0;
      for (int i = 0; i < r.dim(); i++) {
        IntDomain rOrigin = r.origin[i].dom();
        IntDomain rLength = r.length[i].dom();
        settled = settled && rOrigin.singleton() && rLength.singleton();

        minLengthEq0 = minLengthEq0 || (rLength.min() < 0);

        int originStamp = rOrigin.stamp;
        int lengthStamp = rLength.stamp;
        if (maxLevel < originStamp) {
          maxLevel = originStamp;
        }
        if (maxLevel < lengthStamp) {
          maxLevel = lengthStamp;
        }
      }

      if (!minLengthEq0
          && // Check for rectangle r which has
          // all lengths > 0
          !(settled && maxLevel < currentStore.level)) {
        // and are not fixed already

        needToNarrow = needToNarrow || containsChangedVariable(r, fdvQueue);

        List<IntRectangle> usedRect = new ArrayList<>();
        List<Rectangle> profileCandidates = new ArrayList<>();
        List<Rectangle> overlappingRects = new ArrayList<>();
        boolean ntN = findRectangles(r, l, usedRect, profileCandidates, overlappingRects, fdvQueue);

        needToNarrow = needToNarrow || ntN;

        // Checking r against all s with minUse in the domain of r
        if (needToNarrow) {

          if (overlappingRects.size() != ((Diff2VarValue) evalRects[l].value()).Rects.length) {
            Diff2VarValue newRects = new Diff2VarValue();
            newRects.setValue(overlappingRects);
            evalRects[l].update(newRects);
          }

          narrowRectangle(r, usedRect, profileCandidates);
        }
      }
    }
  }

  private boolean findRectangles(
      Rectangle r,
      int index,
      List<IntRectangle> usedRect,
      List<Rectangle> profileCandidates,
      List<Rectangle> overlappingRects,
      Set<IntVar> fdvQueue) {

    boolean contains = false;
    boolean checkArea = false;

    long area = 0;
    long commonArea = 0;
    int totalNumberOfRectangles = 0;
    int dim = r.dim();
    int[] startMin = new int[dim];
    int[] stopMax = new int[dim];
    int[] minLength = new int[dim];
    int[] r_min = new int[dim];
    int[] r_max = new int[dim];
    for (int i = 0; i < startMin.length; i++) {
      IntDomain rLengthDom = r.length[i].dom();
      startMin[i] = IntDomain.MaxInt;
      stopMax[i] = 0;
      minLength[i] = rLengthDom.min();

      IntDomain rOriginDom = r.origin[i].dom();
      r_min[i] = rOriginDom.min();
      r_max[i] = rOriginDom.max() + rLengthDom.max();
    }

    for (Rectangle s : ((Diff2VarValue) evalRects[index].value()).Rects) {
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
          if (start <= stop) {
            Use.add(start, stop - start);
            j++;
          } else {
            use = false;
          }

          minLength0 = minLength0 || (sLengthMin[m] <= 0);

          m++;
        }

        if (overlap) {

          overlappingRects.add(s);

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

              sArea = sArea * sLengthMin[i];
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

      if (availArea < area) {
        throw Store.failException;
      } else
      // check whether there is enough room for
      // all minimal rectangles
      if (rectNumber < (totalNumberOfRectangles + 1)) {
        throw Store.failException;
      }
    }

    return contains;
  }

  @Override
  void profileNarrowing(int i, Rectangle r, List<Rectangle> profileCandidates) {
    // check profile first

    IntDomain rOriginIdom = r.origin[i].dom();
    int rOriginIdomMin = rOriginIdom.min();
    int rOriginIdomMax = rOriginIdom.max();
    DiffnProfile profile = new DiffnProfile();

    for (int j = 0; j < r.dim; j++) {
      if (j != i && r.length[i].min() != 0) {

        profile.make(
            j, i, r, rOriginIdomMin, rOriginIdomMax + r.length[i].min(), profileCandidates);

        if (!profile.isEmpty()) {
          if (trace) {
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
      Rectangle[] toEvaluate = ((Diff2VarValue) evalRects[i].value()).Rects;
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

    result.append(" : disjoint( ");

    for (int i = 0; i < rectangles.length - 1; i++) {
      result.append(rectangles[i]);
      result.append(", ");
    }
    result.append(rectangles[rectangles.length - 1]);
    result.append(")");

    return result.toString();
  }
}
