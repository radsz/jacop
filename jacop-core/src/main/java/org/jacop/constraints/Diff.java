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

import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.Builder;
import org.jacop.core.IntVar;

/**
 * Diff constraint assures that any two rectangles from a vector of rectangles does not overlap in
 * at least one direction. It is a simple implementation which does not use sophisticated techniques
 * for efficient backtracking.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Diff extends AbstractDiff {

  static final AtomicInteger idNumber = new AtomicInteger(0);

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

    if (rectangles == null) {
      throw new IllegalArgumentException("Rectangles list is null");
    }

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
        o1.toArray(IntVar[]::new),
        o2.toArray(IntVar[]::new),
        l1.toArray(IntVar[]::new),
        l2.toArray(IntVar[]::new));
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
  void narrowRectangles(Set<IntVar> fdvQueue) {
    narrowRectanglesEval(null, fdvQueue, false, true);
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
    for (Rectangle r : rectangles) {
      result.append(r);
      if (i < rectangles.length - 1) {
        result.append(", ");
      }
      i++;
    }
    return result.append(")").toString();
  }
}
