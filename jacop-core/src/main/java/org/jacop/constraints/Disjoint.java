/*
 * Disjoint.java
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
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Disjoint constraint assures that any two rectangles from a vector of rectangles does not overlap
 * in at least one direction.
 *
 * <p>Zero-width rectangles does not overlap with any other rectangle.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Disjoint extends Diff {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  Diff2Var[] evalRects;

  /**
   * Constructs a Disjoint constraint ensuring rectangles do not overlap.
   *
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
        o1.toArray(IntVar[]::new),
        o2.toArray(IntVar[]::new),
        l1.toArray(IntVar[]::new),
        l2.toArray(IntVar[]::new));
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

    if (rectangles == null) {
      throw new IllegalArgumentException("Rectangles list is null");
    }

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

  /**
   * Imposes the constraint in the constraint store.
   *
   * @param store the constraint store in which the constraint is imposed.
   */
  @Override
  public void impose(Store store) {

    super.impose(store);

    evalRects = new Diff2Var[rectangles.length];

    for (int j = 0; j < evalRects.length; j++) {
      evalRects[j] = new Diff2Var(store, rectangles);
    }
  }

  @Override
  void narrowRectangles(Set<IntVar> fdvQueue) {
    narrowRectanglesEval(evalRects, fdvQueue, true, true);
  }

  @Override
  void profileNarrowing(int i, Rectangle r, List<Rectangle> profileCandidates) {
    // check profile first

    DiffnProfile profile = new DiffnProfile();

    for (int j = 0; j < r.dim; j++) {
      if (j != i && r.length[i].min() != 0) {

        profile.make(j, i, r, profileCandidates);

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
    return satisfiedEval(evalRects);
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
