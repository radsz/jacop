/*
 * Diff2.java
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
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.Builder;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Diff2 constraint assures that any two rectangles from a vector of rectangles does not overlap in
 * at least one direction.
 *
 * <p>Zero-width rectangles can be packed anywhere.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Diff2 extends Diff {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies a list of pairs of rectangles which can overlap. */
  private int[] exclusiveList = new int[0];

  Diff2Var[] evalRects;
  boolean exceptionListPresent;

  /**
   * Conditional Diff2. The rectangles that are specified on the list Exclusive list is specified
   * contains pairs of rectangles that are excluded from checking that they must be non-overlapping.
   * The rectangles are numbered from 1, for example list [1, 3, 3, 4] specifies that rectangles 1
   * and 3 as well as 3 and 4 can overlap each other.
   *
   * @param rectangles a list of rectangles.
   * @param exclusiveList a list denoting the pair of rectangles, which can overlap
   * @param doProfile should profile be computed and used.
   */
  public Diff2(Rectangle[] rectangles, int[] exclusiveList, boolean doProfile) {

    checkInputForNullness("rectangles", rectangles);
    checkInputForNullness("exlusiveList", exclusiveList);
    checkInput(rectangles, i -> i.dim == 2, "rectangle should have exactly two dimensions");

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();

    this.rectangles = Arrays.copyOf(rectangles, rectangles.length);
    this.exclusiveList = Arrays.copyOf(exclusiveList, exclusiveList.length);
    this.doProfile = doProfile;
    exceptionListPresent = true;

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
  public Diff2(
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
  public Diff2(List<? extends List<? extends IntVar>> rectangles) {

    queueIndex = 2;
    this.rectangles = Rectangle.toArrayOf2dRectangles(rectangles);
    numberId = idNumber.incrementAndGet();

    setScope(rectangles.stream().flatMap(Collection::stream));
  }

  /**
   * It creates a diff2 constraint.
   *
   * @param rectangles list of rectangles with origins and lengths in both dimensions.
   * @param profile specifies if the profile is computed and used.
   */
  public Diff2(List<? extends List<? extends IntVar>> rectangles, boolean profile) {
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
  public Diff2(
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
  public Diff2(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {

    checkInputForNullness(
        new String[] {"origin1", "origin2", "length1", "length2"},
        origin1,
        origin2,
        length1,
        length2);

    queueIndex = 2;
    this.rectangles = Rectangle.toArrayOf2dRectangles(origin1, origin2, length1, length2);
    numberId = idNumber.incrementAndGet();

    setScope(origin1, origin2, length1, length2);
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
  @Builder(builderMethodName = "diff2Builder")
  public Diff2(IntVar[] o1, IntVar[] o2, IntVar[] l1, IntVar[] l2, boolean profile) {
    this(o1, o2, l1, l2);
    doProfile = profile;
  }

  /**
   * It creates a diff2 constraint.
   *
   * @param rectangles list of rectangles with origins and lengths in both dimensions.
   */
  public Diff2(IntVar[][] rectangles) {

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
  public Diff2(IntVar[][] rectangles, boolean profile) {
    this(rectangles);
    doProfile = profile;
  }

  /**
   * Conditional Diff2. The rectangles that are specified on the list Exclusive are excluded from
   * checking that they must be non-overlapping. The rectangles are numbered from 1, for example
   * list [[1,3], [3,4]] specifies that rectangles 1 and 3 as well as 3 and 4 can overlap each
   * other.
   *
   * @param rectangles - list of rectangles, each rectangle represented by a list of variables.
   * @param exclusiveList - list of rectangles pairs which can overlap.
   */
  public Diff2(List<List<? extends IntVar>> rectangles, List<List<Integer>> exclusiveList) {

    queueIndex = 2;
    this.rectangles = Rectangle.toArrayOf2dRectangles(rectangles);
    numberId = idNumber.incrementAndGet();

    exceptionListPresent = true;

    List<Integer> list = new ArrayList<>(exclusiveList.size() * 2);

    for (List<Integer> pair : exclusiveList) {
      list.addAll(pair);
    }

    this.exclusiveList = new int[list.size()];
    for (int i = 0; i < list.size(); i++) {
      this.exclusiveList[i] = list.get(i);
    }

    setScope(rectangles.stream().flatMap(Collection::stream));
  }

  /**
   * Conditional Diff2. The rectangles that are specified on the list Exclusive are excluded from
   * checking that they must be non-overlapping. The rectangles are numbered from 1, for example
   * list [[1,3], [3,4]] specifies that rectangles 1 and 3 as well as 3 and 4 can overlap each
   * other.
   *
   * @param rect - list of rectangles, each rectangle represented by a list of variables.
   * @param exclusive - list of rectangles pairs which can overlap.
   */
  public Diff2(IntVar[][] rect, List<List<Integer>> exclusive) {

    queueIndex = 2;
    this.rectangles = Rectangle.toArrayOf2dRectangles(rect);
    numberId = idNumber.incrementAndGet();

    exceptionListPresent = true;

    List<Integer> list = new ArrayList<>(exclusive.size() * 2);

    for (List<Integer> pair : exclusive) {
      list.addAll(pair);
    }

    this.exclusiveList = new int[list.size()];
    for (int i = 0; i < list.size(); i++) {
      this.exclusiveList[i] = list.get(i);
    }

    setScope(Rectangle.getStream(this.rectangles));
  }

  private Rectangle[] onList(int index, int[] exclusiveList) {

    List<Rectangle> list = new ArrayList<>();

    for (int i = 0; i < rectangles.length; i++) {
      if (notOverlapping(index + 1, i + 1, exclusiveList)) {
        list.add(rectangles[i]);
      }
    }

    return list.toArray(new Rectangle[0]);
  }

  boolean notOverlapping(int i, int j, int[] exclusiveList) {

    boolean onList = false;
    int l = 0;

    while (!onList && l < exclusiveList.length / 2) {
      int el1 = exclusiveList[l * 2];
      int el2 = exclusiveList[l * 2 + 1];

      onList = (i == el1 && j == el2) || (i == el2 && j == el1);
      l++;
    }

    return !onList;
  }

  @Override
  public void impose(Store store) {

    super.impose(store);

    if (this.exclusiveList.length == 0) {
      evalRects = new Diff2Var[rectangles.length];

      for (int j = 0; j < evalRects.length; j++) {
        evalRects[j] = new Diff2Var(store, this.rectangles);
      }
    } else {

      evalRects = new Diff2Var[rectangles.length];

      for (int j = 0; j < evalRects.length; j++) {
        evalRects[j] = new Diff2Var(store, onList(j, exclusiveList));
      }
    }
  }

  @Override
  void narrowRectangles(Set<IntVar> fdvQueue) {
    narrowRectanglesEval(evalRects, fdvQueue, false, !exceptionListPresent);
  }

  @Override
  public boolean satisfied() {
    return satisfiedEval(evalRects);
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : diff2( ");

    for (int i = 0; i < rectangles.length - 1; i++) {
      result.append(rectangles[i]);
      result.append(", ");
    }
    result.append(rectangles[rectangles.length - 1]);
    result.append(")");

    return result.toString();
  }
}
