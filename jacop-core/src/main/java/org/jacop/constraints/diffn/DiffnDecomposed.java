/*
 * DiffnDecomposed.java
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
import java.util.List;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Max;
import org.jacop.constraints.Min;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
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
public class DiffnDecomposed extends DecomposedConstraint<Constraint> {

  protected final List<Var> auxVar = new ArrayList<>();
  final IntVar[] x;
  final IntVar[] y;
  final IntVar[] lx;
  final IntVar[] ly;
  protected List<Constraint> constraints;

  /**
   * It specifies a diffn constraint.
   *
   * @param rectangle list of rectangles which can not overlap in at least one dimension.
   */
  public DiffnDecomposed(IntVar[][] rectangle) {

    if (ASSERTS_ENABLED && rectangle == null) {
      throw new IllegalStateException(String.valueOf("Rectangles list is null"));
    }

    queueIndex = 2;

    x = new IntVar[rectangle.length];
    y = new IntVar[rectangle.length];
    lx = new IntVar[rectangle.length];
    ly = new IntVar[rectangle.length];

    for (int i = 0; i < rectangle.length; i++) {
      if (ASSERTS_ENABLED && rectangle[i] == null) {
        throw new IllegalStateException(String.valueOf(i + "-th rectangle in the list is null"));
      }
      if (ASSERTS_ENABLED && rectangle[i].length == 4) {
        throw new IllegalStateException(
            String.valueOf("The rectangle has to have exactly two dimensions"));
      }

      x[i] = rectangle[i][0];
      y[i] = rectangle[i][1];
      lx[i] = rectangle[i][2];
      ly[i] = rectangle[i][3];
    }
  }

  /**
   * It constructs a diffn constraint.
   *
   * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
   * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
   * @param length1 list of variables denoting length of the rectangle in the first dimension.
   * @param length2 list of variables denoting length of the rectangle in the second dimension.
   */
  public DiffnDecomposed(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {

    checkInputForNullness(
        new String[] {"origin1", "origin2", "length1", "length2"},
        origin1,
        origin2,
        length1,
        length2);

    int size = origin1.length;
    if (size == origin2.length && size == length1.length && size == length2.length) {

      this.queueIndex = 2;

      x = new IntVar[origin1.length];
      y = new IntVar[origin2.length];
      lx = new IntVar[length1.length];
      ly = new IntVar[length2.length];

      System.arraycopy(origin1, 0, x, 0, size);
      System.arraycopy(origin2, 0, y, 0, size);
      System.arraycopy(length1, 0, lx, 0, size);
      System.arraycopy(length2, 0, ly, 0, size);
    } else {
      String s = "\nNot equal sizes of Variable vectors in Nooverlap";
      throw new IllegalArgumentException(s);
    }
  }

  /**
   * It specifies a diffn constraint.
   *
   * @param rectangle list of rectangles which can not overlap in at least one dimension.
   */
  public DiffnDecomposed(List<? extends List<? extends IntVar>> rectangle) {

    if (ASSERTS_ENABLED && rectangle == null) {
      throw new IllegalStateException(String.valueOf("Rectangles list is null"));
    }

    this.queueIndex = 2;

    x = new IntVar[rectangle.size()];
    y = new IntVar[rectangle.size()];
    lx = new IntVar[rectangle.size()];
    ly = new IntVar[rectangle.size()];

    for (int i = 0; i < rectangle.size(); i++) {
      if (ASSERTS_ENABLED && rectangle.get(i) == null) {
        throw new IllegalStateException(String.valueOf(i + "-th rectangle in the list is null"));
      }
      if (ASSERTS_ENABLED && rectangle.get(i).size() == 4) {
        throw new IllegalStateException(
            String.valueOf("The rectangle has to have exactly two dimensions"));
      }

      x[i] = rectangle.get(i).getFirst();
      y[i] = rectangle.get(i).get(1);
      lx[i] = rectangle.get(i).get(2);
      ly[i] = rectangle.get(i).get(3);
    }
  }

  /**
   * It constructs a diffn constraint.
   *
   * @param x list of variables denoting origin of the rectangle in the first dimension.
   * @param y list of variables denoting origin of the rectangle in the second dimension.
   * @param lx list of variables denoting length of the rectangle in the first dimension.
   * @param ly list of variables denoting length of the rectangle in the second dimension.
   */
  public DiffnDecomposed(
      List<? extends IntVar> x,
      List<? extends IntVar> y,
      List<? extends IntVar> lx,
      List<? extends IntVar> ly) {

    this(
        x.toArray(IntVar[]::new),
        y.toArray(IntVar[]::new),
        lx.toArray(IntVar[]::new),
        ly.toArray(IntVar[]::new));
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

  /**
   * Decomposes the diffn constraint into a collection of simpler constraints including nooverlap
   * and cumulative constraints in both dimensions.
   *
   * @param store the constraint store
   * @return list of constraints representing the decomposition
   */
  @Override
  public List<Constraint> decompose(Store store) {
    constraints = new ArrayList<>();

    constraints.add(new Nooverlap(x, y, lx, ly));

    // add cumulative in x direction
    addCumulativeConstraints(store, constraints, y, ly, x, lx, "by", 0);

    // add cumulative in y direction
    addCumulativeConstraints(store, constraints, x, lx, y, ly, "bx", 1);

    return constraints;
  }

  /**
   * Adds cumulative constraints for a given direction.
   *
   * @param store the constraint store
   * @param result the list to add constraints to
   * @param origins the origin variables for this direction
   * @param lengths the length variables for this direction
   * @param otherOrigins the origin variables for the other direction (used in CumulativeBasic)
   * @param otherLengths the length variables for the other direction (used in CumulativeBasic)
   * @param suffix the suffix for variable names (e.g., "bx" or "by")
   * @param dim the dimension index (0 for x direction, 1 for y direction)
   */
  private void addCumulativeConstraints(
      Store store,
      List<Constraint> result,
      IntVar[] origins,
      IntVar[] lengths,
      IntVar[] otherOrigins,
      IntVar[] otherLengths,
      String suffix,
      int dim) {

    IntVar[] ends = new IntVar[origins.length];
    int min = IntDomain.MAX_INT;
    int max = IntDomain.MIN_INT;
    for (int i = 0; i < origins.length; i++) {
      min = Math.min(min, origins[i].min());
      max = Math.max(max, origins[i].max() + lengths[i].max());
      ends[i] =
          new IntVar(
              store, origins[i].min() + lengths[i].min(), origins[i].max() + lengths[i].max());
      result.add(new XplusYeqZ(origins[i], lengths[i], ends[i]));
      auxVar.add(ends[i]);
    }

    IntVar bMin = new IntVar(store, dim == 1 ? suffix + "Min" : null, min, max);
    IntVar bMax = new IntVar(store, dim == 1 ? suffix + "Max" : null, min, max);
    IntVar b = new IntVar(store, 0, max - min);
    auxVar.add(bMin);
    auxVar.add(bMax);
    auxVar.add(b);
    result.add(new Max(ends, bMax));
    result.add(new Min(origins, bMin));
    result.add(new XplusYeqZ(bMin, b, bMax));
    CumulativeBasic cc = new CumulativeBasic(otherOrigins, otherLengths, lengths, b);
    result.add(cc);
  }

  /**
   * Returns the list of auxiliary variables created during decomposition.
   *
   * @return list of auxiliary variables
   */
  @Override
  public List<Var> auxiliaryVariables() {
    return auxVar;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder();

    result.append("DiffnDecomposed(");

    for (int i = 0; i < x.length; i++) {
      result.append("[");
      result.append(x[i]);
      result.append(y[i]);
      result.append(lx[i]);
      result.append(ly[i]);
      result.append("]");
      if (i < x.length - 1) {
        result.append(", ");
      }
    }
    return result.append(")").toString();
  }
}
