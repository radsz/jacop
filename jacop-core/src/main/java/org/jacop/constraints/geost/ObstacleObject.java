/*
 * ObstacleObject.java
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

package org.jacop.constraints.geost;

import java.util.ArrayList;
import java.util.Arrays;
import org.jacop.core.IntDomain;

/**
 * This version of the ObstacleObject internal constraint allows the use of multiple d-boxes per
 * shape.
 *
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 * @version 5.0
 */
public class ObstacleObject extends ObstacleObjectFrame {

  /**
   * It shifts boxes of the given shape as required by the frame. It recomputed always when frame is
   * updated. It allows for faster execution in between frame updates.
   */
  final ArrayList<Dbox> preshiftedElems;

  final int[] lowerAbsInsfeasible;
  final int[] upperAbsInsfeasible;

  /**
   * It is a boolean switch which steers this constraint behavior. It is set to true as soon as
   * frame is not empty.
   */
  boolean frameExists;

  /**
   * It stores the information about the shape, so it does not always have to look for its value
   * inside the domain of shape variable.
   */
  int shapeId;

  /**
   * It constructs an internal constraint to constraint the objects not to overlap with this
   * obstacle object.
   *
   * @param geost the constraint for which this internal constraint has been created.
   * @param obstacle the obstacle object which is responsible for this constraint.
   * @param selectedDimensions the dimensions on which the constraint is applicable.
   */
  public ObstacleObject(Geost geost, GeostObject obstacle, int[] selectedDimensions) {

    super(geost, obstacle, selectedDimensions);

    preshiftedElems = new ArrayList<>();

    assert obstacle.shapeId.singleton()
        : "Polymorphism not supperted by this simple internal constraint. Use ObstacleObjectFrame instead.";

    shapeId = obstacle.shapeId.value();

    for (Dbox elem : geost.getShape(shapeId).boxes) {
      preshiftedElems.add(elem.copyInto(Dbox.newBox(obstacle.dimension)));
    }

    upperAbsInsfeasible = new int[obstacle.dimension + 1];
    lowerAbsInsfeasible = new int[obstacle.dimension + 1];
  }

  @Override
  public String checkInvariants() {

    if (super.checkInvariants() != null) {
      return super.checkInvariants();
    }

    if (obstacle == null) {
      return "obstacle field is null";
    }

    // make sure the selected dimensions are sorted and have correct values
    int previous = 0;
    for (int i = 0; i < selectedDimensions.length; i++) {
      if (i != 0 && selectedDimensions[i] <= previous) {
        return "selected dimensions "
            + Arrays.toString(selectedDimensions)
            + " are not sorted or not unique";
      }

      previous = selectedDimensions[i];

      if (!(selectedDimensions[i] >= 0 && selectedDimensions[i] <= obstacle.dimension)) {
        return "incorrect dimension: " + selectedDimensions[i];
      }
    }

    return null;
  }

  @Override
  public int[] absInfeasible(Geost.SweepDirection minlex) {

    if (frameExists) {
      return super.absInfeasible(minlex);
    } else {

      if (minlex == Geost.SweepDirection.PRUNEMAX) {
        return upperAbsInsfeasible;
      } else {
        return lowerAbsInsfeasible;
      }
    }
  }

  @Override
  public int cardInfeasible() {

    if (frameExists) {
      return super.cardInfeasible();
    } else {
      // rough approximation, but consistent among ObstacleObject constraint
      return 1;
    }
  }

  @Override
  public Dbox isFeasible(
      Geost.SweepDirection min,
      LexicographicalOrder order,
      GeostObject o,
      int currentShape,
      int[] c) {

    assert obstacle.shapeId.singleton()
        : "no support for polymorphism. Use ObstacleObjectFrame instead.";

    if (frameExists) {
      return super.isFeasible(min, order, o, currentShape, c);
    }
    if (o == obstacle) {
      return null;
    }
    if (!timeOnlyCheck(min, order, o, currentShape, c)) {
      return null;
    }
    if (!boundingBoxContainsPoint(c, currentShape)) {
      return null;
    }

    Dbox outBox = Dbox.getAllocatedInstance(obstacle.dimension + 1);
    outBox.origin[obstacle.dimension] = timeSizeOrigin;
    outBox.length[obstacle.dimension] = timeSizeMax - timeSizeOrigin;

    return findOverlappingOutbox(c, currentShape, outBox);
  }

  private boolean boundingBoxContainsPoint(int[] c, int currentShape) {
    Dbox obstacleBb = geost.getShape(shapeId).boundingBox;
    Dbox otherBb = geost.getShape(currentShape).boundingBox;
    int selectedDimIndex = 0;
    for (int i = 0; i < obstacle.dimension; i++) {
      int outDimOrigin;
      int outDimLength;
      if (selectedDimIndex < selectedDimensions.length
          && selectedDimensions[selectedDimIndex] == i) {
        selectedDimIndex++;
        outDimOrigin =
            obstacleBb.origin[i]
                + obstacle.coords[i].max()
                - otherBb.origin[i]
                - otherBb.length[i]
                + 1;
        final int max =
            obstacleBb.origin[i]
                + obstacleBb.length[i]
                + obstacle.coords[i].min()
                - otherBb.origin[i];
        outDimLength = max - outDimOrigin;
        if (outDimLength <= 0) {
          return false;
        }
      } else {
        outDimOrigin = IntDomain.MIN_INT;
        outDimLength = IntDomain.MAX_INT - IntDomain.MIN_INT;
      }
      if (c[i] < outDimOrigin || c[i] >= outDimOrigin + outDimLength) {
        return false;
      }
    }
    return true;
  }

  private Dbox findOverlappingOutbox(int[] c, int currentShape, Dbox outBox) {
    int[] outOrigin = outBox.origin;
    int[] outLength = outBox.length;
    for (Dbox constrainedPiece : geost.getShape(currentShape).boxes) {
      for (Dbox preshift : preshiftedElems) {
        boolean useless = fillOutBoxForPiecePair(outOrigin, outLength, constrainedPiece, preshift);
        assert useless || outBox.checkInvariants() == null : outBox.checkInvariants();
        if (!useless && outBox.containsPoint(c)) {
          return outBox;
        }
      }
    }
    return null;
  }

  private boolean fillOutBoxForPiecePair(
      int[] outOrigin, int[] outLength, Dbox constrainedPiece, Dbox preshift) {
    int selectedDimIndex = 0;
    boolean useless = false;
    for (int i = 0; i < obstacle.dimension; i++) {
      if (selectedDimIndex < selectedDimensions.length
          && selectedDimensions[selectedDimIndex] == i) {
        selectedDimIndex++;
        outOrigin[i] =
            preshift.origin[i] - constrainedPiece.origin[i] - constrainedPiece.length[i] + 1;
        final int max = preshift.length[i] - constrainedPiece.origin[i];
        outLength[i] = max - outOrigin[i];
        if (outLength[i] <= 0) {
          useless = true;
        }
      } else {
        outOrigin[i] = IntDomain.MIN_INT;
        outLength[i] = IntDomain.MAX_INT - IntDomain.MIN_INT;
      }
    }
    return useless;
  }

  @Override
  public String toString() {

    return "ObstacleObject(o" + obstacle.no + ", " + Arrays.toString(selectedDimensions) + ")";
  }

  @Override
  public void updateFrame() {

    // note: frameIsUsed is undefined until the first call to this function (done at initialization)

    super.updateFrame();

    if (frame.isEmpty()) {

      frameExists = false;
      int currentIndex = 0;

      for (Dbox elem : geost.getShape(shapeId).boxes) {

        Dbox preshift = preshiftedElems.get(currentIndex);

        for (int i = 0; i < obstacle.dimension; i++) {
          preshift.origin[i] = elem.origin[i] + obstacle.coords[i].max();
          preshift.length[i] = elem.origin[i] + elem.length[i] + obstacle.coords[i].min();
        }

        currentIndex++;
      }

      // update absolute infeasible points
      Dbox bb = geost.getShape(shapeId).boundingBox;

      for (int i = 0; i < obstacle.dimension; i++) {
        upperAbsInsfeasible[i] = obstacle.coords[i].min() + bb.origin[i] + bb.length[i];
        lowerAbsInsfeasible[i] = obstacle.coords[i].max() + bb.origin[i];
      }

      upperAbsInsfeasible[obstacle.dimension] = IntDomain.MAX_INT;
      lowerAbsInsfeasible[obstacle.dimension] = IntDomain.MIN_INT;

    } else {
      frameExists = true;
    }

    assert checkInvariants() == null : checkInvariants();
  }
}
