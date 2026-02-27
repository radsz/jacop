/*
 * ObstacleObjectFrame.java
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.ListIterator;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * This version of the ObstacleObject internal constraint allows the use of multiple d-boxes per
 * shape.
 *
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 * @version 5.0
 */
public class ObstacleObjectFrame extends InternalConstraint {

  static final boolean DISPLAY_FRAME = false;

  // Non-static: set from instance method computeFrame; shared-display concerns are handled
  // externally.
  BoxDisplay display;

  /** It specifies the geost constraint to which this internal constraint belongs to. */
  final Geost geost;

  /** It specifies the geost objection which is the foundation of this obstacle constraint. */
  final GeostObject obstacle;

  /** The selected dimensions are sorted, they were sorted by NonOverlapping external constraint. */
  final int[] selectedDimensions;

  /** It specifies if the time dimension is used within computation. */
  final boolean useTime;

  /**
   * The collection of holes that are included in all possible shapes, enlarged to include the whole
   * domain that can be covered for any feasible choice of the origin.
   */
  private final ArrayList<Dbox> extendedHoles;

  /**
   * The frame is the area that is ensured to be covered by the obstacle, given the domain of its
   * origin variables.
   */
  public LinkedList<Dbox> frame;

  int timeSizeOrigin;
  int timeSizeMax;

  /** It specifies the bounding box of the frame. */
  private Dbox frameBoundingBox;

  /** It computes the area/volume of the frame. */
  private int frameArea;

  /**
   * It creates an internal constraint to enforce non-overlapping relation with this obstacle
   * object.
   *
   * @param geost the geost constraint which this constraint is part of.
   * @param obstacle the obstacle object responsible for this internal constraint.
   * @param selectedDimensions the dimensions on which the constraint is applied
   */
  public ObstacleObjectFrame(Geost geost, GeostObject obstacle, int[] selectedDimensions) {

    this.obstacle = obstacle;

    this.geost = geost;

    this.selectedDimensions = selectedDimensions;

    // check whether time should be used or not
    useTime = selectedDimensions[selectedDimensions.length - 1] == obstacle.dimension;

    extendedHoles = new ArrayList<>();
  }

  /**
   * It checks that this constraint has consistent data structures.
   *
   * @return a string describing the consistency problem with data structures, null if no problem
   *     encountered.
   */
  public String checkInvariants() {

    if (frame == null) {
      return "frame is null";
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

  /** Creates the frame if it does not exist, and clears it if it does. */
  private void clearFrame() {

    if (frame != null) {

      for (Dbox b : frame) {
        Dbox.dispatchBox(b);
      }
      frame.clear();

    } else {
      frame = new LinkedList<>();
      frameBoundingBox = Dbox.newBox(obstacle.dimension);
    }

    frameArea = 0;
  }

  /**
   * Updates the frame given the current values of the object coordinate variables. This method
   * should be called whenever some of the coordinate variables of the associated object change.
   */
  public void updateFrame() {

    if (geost.backtracking && obstacle.isGrounded()) {
      return;
    }

    ensureDisplayReady();
    Dbox domain = Dbox.newBox(obstacle.dimension);
    boolean[] holesExistRef = new boolean[1];
    Dbox boundingBox = computeIntersectionBoundingBox(domain, holesExistRef);
    if (boundingBox == null) {
      return;
    }

    if (!fillDomainFromBoundingBox(domain, boundingBox)) {
      return;
    }
    Dbox.dispatchBox(boundingBox);

    if (!holesExistRef[0]) {
      clearFrame();
      frame.add(domain);
      frameArea = domain.area();
    } else {
      updateFrameWithHoles(domain);
    }

    if (DISPLAY_FRAME) {
      for (Dbox framePiece : frame) {
        display.display2dBox(framePiece, Color.red);
      }
    }

    if (!frame.isEmpty()) {
      Dbox.boundingBox(frame).copyInto(frameBoundingBox);
    }
    frameArea = 0;
    for (Dbox frameComponent : frame) {
      frameArea += frameComponent.area();
    }
    if (!frame.isEmpty()) {
      frameArea++;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  private void ensureDisplayReady() {
    if (!DISPLAY_FRAME) {
      return;
    }
    if (display == null) {
      display = new BoxDisplay(5, obstacle.toString());
    } else {
      display.eraseAll();
      display.setTitle(obstacle.toString());
      display.drawGrid(Color.lightGray);
    }
  }

  /** Returns intersection bounding box of all shapes, or null if empty. Sets holesExistRef[0]. */
  private Dbox computeIntersectionBoundingBox(Dbox domain, boolean[] holesExistRef) {
    Dbox boundingBox = null;
    ValueEnumeration vals = obstacle.shapeId.domain.valueEnumeration();
    boolean firstIter = true;
    while (vals.hasMoreElements()) {
      int sid = vals.nextElement();
      Shape shape = geost.getShape(sid);
      if (!shape.holes().isEmpty()) {
        holesExistRef[0] = true;
      }
      Dbox shapeBoundingBox = shape.boundingBox();
      if (firstIter) {
        boundingBox = shapeBoundingBox.copyInto(Dbox.newBox(obstacle.dimension));
        firstIter = false;
      } else {
        Dbox inter = boundingBox.intersectWith(shapeBoundingBox);
        if (inter != null) {
          inter.copyInto(boundingBox);
        } else {
          clearFrame();
          Dbox.dispatchBox(domain);
          Dbox.dispatchBox(boundingBox);
          return null;
        }
      }
    }
    return boundingBox;
  }

  /** Fills domain from bounding box. Returns false if domain is invalid (empty). */
  private boolean fillDomainFromBoundingBox(Dbox domain, Dbox boundingBox) {
    for (int i = 0; i < obstacle.dimension; i++) {
      IntVar coordVar = obstacle.coords[i];
      domain.origin[i] = coordVar.max() + boundingBox.origin[i];
      domain.length[i] = coordVar.min() + boundingBox.length[i] - coordVar.max();
      if (domain.length[i] < 0) {
        clearFrame();
        Dbox.dispatchBox(domain);
        Dbox.dispatchBox(boundingBox);
        return false;
      }
    }
    return true;
  }

  private void updateFrameWithHoles(Dbox domain) {
    clearFrame();
    updateExtendedHoles();
    for (int i = 0; i < obstacle.dimension; i++) {
      domain.origin[i] = domain.origin[i] * 4 - 1;
      domain.length[i] = domain.length[i] * 4 + 2;
    }
    if (DISPLAY_FRAME) {
      displayShapesAndHolesForFrame(domain);
    }
    domain.subtractAll(extendedHoles, frame);
    rescaleFramePieces();
    for (Dbox b : extendedHoles) {
      Dbox.dispatchBox(b);
    }
    Dbox.dispatchBox(domain);
  }

  private void displayShapesAndHolesForFrame(Dbox domain) {
    ValueEnumeration vals2 = obstacle.shapeId.domain.valueEnumeration();
    while (vals2.hasMoreElements()) {
      int sid = vals2.nextElement();
      Shape shape = geost.getShape(sid);
      for (Dbox sp : shape.holes()) {
        display.display2dBox(sp, Color.orange);
      }
      for (Dbox b : shape.boxes) {
        display.display2dBox(b, Color.black);
      }
      Collection<Dbox> rescaledBoxes = new ArrayList<>(shape.boxes.size());
      for (Dbox b : shape.boxes) {
        int dim = b.origin.length;
        Dbox scaled = Dbox.newBox(dim);
        for (int i = 0; i < dim; i++) {
          scaled.origin[i] = b.origin[i] * 4;
          scaled.length[i] = b.length[i] * 4;
        }
        rescaledBoxes.add(scaled);
      }
      for (Dbox sb : rescaledBoxes) {
        display.display2dBox(sb, Color.magenta);
      }
    }
    for (Dbox sp : extendedHoles) {
      display.display2dBox(sp, Color.blue);
    }
    display.display2dBox(domain, Color.green);
  }

  private void rescaleFramePieces() {
    ListIterator<Dbox> iterator = frame.listIterator();
    int dim = obstacle.dimension;
    while (iterator.hasNext()) {
      Dbox piece = iterator.next();
      if (DISPLAY_FRAME) {
        display.display2dBox(piece, Color.gray);
      }
      boolean valid = true;
      for (int i = 0; valid && i < dim; i++) {
        if (piece.length[i] == 1) {
          valid = false;
          Dbox.dispatchBox(piece);
          iterator.remove();
        } else {
          int originMod = piece.origin[i] % 4;
          int end = piece.origin[i] + piece.length[i];
          int endMod = end % 4;
          piece.origin[i] =
              originMod == 3
                  ? (int) Math.ceil(piece.origin[i] / 4.0)
                  : (int) Math.floor(piece.origin[i] / 4.0);
          end = endMod <= 1 ? (int) Math.floor(end / 4.0) : (int) Math.ceil(end / 4.0);
          piece.length[i] = end - piece.origin[i];
        }
      }
    }
  }

  private void updateExtendedHoles() {

    /*
     * This can be further improved by updating the extended the holes in the only
     * dimension that changed.
     */
    extendedHoles.clear(); // DBoxes are not collected anyway

    final ValueEnumeration vals = obstacle.shapeId.domain.valueEnumeration();
    while (vals.hasMoreElements()) {
      int sid = vals.nextElement();

      Shape shape = geost.getShape(sid);

      for (Dbox hole : shape.holes()) {
        // define coverable domain
        Dbox extendedHole = Dbox.newBox(obstacle.dimension);
        int[] holeDomOrigin = extendedHole.origin;
        int[] holeDomSize = extendedHole.length;

        // preserve scaling by 4
        for (int i = 0; i < obstacle.dimension; i++) {
          IntVar coordVar = obstacle.coords[i];
          holeDomOrigin[i] = 4 * coordVar.min() + hole.origin[i];
          holeDomSize[i] = 4 * coordVar.max() + hole.length[i] - 4 * coordVar.min();
        }

        extendedHoles.add(extendedHole);
      }
    }
  }

  @Override
  public int[] absInfeasible(Geost.SweepDirection minlex) {
    int[] outPoint = Dbox.getAllocatedInstance(obstacle.dimension + 1).origin;

    if (frame.isEmpty()) {
      return null;
    }

    if (minlex == Geost.SweepDirection.PRUNEMAX) {
      Arrays.fill(outPoint, Integer.MIN_VALUE);
    } else {
      Arrays.fill(outPoint, Integer.MAX_VALUE);
    }

    fillAbsInfeasibleDimensions(minlex, outPoint);
    setAbsInfeasibleTimeDimension(minlex, outPoint);
    return outPoint;
  }

  private void fillAbsInfeasibleDimensions(Geost.SweepDirection minlex, int[] outPoint) {
    int selectedDimIndex = 0;
    for (int i = 0; i < obstacle.dimension; i++) {
      boolean relevant =
          selectedDimIndex < selectedDimensions.length && selectedDimensions[selectedDimIndex] == i;
      if (relevant) {
        selectedDimIndex++;
        outPoint[i] =
            minlex == Geost.SweepDirection.PRUNEMAX
                ? frameBoundingBox.origin[i] + frameBoundingBox.length[i]
                : frameBoundingBox.origin[i];
      } else {
        outPoint[i] =
            minlex == Geost.SweepDirection.PRUNEMAX ? Integer.MAX_VALUE : IntDomain.MIN_INT;
      }
    }
  }

  private void setAbsInfeasibleTimeDimension(Geost.SweepDirection minlex, int[] outPoint) {
    if (!useTime) {
      outPoint[obstacle.dimension] =
          minlex == Geost.SweepDirection.PRUNEMAX ? Integer.MAX_VALUE : IntDomain.MIN_INT;
      return;
    }
    int up = obstacle.end.max();
    int low = obstacle.start.min();
    if (up - low < 0) {
      outPoint[obstacle.dimension] = 0;
      return;
    }
    if (minlex == Geost.SweepDirection.PRUNEMAX && up == low) {
      up = low + 1;
    }
    outPoint[obstacle.dimension] = minlex == Geost.SweepDirection.PRUNEMIN ? low : up;
  }

  @Override
  public int cardInfeasible() {
    return frameArea;
  }

  @Override
  public Collection<Var> definingVariables() {

    Collection<Var> variables = new ArrayList<>(obstacle.dimension);

    variables.addAll(Arrays.asList(obstacle.coords).subList(0, obstacle.dimension));

    variables.add(obstacle.shapeId);
    variables.add(obstacle.start);
    variables.add(obstacle.duration);
    variables.add(obstacle.end);

    return variables;
  }

  /**
   * It checks if two objects overlap only in the time dimension.
   *
   * @param min the sweep direction for pruning.
   * @param order the lexicographical order for comparison.
   * @param o the geost object to check.
   * @param currentShape the current shape identifier.
   * @param c the coordinates array.
   * @return true if there is no overlap in time dimension, false otherwise.
   */
  protected boolean timeOnlyCheck(
      Geost.SweepDirection min,
      LexicographicalOrder order,
      GeostObject o,
      int currentShape,
      int[] c) {

    if (useTime) {
      // if there is no overlap in time, no need to continue
      if (min == Geost.SweepDirection.PRUNEMIN) {
        // largest possible origin when objects begin to overlap (infeasible)
        timeSizeOrigin = obstacle.start.max() - o.duration.min() + 1;
        // smallest possible end is when placed after the obstacle (feasible)
        if (ASSERTS_ENABLED
            && !(obstacle.start.min() + obstacle.duration.min() <= obstacle.end.min())) {
          throw new IllegalStateException(
              String.valueOf(
                  "time constraint not valid: "
                      + obstacle.start
                      + " + "
                      + obstacle.duration
                      + " <= "
                      + obstacle.end));
        }
        timeSizeMax = obstacle.end.min();
      } else {
        // PRUNEMAX: the outbox has to mark the upper limit of the possible domain (end variable)

        /* in the usual case (not time), we can simply prune the upper bound of the origin domain.
         * However, in this case, since the "length" changes, we really have to consider the maximal
         * ending time.
         */

        timeSizeOrigin = obstacle.start.max() + 1;
        if (ASSERTS_ENABLED
            && !(obstacle.start.min() + obstacle.duration.min() <= obstacle.end.min())) {
          throw new IllegalStateException("Assertion failed");
        }
        timeSizeMax = obstacle.end.min() + o.duration.min();
      }

      if (timeSizeMax - timeSizeOrigin <= 0) {
        return false;
      }

      // check if point is between bounds, if not return null
      // point cannot be contained in outbox, no need to continue
      return c[obstacle.dimension] >= timeSizeOrigin && c[obstacle.dimension] <= timeSizeMax;

    } else {
      // time is not included in the dimensions, thus the outbox covers the whole space
      timeSizeOrigin = IntDomain.MIN_INT;
      timeSizeMax = IntDomain.MAX_INT;
      return true;
    }
  }

  @Override
  public Dbox isFeasible(
      Geost.SweepDirection min,
      LexicographicalOrder order,
      GeostObject o,
      int currentShape,
      int[] c) {

    if (o == obstacle || frame.isEmpty()) {
      return null;
    }

    if (!timeOnlyCheck(min, order, o, currentShape, c)) {
      return null;
    }

    if (pointOutsideBoundingBox(c, geost.getShape(currentShape).boundingBox)) {
      return null;
    }

    return findContainingOutBox(currentShape, c);
  }

  private boolean pointOutsideBoundingBox(int[] c, Dbox otherBb) {
    int selectedDimIndex = 0;
    for (int i = 0; i < obstacle.dimension; i++) {
      int outDimOrigin;
      int outDimLength;
      if (selectedDimIndex < selectedDimensions.length
          && selectedDimensions[selectedDimIndex] == i) {
        selectedDimIndex++;
        outDimLength = frameBoundingBox.length[i] + otherBb.length[i] - 1;
        outDimOrigin = frameBoundingBox.origin[i] - (otherBb.length[i] - 1) - otherBb.origin[i];
      } else {
        outDimOrigin = IntDomain.MIN_INT;
        outDimLength = IntDomain.MAX_INT - IntDomain.MIN_INT;
      }
      if (c[i] < outDimOrigin || c[i] >= outDimOrigin + outDimLength) {
        return true;
      }
    }
    return false;
  }

  private Dbox findContainingOutBox(int currentShape, int[] c) {
    Dbox outBox = Dbox.getAllocatedInstance(obstacle.dimension + 1);
    int[] outOrigin = outBox.origin;
    int[] outLength = outBox.length;
    outOrigin[obstacle.dimension] = timeSizeOrigin;
    outLength[obstacle.dimension] = timeSizeMax - timeSizeOrigin;

    for (Dbox constrainedPiece : geost.getShape(currentShape).boxes) {
      for (Dbox framePiece : frame) {
        int selectedDimIndex = 0;
        for (int i = 0; i < obstacle.dimension; i++) {
          if (selectedDimIndex < selectedDimensions.length
              && selectedDimensions[selectedDimIndex] == i) {
            selectedDimIndex++;
            outLength[i] = framePiece.length[i] + constrainedPiece.length[i] - 1;
            outOrigin[i] =
                framePiece.origin[i]
                    - (constrainedPiece.length[i] - 1)
                    - constrainedPiece.origin[i];
          } else {
            outOrigin[i] = IntDomain.MIN_INT;
            outLength[i] = IntDomain.MAX_INT - IntDomain.MIN_INT;
          }
        }
        if (ASSERTS_ENABLED && outBox.checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(outBox.checkInvariants()));
        }
        if (outBox.containsPoint(c)) {
          return outBox;
        }
      }
    }
    return null;
  }

  @Override
  public String toString() {

    return "ObstacleObject(o"
        + obstacle.no
        + ", "
        + Arrays.toString(selectedDimensions)
        + ", "
        + frame.toString();
  }

  @Override
  public boolean isStatic() {
    // if obstacle object is grounded, frame will not change anymore
    return obstacle.isGrounded();
  }

  @Override
  public boolean isSingleUse() {
    return false;
  }
}
