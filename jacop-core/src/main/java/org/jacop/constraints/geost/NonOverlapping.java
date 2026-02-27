/*
 * NonOverlapping.java
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
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

/**
 * External constraint for geost ensuring objects do not overlap.
 *
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 * @version 5.0
 */
public class NonOverlapping implements ExternalConstraint {

  /** It specifies the objects which are being in the scope of this external constraint. */
  final GeostObject[] objects;

  /**
   * The dimensions (from 0 to dimension-1) on which the constraint applies. To consider time,
   * include dimension in the array
   */
  final int[] selectedDimensions;

  /** It maps object (through object.id) to the internal constraint connected to this object. */
  ObstacleObjectFrame[] objectConstraintMap;

  // For a moment not really needed, if the dead code inside function
  // isInternalConstraintApplicableTo
  // is removed then this attribute can be removed too.
  Set<InternalConstraint> constraints;

  /**
   * It creates an external constraint to make sure that specified set of objects does not overlap
   * in k-dimensional space on the given number of selected dimensions within this k-dimensional
   * space.
   *
   * @param objects the set of objects which can not overlap
   * @param selectedDimensions the dimensions among which there must be at least one for which the
   *     objects do not overlap.
   */
  public NonOverlapping(GeostObject[] objects, int[] selectedDimensions) {

    this.objects = objects;

    // use a copy for safety, and sort it for easier use
    this.selectedDimensions = new int[selectedDimensions.length];
    System.arraycopy(selectedDimensions, 0, this.selectedDimensions, 0, selectedDimensions.length);
    Arrays.sort(this.selectedDimensions);

    objectConstraintMap = null;
    constraints = null;
  }

  /**
   * It creates an external constraint to make sure that specified set of objects does not overlap
   * in k-dimensional space on the given number of selected dimensions within this k-dimensional
   * space.
   *
   * @param objects the set of objects which can not overlap
   * @param selectedDimensions the dimensions among which there must be at least one for which the
   *     objects do not overlap.
   */
  public NonOverlapping(Collection<GeostObject> objects, int[] selectedDimensions) {

    this(objects.toArray(new GeostObject[0]), selectedDimensions);
  }

  @Override
  public boolean addPrunableObjects(GeostObject o, Set<GeostObject> accumulator) {

    boolean changed = false;

    for (GeostObject oc : objects) {
      if (oc != o) {
        changed = true;
        accumulator.add(oc);
      }
    }

    return changed;
  }

  /** {@inheritDoc} */
  public Collection<InternalConstraint> genInternalConstraints(Geost geost) {

    if (objectConstraintMap == null) {

      // find largest object ID
      int largestId = 0;
      for (GeostObject o : objects) {
        largestId = Math.max(largestId, o.no);
      }

      objectConstraintMap = new ObstacleObjectFrame[largestId + 1];
      Arrays.fill(objectConstraintMap, null);

      constraints = new HashSet<>();

      for (GeostObject o : objects) {

        ObstacleObjectFrame c;

        if (geost.alwaysUseFrames || !o.shapeId.singleton()) {
          c = new ObstacleObjectFrame(geost, o, selectedDimensions);
        } else {
          c = new ObstacleObject(geost, o, selectedDimensions);
        }

        objectConstraintMap[o.no] = c;
        constraints.add(c);
      }
    }

    return constraints;
  }

  /** {@inheritDoc} */
  public void onObjectUpdate(GeostObject o) {

    /*
     * This is where we update the object's constraint
     */
    if (o.no < objectConstraintMap.length && objectConstraintMap[o.no] != null) {
      objectConstraintMap[o.no].updateFrame();
    }
  }

  /** {@inheritDoc} */
  public Collection<InternalConstraint> getObjectConstraints(GeostObject o) {

    Collection<InternalConstraint> relatedConstraints = new ArrayList<>();

    if (o.no < objectConstraintMap.length && objectConstraintMap[o.no] != null) {

      // if the object is not concerned by this constraint, no constraints should be added
      // using an array causes this lookup to be a bit more costly, due to holes, but method is used
      // only once
      for (int i = objectConstraintMap.length - 1; i >= 0; i--) {
        ObstacleObjectFrame c = objectConstraintMap[i];
        if (c != null) {
          relatedConstraints.add(c);
        }
      }
    }

    return relatedConstraints;
  }

  /** {@inheritDoc} */
  public boolean isInternalConstraintApplicableTo(InternalConstraint ic, GeostObject o) {

    return getObjectConstraints(o).contains(ic);
  }

  /** {@inheritDoc} */
  public GeostObject[] getObjectScope() {
    return objects;
  }

  /** {@inheritDoc} */
  @Override
  public String toString() {

    return "(non_overlapping: "
        + Arrays.asList(objects)
        + ", "
        + "selected_dimensions: "
        + Arrays.toString(selectedDimensions)
        + ")";
  }
}
