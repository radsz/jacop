/*
 * InArea.java
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

/**
 * InArea constraint allows on to define an area within which objects should be contained, as well
 * as a collection of "holes" within the area.
 *
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 * @version 5.0
 */
public class InArea implements ExternalConstraint {

  /** It specifies the allowed area in which the objects can reside. */
  final Dbox allowedArea;

  /** It specifies the holes within the allowed area in which the objects can not be placed. */
  public final Collection<Dbox> holes;

  /** It holds all the constraints which have been generated from this external constraints. */
  public Set<InternalConstraint> constraints;

  /**
   * It constructs an external constraint to enforce that all objects within Geost constraint are
   * placed within a specified area with holes in that area specfied as well.
   *
   * @param area the specification of the area within which the objects have to be placed.
   * @param holes the holes in which the objects can not be placed.
   */
  public InArea(Dbox area, Collection<Dbox> holes) {

    this.allowedArea = area;
    this.holes = Objects.requireNonNullElseGet(holes, () -> new ArrayList<>(0));

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /**
   * It checks whether the InArea is consistent.
   *
   * @return It returns the string description of the problem, or null if no problem with data
   *     structure consistency encountered.
   */
  public String checkInvariants() {

    if (holes == null) {
      return "uninitialized holes set";
    }

    if (this.allowedArea == null) {
      return "allowed area is not defined";
    }

    return null;
  }

  /** {@inheritDoc} */
  public Collection<InternalConstraint> genInternalConstraints(Geost geost) {

    constraints = new HashSet<>(holes.size() + 1);

    constraints.add(new AllowedArea(geost, allowedArea.origin, allowedArea.length));

    for (Dbox hole : holes) {
      constraints.add(new ForbiddenArea(geost, hole.origin, hole.length));
    }

    return constraints;
  }

  @Override
  public boolean addPrunableObjects(GeostObject o, Set<GeostObject> accumulator) {
    // whatever object has been changed this constraint will not cause
    // any new pruning of any objects in the scope of this constraint.
    return false;
  }

  /** {@inheritDoc} */
  public void onObjectUpdate(GeostObject o) {
    // nothing to do here, as the external constraint does not have any state changing due to
    // updating any object.
  }

  /** {@inheritDoc} */
  public Collection<InternalConstraint> getObjectConstraints(GeostObject o) {
    // all objects are in the scope of this constraint and each object is constrained in the same
    // manner.
    return constraints;
  }

  /** {@inheritDoc} */
  public boolean isInternalConstraintApplicableTo(InternalConstraint ic, GeostObject o) {

    if (ic.getClass() != AllowedArea.class && ic.getClass() != ForbiddenArea.class) {
      return false;
    } else {
      return constraints.contains(ic);
    }
  }

  /** {@inheritDoc} */
  public GeostObject[] getObjectScope() {
    return null;
  }

  /** {@inheritDoc} */
  public String toString() {
    return "(in_area: " + allowedArea + " - holes(" + holes + "))";
  }
}
