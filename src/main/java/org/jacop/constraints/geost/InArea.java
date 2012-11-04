/**
 *  InArea.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
package org.jacop.constraints.geost;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.jacop.util.SimpleHashSet;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 *
 * InArea constraint allows on to define an area within which objects
 * should be contained, as well as a collection of "holes" within the area
 * 
 * TODO implement the use of a subset of objects only. In some applications,
 * classes of objects may need to be placed in different portions of the space.
 * Possibly, create class InAreaSetOfObjects extending from InArea to allow 
 * specification of the objects in the focus of the constraint.
 * 
 */

public class InArea implements ExternalConstraint {

	/**
	 * It specifies the allowed area in which the objects can reside.
	 */
	public DBox allowedArea;
	
	/**
	 * It specifies the holes within the allowed area in which 
	 * the objects can not be placed.
	 */
	public Collection<DBox> holes;
	
	/**
	 * It holds all the constraints which have been generated from this external constraints.
	 */
	public Set<InternalConstraint> constraints;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"allowedArea", "holes"};

	/**
	 * It constructs an external constraint to enforce that all objects 
	 * within Geost constraint are placed within a specified area with 
	 * holes in that area specfied as well. 
	 * 
	 * @param area the specification of the area within which the objects have to be placed.
	 * @param holes the holes in which the objects can not be placed.
	 */
	public InArea(DBox area, Collection<DBox> holes) {
		
		this.allowedArea = area;
		
		if( holes != null )
			this.holes = holes;
		else 
			this.holes = new ArrayList<DBox>(0);
		
		assert checkInvariants() == null : checkInvariants();
		
	}

	/**
	 * It checks whether the InArea is consistent.
	 * 
	 * @return It returns the string description of the problem, or null if no problem 
	 * with data structure consistency encountered. 
	 */
	public String checkInvariants() {
		
		if(holes == null)
			return "uninitialized holes set";
		
		if (this.allowedArea == null)
			return "allowed area is not defined";
		
		return null;
		
	}
	
	
	public Collection<InternalConstraint> genInternalConstraints(Geost geost) {
		
		constraints = new HashSet<InternalConstraint>( holes.size() + 1);
		
		constraints.add(new AllowedArea(geost, allowedArea.origin, allowedArea.length));
		
		for(DBox hole : holes)
			constraints.add(new ForbiddenArea(geost, hole.origin, hole.length));
		
		return constraints;
		
	}

	
	public boolean addPrunableObjects(GeostObject o,
				    				  SimpleHashSet<GeostObject> accumulator) {
		// whatever object has been changed this constraint will not cause 
		// any new pruning of any objects in the scope of this constraint.
		return false;
	}

	
	public void onObjectUpdate(GeostObject o) {
		// nothing to do here, as the external constraint does not have any state changing due to updating any object.
	}

	
	public Collection<? extends InternalConstraint> getObjectConstraints(GeostObject o) {
		// all objects are in the scope of this constraint and each object is constrained in the same manner.
		return constraints;
	}

	
	public boolean isInternalConstraintApplicableTo(InternalConstraint ic,
													GeostObject o) {
		
		if( ic.getClass() != AllowedArea.class && ic.getClass() != ForbiddenArea.class )
			return false;
		else 
			return constraints.contains(ic);
		
	}

	public GeostObject[] getObjectScope() {
		return null;
	}

}
