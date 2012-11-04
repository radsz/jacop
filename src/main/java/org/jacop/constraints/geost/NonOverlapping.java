/**
 *  NonOverlapping.java 
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
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;

import org.jacop.util.SimpleHashSet;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 */
public class NonOverlapping implements ExternalConstraint {

	
	/**
	 * It specifies the objects which are being in the scope of this external constraint.
	 */
	public final GeostObject[] objects;
	
	
	/**
	 * It maps object (through object.id) to the internal constraint connected to this object.
	 */
	public ObstacleObjectFrame[] objectConstraintMap;
	
	// For a moment not really needed, if the dead code inside function isInternalConstraintApplicableTo
	// is removed then this attribute can be removed too.
	HashSet<ObstacleObjectFrame> constraints;
	
	/**
	 * the dimensions (from 0 to dimension-1) on which the constraint applies. To consider time,
	 * include dimension in the array
	 */
	public final int[] selectedDimensions;
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"objects", "selectedDimensions"};

	/**
	 * It creates an external constraint to make sure that specified set of objects does not overlap
	 * in k-dimensional space on the given number of selected dimensions within this k-dimensional space.
	 * 
	 * @param objects the set of objects which can not overlap
	 * @param selectedDimensions the dimensions among which there must be at least one for which the objects do not overlap. 
	 */
	public NonOverlapping(GeostObject[] objects, 
						  int[] selectedDimensions) {
		
		this.objects = objects;
		
		//use a copy for safety, and sort it for easier use
		this.selectedDimensions = new int[selectedDimensions.length];
		System.arraycopy(selectedDimensions, 0, this.selectedDimensions, 0, selectedDimensions.length);
		Arrays.sort(this.selectedDimensions);
		
		objectConstraintMap = null; //TODO replace by an array/SimpleArrayList
		constraints = null;
	
	}

	/**
	 * It creates an external constraint to make sure that specified set of objects does not overlap
	 * in k-dimensional space on the given number of selected dimensions within this k-dimensional space.
	 * 
	 * @param objects the set of objects which can not overlap
	 * @param selectedDimensions the dimensions among which there must be at least one for which the objects do not overlap. 
	 */
	public NonOverlapping(Collection<GeostObject> objects, 
						  int[] selectedDimensions) {
		
		this(objects.toArray(new GeostObject[objects.size()]), 
			 selectedDimensions);
	}
	
	
	public boolean addPrunableObjects(GeostObject o, SimpleHashSet<GeostObject> accumulator) {
		
		boolean changed = false;
	
		for(GeostObject oc : objects)
			if(oc != o) {
				changed = true;
				accumulator.add(oc);
			}
		
		return changed;
		
	}

	
	public Collection<ObstacleObjectFrame> genInternalConstraints(Geost geost) {
		
		if(objectConstraintMap == null) {
			
			//find largest object ID
			int largestID = 0;
			for(GeostObject o : objects)
				largestID = Math.max(largestID, o.no);
			
			objectConstraintMap = new ObstacleObjectFrame[largestID + 1];
			Arrays.fill(objectConstraintMap, null);
			
			constraints = new HashSet<ObstacleObjectFrame>();
			
			for(GeostObject o : objects) {
				
				ObstacleObjectFrame c;
				
				if(geost.alwaysUseFrames || !o.shapeID.singleton())
					c = new ObstacleObjectFrame(geost, o, selectedDimensions);
				else
					c = new ObstacleObject(geost, o, selectedDimensions);
				
				objectConstraintMap[o.no] = c;
				constraints.add(c);
			}
		}
	
		return  constraints;
	}

	
	public void onObjectUpdate(GeostObject o) {

		/*
		 * This is where we update the object's constraint
		 */
		if(o.no < objectConstraintMap.length && objectConstraintMap[o.no] != null)
			objectConstraintMap[o.no].updateFrame();

	}

	
	public Collection<? extends InternalConstraint> getObjectConstraints(GeostObject o) {
		
		Collection<InternalConstraint> relatedConstraints = new ArrayList<InternalConstraint>();
		
		if(o.no < objectConstraintMap.length && objectConstraintMap[o.no] != null) {

			//if the object is not concerned by this constraint, no constraints should be added
			//using an array causes this lookup to be a bit more costly, due to holes, but method is used only once
			for(int i = objectConstraintMap.length-1; i >= 0; i--) {
				ObstacleObjectFrame c = objectConstraintMap[i];
				if( c != null)
					relatedConstraints.add(c);
			}
			
		}
		
		return relatedConstraints;
	}

	
	public boolean isInternalConstraintApplicableTo(InternalConstraint ic, GeostObject o) {
		
		final boolean inefficient = true;
		
		// TODO, do we keep inefficient version? If so, attribute constraints is no longer needed.
		if(inefficient)
			return getObjectConstraints(o).contains(ic);
		else {

			// TODO, Potentially a bug after introducing inheritance between ObstacleObject and ObstacleObjectFrame.
			if(ic.getClass() != ObstacleObjectFrame.class)
				return false;
			else {
				InternalConstraint oc = objectConstraintMap[o.no];
				return oc != null && ic != oc && constraints.contains(ic);
			}
			
		}
	}

	public GeostObject[] getObjectScope() {
		return objects;
	}

}
