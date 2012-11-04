/**
 *  GeostObject.java 
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

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 * It contains all information about the Geost object as well as functionality to 
 * maintain the consistency among time variables. 
 */

public class GeostObject {
	
	/**
	 * A unique identifier greater or equal to 0. The last object supplied to GeostConstraint
	 * should have an identifier equal to n-1, where n is the total number of objects.
	 */
	public final int no;
	
	/**
	 * It specifies the number of dimensions in this object.
	 */
	public final int dimension;
	
	/**
	 * It specifies the coordinates in k-dimensional space at which the object is fixed. 
	 * It is the origin of the object. The actual starting point of the object depends
	 * at the end also on the shape used by the object or in particular the origins of 
	 * the boxes which constitutes the shape. 
	 */
	public final IntVar[] coords;
	
	/**
	 * It specifies the possible shape ids to be taken by this object.
	 */
	public final IntVar shapeID;
	
	/**
	 * It specifies the start time of this object in time dimension.
	 */
	public final IntVar start;
	
	/**
	 * It specifies the duration time of this object. 
	 */
	public final IntVar duration;
	
	/**
	 * It specifies the end time of this object.
	 */
	public final IntVar end;
	
	/**
	 * It stores all finite domain variables in connection to this object. E.g. shape variables
	 * are one of the objects in the focus of the constraint.
	 */
	public final ArrayList<Var> variables;

	/**
	 * It specifies the time constraint to execute to ensure that start + duration = end.
	 */
	TimeBoundConstraint timeConstraint;
		
	/**
	 * For each dimension, the shape ID that provided the minimal lower bound or the maximal upperBound
	 */
	int[] bestShapeID;
	
	/**
	 * It specifies the number of variables currently grounded.
	 */
	int groundCount;

	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"no", "coords", "shapeID", "start", 
											"duration", "end"};

	/**
	 * 
	 * It constructs a Geost object with all the attributes needed by the Geost
	 * constraint. 
	 * 
	 * @param no nonnegative unique id of this object. 
	 * @param coords an array of variables representing the origin (start) of the objects.
	 * @param shapeID the variable specifying the shape finite domain variable.
	 * @param start it determines the start time of the geost object in terms of time.
	 * @param duration finite domain variable specifying the duration of the geost object in terms of time.
	 * @param end 
	 */
	public GeostObject(int no, IntVar[] coords, IntVar shapeID, IntVar start,
						IntVar duration, IntVar end) {
		
		dimension = coords.length;
		this.no = no;
		this.coords = coords;
		this.shapeID = shapeID;
		this.start = start;
		this.duration = duration;
		this.end = end;
		
		variables = new ArrayList<Var>();
		
		for(int i = 0; i < dimension; i++)
			variables.add(coords[i]);
		
		variables.add(shapeID);
		variables.add(start);
		variables.add(duration);
		variables.add(end);
		
		this.timeConstraint = new TimeBoundConstraint();
		
		bestShapeID = new int[dimension+1];//+1 because of time
		for(int i = 0; i < dimension+1; i++)
			bestShapeID[i] = shapeID.min();
		
		
		groundCount = 0;
		
	}
	
	/**
	 * It returns finite domain variables which belong to this object.
	 * 
	 * @return variables that constitute this object.
	 */
	public Collection<Var> getVariables() {
		return variables;
	}
	
	/**
	 * It is executed as soon as any object variable is grounded. 
	 * @param variable variable being grounded.
	 */
	public final void onGround(Var variable) {
		assert variables.contains(variable) : "grounding " + variable + ", not variable defining " + this;
		groundCount++;
		assert groundCount <= variables.size();
	}
	
	/**
	 * It is executed as soon as backtracking has occurred making previously grounded variable ungrounded again. 
	 * 
	 * @param variable variable being ungrounded.
	 */
	public final void onUnGround(Var variable){
		assert variables.contains(variable) : "ungrounding " + variable + ", not variable defining " + this;
		groundCount--;
		assert groundCount >= 0;
		
	}
	
	/**
	 * It checks whether the object location is fixed. 
	 * 
	 * @return true if the object location is fixed, false otherwise.
	 */
	public final boolean isGrounded(){
		return groundCount == variables.size();
	}

	public String toString(){
		
		StringBuilder builder = new StringBuilder();
		builder.append("Object(");
		builder.append(shapeID).append(", ");
		builder.append(Arrays.toString(coords)).append(", ");
		builder.append(start).append(", ");
		builder.append(duration).append(", ");
		builder.append(end);
		builder.append(")");
		
		return builder.toString();
		
	}
	
	/**
	 * @author Marc-Olivier Fleury and Radoslaw Szymanek
	 *
	 * It contains facility to keep the domain of time variables consistent. 
	 */
	public class TimeBoundConstraint {

		
		/**
		 * TODO, is it really needed this constructor?
		 */
		public TimeBoundConstraint() {
		}
				
		/**
		 * It evaluates part of the constraint that ensures that start + duration = end
		 * @param store
		 * @return true if some variable was changed, false otherwise
		 */
		public boolean consistencyStartPlusDurationEqEnd(Store store) {
			
			boolean updated = false;

			do {
				
				store.propagationHasOccurred = false;
			
				if (start.singleton()) {

					duration.domain.inShift(store.level, duration, end.domain, -start.value());
					end.domain.inShift(store.level, end, duration.domain, start.value());

				} else if (duration.singleton()) {

					start.domain.inShift(store.level, start, end.domain, -duration.value());
					end.domain.inShift(store.level, end, start.dom(), duration.value());

				} else {
					
					start.domain.in(store.level, start, end.min() - duration.max(), end.max()
							- duration.min());
					
					duration.domain.in(store.level, duration, end.min() - start.max(), end.max()
							- start.min());
					
					end.domain.in(store.level, end, start.min() + duration.min(), start.max()
							+ duration.max());
				
				}
				
				if(store.propagationHasOccurred)
					updated = true;
				
			} while (store.propagationHasOccurred);

			return updated;
		}
		
		/**
		 * It applies constraint enforcing that duration > 0
		 * 
		 * @param store constraint store in which the geost constraint is imposed at.
		 * @return true if a variable was updated, false otherwise
		 */
		public boolean consistencyDurationGtZero(Store store) {

			store.propagationHasOccurred = false;
			duration.domain.inMin(store.level, duration, 1);
			return store.propagationHasOccurred;
			
		}
		
		@Override
		public String toString(){
			
			StringBuilder result = new StringBuilder();
			result.append("TimeBoundConstraint( ").append(start).append(" + ");
			result.append(duration).append(" = ").append(end).append(" )");
			
			return result.toString();
		}

		/**
		 * It returns the corresponding object for which this time constraint corresponds to.
		 * 
		 * @return GeostObject to which this time constraint is connected to.
		 */
		public final GeostObject getCorrespondingObject() {
			return GeostObject.this;
		}
		
	}

}
