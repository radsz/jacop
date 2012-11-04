/**
 *  BacktrackableManager.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *  Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.core;

/**
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 *
 */
public interface BacktrackableManager {

		/**
		 * It allows to inform the manager that a given item with id (index) has changed at given level. 
		 * 
		 * @param index it specifies the index  of the object which has changed.
		 */
		void addChanged(int index);

		/**
		 * It specifies the level which should become the active one in the manager.
		 * @param level the active level at which the changes will be recorded.
		 */
		void setLevel(int level);
			
		/**
		 * It allows to inform all objects which have changed at removedLevel
		 * that the backtracking from that level has occurred.
		 * 
		 * @param removedLevel it specifies the level which is being removed.
		 */
		void removeLevel(int removedLevel);
		
		/**
		 * It specifies how many objects within objects array are being actually 
		 * managed. It allows to specify partially empty array. 
		 * 
		 * @param size the number of objects in the array.
		 */
		void setSize(int size);

		/**
		 * It allows for easy testing if a given object is considered by 
		 * the manager as the object which has changed and needs being 
		 * informed about backtracking. 
		 * 
		 * @param index the position of the object which status is in question.
		 * @return it returns true if the manager recognizes object at position index as changed one. 
		 */
		boolean isRecognizedAsChanged(int index);
		
		/**
		 * It returns the current level at which the changes are being registered.
		 * @return the active level for which the changes are being registered.
		 */
		int getLevel();
	
		/**
		 * It updates the manager with new array of objects to manage and new number of them. 
		 * This function works properly only during model creation phase, so manager can learn
		 * about freshly created objects. If used during search then the old array must be part
		 * of the new array to allow manager work properly. 
		 * @param objects a new array of objects
		 * @param noOfObjects number of objects in the new array to be taken care of. 
		 */
		
		void update(Backtrackable[] objects, int noOfObjects);
		
}
