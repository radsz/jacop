/**
 *  SimpleBacktrackableManager.java 
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

import java.util.ArrayList;

import org.jacop.util.SparseSet;

/**
 * It is responsible of remembering what variables have changed at given
 * store level. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class SimpleBacktrackableManager implements BacktrackableManager {

	/**
	 * It specifies the current level which is active in the manager.
	 */
	public int currentLevel;
	
	/**
	 * It specifies the actual number of objects in the objects array.
	 */
	int noOfObjects;
	
	/**
	 * It contains indexes of objects changed at active level. It may
	 * be empty if trailContainsAllChanges is set to true. 
	 */
	SparseSet currentlyChanged;
	
	/**
	 * It specifies a trail. A recorded changes which will be used upon 
	 * backtracking to inform the objects about backtracking.  
	 */
	ArrayList< int [] > trail;
	
	/**
	 * It specifies the levels of the store for which trails are stored.
	 */
	ArrayList< Integer > levelInfo;
	
	/**
	 * It specifies the cutoff value after which a trail is no longer stored
	 * and recovery of the old state is done by informing all the variables 
	 * about the backtracking.
	 */
	int cutOffValue;
	
	/**
	 * It stores objects which change has to be restored upon backtracking. The 
	 * positions of objects will be stored by the manager and all changed objects
	 * will have their function removeLevel() be called.
	 */
	public Backtrackable[] objects;
	
	/**
	 * It specifies if for the current level the all changes are already 
	 * stored in the trail. This situation occurs after each backtrack. 
	 * If new changes are added then this flag indicates that trail has to 
	 * be used. 
	 */
	public boolean trailContainsAllChanges;
	
	/**
	 * It specifies if for the current level we have reached the cutoff value.
	 */
	public boolean currentLevelMax;
	
	/**
	 * It is a fake variable to distinguish between empty levels and 
	 * full levels.
	 */
	final int [] emptyLevel;
	
	/**
	 * It is a fake variable to disinguish between full levels and 
	 * empty ones.
	 */
	final int [] fullLevel;
	
	/**
	 * It specifies if the debugging information should be displayed.
	 */
	final boolean debug = false;
	
	/**
	 * It constructs a trail manager. 
	 * 
	 * @param noOfObjects it specifies number of objects being managed.
	 * @param vars it specifies the list of objects being managed.
	 */
	
	public SimpleBacktrackableManager(Backtrackable[] vars, 
									  int noOfObjects) {
	
		assert (noOfObjects <= vars.length) : "More objects than array is holding.";
		
		this.noOfObjects = noOfObjects;
		currentlyChanged = new SparseSet(vars.length);
		cutOffValue = Math.max(noOfObjects / 50, 20);
		trailContainsAllChanges = false;
		currentLevelMax = false;
		objects = (Backtrackable[]) vars;
		trail = new ArrayList<int[]>();
		levelInfo = new ArrayList<Integer>();
		emptyLevel = new int[0];
		fullLevel = new int[0];
		assert (emptyLevel != fullLevel) : "Code needs to be changed.";
	}
	
	/**
	 * It allows to inform the manager that a given item with id (index) has changed at given level. 
	 * 
	 * @param index it specifies the index  of the object which has changed.
	 */
	public void addChanged(int index) {
				
		if (debug)
			System.out.println(this + "Add item " + index + "max reached " + currentLevelMax);

		if (currentLevelMax)
			return;

		if (trailContainsAllChanges) {
			trailContainsAllChanges = false;
			currentlyChanged.clear();

			int lastLevel = levelInfo.remove( levelInfo.size() - 1 );
			
			assert (lastLevel == currentLevel);
			// currentLevel = lastLevel;
			
			int [] lastTrail = trail.remove( trail.size() - 1);

			
			if (lastTrail == fullLevel) {
				currentLevelMax = true;
				return;
			}
				
			if (lastTrail != emptyLevel)
				for (int i : lastTrail)
					currentlyChanged.addMember(i);
			
		}

		currentlyChanged.addMember(index);
		
		if (currentlyChanged.members > cutOffValue)
			currentLevelMax = true;
		
	}

	/**
	 * It specifies the level which should become the active one in the manager.
	 * @param level the active level at which the changes will be recorded.
	 */
	public void setLevel(int level) {

		if (currentLevel == level)
			return;
		
		if (debug)
			System.out.println(">" + this + "Add level " + level);

		assert (level > currentLevel) : "It is possible only to add higher levels";

		if( level > currentLevel && !trailContainsAllChanges) {
		// store old level
			if (currentlyChanged.members <= cutOffValue &&
				!currentlyChanged.isEmpty()) {
				// remember the trail. 
				int [] trailLevel = new int[currentlyChanged.members];
				System.arraycopy(currentlyChanged.dense, 
								 0, 
								 trailLevel, 
								 0, 
								 currentlyChanged.members);
				trail.add(trailLevel);
			}
			else {
				// do remove level by checking all variables.
				// @TODO, later implement intervals functionality.
				if (!currentlyChanged.isEmpty())
					trail.add(fullLevel);
				else
					trail.add(emptyLevel);
			}
			
			levelInfo.add(currentLevel);
			
		}

		currentlyChanged.clear();
		trailContainsAllChanges = false;
		currentLevelMax = false;
		currentLevel = level;

		if (debug)
			System.out.println("<" + this + "Add level " + level + "\n");

	}
		
	/**
	 * It allows to inform all objects which have changed at removedLevel
	 * that the backtracking from that level has occurred.
	 * 
	 * @param removedLevel it specifies the level which is being removed.
	 */
	public void removeLevel(int removedLevel) {
	
		if (debug)
			System.out.println(">" + this + "Remove level " + removedLevel + " current level " + currentLevel);
		
		if (currentLevel == removedLevel) {
			
			if (trailContainsAllChanges) {
				int lastLevel = levelInfo.remove( levelInfo.size() - 1 );
				assert (lastLevel == removedLevel) :
					"It is only possible to remove recently added level";
			
				int [] lastTrail = trail.remove( trail.size() - 1);
			
				if (lastTrail != emptyLevel && lastTrail != fullLevel)
					for (int i : lastTrail)
						objects[i].remove(removedLevel);
				
				if (lastTrail == fullLevel)
					for (int i = noOfObjects - 1; i >= 0; i--)
						objects[i].remove(removedLevel);
			
			}
			else {
				
				if (!currentLevelMax) {
					if (!currentlyChanged.isEmpty())
						for (int i = currentlyChanged.members; i >= 0; i--)
							objects[ currentlyChanged.dense[i] ].remove(removedLevel);
				}
				else {
					for (int i = noOfObjects - 1; i >= 0; i--)
						objects[i].remove(removedLevel);
				}

				trailContainsAllChanges = true;
				currentlyChanged.clear();
			}

			if (!levelInfo.isEmpty())
				currentLevel = levelInfo.get(levelInfo.size() - 1);
			else
				currentLevel = 0;
			
			currentLevelMax = false;
			if (!trail.isEmpty())
				if (trail.get( trail.size() - 1) == fullLevel) {
					currentLevelMax = true;
				}			
			
		}

		if (debug)
			System.out.println("<" + this + "Remove level " + removedLevel + "\n");

		assert (removedLevel >= currentLevel) : "It is only possible to remove the most recent not removed level";

	}
	
	/**
	 * It specifies how many objects within objects array are being actually 
	 * managed. It allows to specify partially empty array. 
	 * 
	 * @param size the number of objects in the array.
	 */
	public void setSize(int size) {
		
		noOfObjects = size;
		cutOffValue = Math.max(noOfObjects / 50, 20);

		assert (noOfObjects <= objects.length) : "It can not set the size larger than the length of the object array";
		
	} 
	
	public String toString() {
		StringBuffer result = new StringBuffer();
		
		result.append("Level ").append(currentLevel).append("\n");
		result.append("Levels ").append(levelInfo).append("\n");
		result.append("Last trail").append(currentlyChanged).append("\n");
		result.append("Last stored trail ");
		
		if (levelInfo.size() > 0)
			result.append("stored for ").append(levelInfo.get(levelInfo.size() - 1)).append(" ");
		if (trail.size() > 0) {
			int [] lastTrail = trail.get(trail.size() - 1);
			if (lastTrail == emptyLevel)
				result.append(" Empty ");
			if (lastTrail == fullLevel)
				result.append(" Full ");
			for (int i : lastTrail)
				result.append( i ).append(" ");
			result.append("\n");
		}
		
		return result.toString();
		
	}
	
	/**
	 * It allows for easy testing if a given object is considered by 
	 * the manager as the object which has changed and needs being 
	 * informed about backtracking. 
	 * 
	 * @param index the position of the object which status is in question.
	 * @return it returns true if the manager recognizes object at position index as changed one. 
	 */
	public boolean isRecognizedAsChanged(int index) {
		
		if (currentLevelMax)
			return true;
		
		if (trailContainsAllChanges) {
			
			int [] trailLevel = trail.get(trail.size() - 1);
			
			for (int i : trailLevel)
				if (i == index)
					return true;
			
			return false;
			
		} else {
		
			// SparseSet contains all changes for the current level.
			return currentlyChanged.isMember(index);
			
		}
		
		
	}

	public int getLevel() {
		return currentLevel;
	}

	
	public void update(Backtrackable[] objects, int noOfObjects) {
		
		assert (noOfObjects <= objects.length) : "More objects than array is holding.";
		assert (this.objects.length < objects.length) : "Can not update with a smaller array as trail will not work";
		assert (this.noOfObjects < noOfObjects) : "Making number of objects smaller will make trail work incorrectly.";
		
		this.noOfObjects = noOfObjects;
		
		SparseSet replacement = new SparseSet(objects.length);
		System.arraycopy(currentlyChanged.dense, 0, replacement.dense, 0, currentlyChanged.dense.length);
		System.arraycopy(currentlyChanged.sparse, 0, replacement.sparse, 0, currentlyChanged.sparse.length);
		currentlyChanged = replacement;
		
		cutOffValue = Math.max(noOfObjects / 50, 20);
		
		this.objects = objects;
	}
	
	
}
