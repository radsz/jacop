/**
 *  IntervalBasedBacktrackableManager.java 
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
import java.util.Arrays;

/**
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * 
 * This manager works as simple manager to the point when cutoff value for a list
 * is reached. The objects indexes are continously stored in a list, but they 
 * are stored in the trail only as a list of holes. There is a possibility to express
 * the maximum number of holes being registered as well as minimum size requirement
 * for hole. 
 *
 */
public class IntervalBasedBacktrackableManager extends SimpleBacktrackableManager {

	/**
	 * It specifies a trail. A recorded changes which will be used upon 
	 * backtracking to inform the objects about backtracking.  
	 */
	ArrayList< Boolean > intervalBasedTrail;
	
	int intervalCutOffValue;
	
	int maxNoOfIntervals;

	int minHoleSize;
	
	int minHoleSizeAfterSplit = 4;
	
	int [] currentIntervals;
	
	int [] temporaryArray;
	
	int removeCount = 0;
	
	/**
	 * It creates a interval based backtrackable manager. At some point, instead of storing a list of changed
	 * indexes the manager stores a fixed number of intervals representing objects which have not changed.
	 * 
	 * @param vars the number of objects. 
	 * @param noOfObjects the number of objects being handled.
	 * @param minHoleSize the minimum size of the hole to be registered.
	 * @param maxNoOfIntervals maximum number of holes (intervals) being registered.
	 */
	public IntervalBasedBacktrackableManager(Backtrackable[] vars,
											 int noOfObjects,
			 								 int minHoleSize, 
			 								 int maxNoOfIntervals) {
		
		super(vars, noOfObjects);
		
		assert (maxNoOfIntervals > 0) : "The maximal number of intervals must be positive integer.";

		this.minHoleSize = Math.max( minHoleSize, minHoleSizeAfterSplit);
		this.maxNoOfIntervals = maxNoOfIntervals;
		this.currentIntervals = new int[maxNoOfIntervals];
		this.temporaryArray = new int[maxNoOfIntervals * 2];
		this.intervalCutOffValue = Math.max(noOfObjects / 2, this.cutOffValue + 1);
		this.addingToIntervals = false;
		this.intervalBasedTrail = new ArrayList<Boolean>();

	}

	boolean addingToIntervals;
	
	Boolean valueFalse = new Boolean(false);
	
	Boolean valueTrue = new Boolean(true);
	
	@Override
	public void addChanged(int index) {
			
		if (debug)
			System.out.println(this + "Add item " + index + "max reached " + currentLevelMax);

		if (currentLevelMax)
			return;

		if (trailContainsAllChanges) {
			
			if (debug) {
				
				System.out.println("Level info " + levelInfo);
				System.out.println("Intervals? " + intervalBasedTrail);
				System.out.println("LastTrail " + trail.get(trail.size() - 1));
				System.out.println(super.toString());
				
			}
			
			trailContainsAllChanges = false;
			currentlyChanged.clear();

			levelInfo.remove( levelInfo.size() - 1 );
			addingToIntervals = intervalBasedTrail.remove( intervalBasedTrail.size() - 1);
			
			int [] lastTrail = trail.remove( trail.size() - 1);

			if (lastTrail == fullLevel) {
				currentLevelMax = true;
				return;
			}

			if (addingToIntervals) {
				// lastTrail is a list of intervals.
				currentIntervals = lastTrail;
				
				addChangedToInterval(index);
				
				if (!isRecognizedAsChanged(index))
					addChangedToInterval(index);
				
				assert ( isRecognizedAsChanged(index)) ;
				return;
			}
				
			if (lastTrail != emptyLevel)
				for (int i : lastTrail)
					currentlyChanged.addMember(i);
			
		}

		if (addingToIntervals) {
			addChangedToInterval(index);
		}
		else {
			currentlyChanged.addMember(index);
		
			if (currentlyChanged.members > intervalCutOffValue)
				currentLevelMax = true;
		}
		
		assert ( isRecognizedAsChanged(index)) ;

	}

	@Override
	public void setLevel(int level) {

		if (currentLevel == level)
			return;
		
		if (debug) {
			
			System.out.println("Level being set" + level);
			System.out.println("Last Level info " + levelInfo);
			System.out.println("Intervals? " + intervalBasedTrail);
			if (trail.size() != 0)
				System.out.println("LastTrail " + trail.get(trail.size() - 1));
			System.out.println(super.toString());
			
		}

		
		if (debug)
			System.out.println(">" + this + "Add level " + level);

		assert (level > currentLevel) : "It is possible only to add higher levels";

		if (addingToIntervals) {
			intervalBasedTrail.add(valueTrue);
			trail.add( currentIntervals );
			levelInfo.add(currentLevel);
		}
		else
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
			
				intervalBasedTrail.add(valueFalse);
				
			}
			else {
				// do remove level by checking all variables.
				// @TODO, later implement intervals functionality.
				
				if (currentlyChanged.members <= intervalCutOffValue &&
					!currentlyChanged.isEmpty() ) {
					intervalBasedTrail.add(valueTrue);
					trail.add( computeIntervals() );
				}
				else {
					intervalBasedTrail.add(valueFalse);
					if (!currentlyChanged.isEmpty())
						trail.add(fullLevel);
					else
						trail.add(emptyLevel);
				}
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
	
	
	private int[] computeIntervals() {
				
		int noOfIntervals = maxNoOfIntervals * 2;
		
		Arrays.sort(currentlyChanged.dense, 0, currentlyChanged.members);
		
		int [] dense = currentlyChanged.dense;
		int noOfElements = currentlyChanged.members;
		
		if (noOfObjects - dense[noOfElements - 1] > minHoleSize) {
			temporaryArray[--noOfIntervals] = noOfObjects;
			temporaryArray[--noOfIntervals] = dense[noOfElements - 1] + 1;
		}
					
		for (int i = currentlyChanged.members; i >= 1 && noOfIntervals >= 2; i--) {
			
			if (currentlyChanged.dense[i] - currentlyChanged.dense[i-1] > minHoleSize) {
				temporaryArray[--noOfIntervals] = currentlyChanged.dense[i] - 1;
				temporaryArray[--noOfIntervals] = currentlyChanged.dense[i-1] + 1;				
			}
			
		}

		if (dense[0] > minHoleSize) {
			if ( noOfIntervals == 0 ) { 
				 if ( dense[0] > temporaryArray[1] - temporaryArray[0]) {
					 temporaryArray[1] = dense[0] - 1;
					 temporaryArray[0] = 0;
				 }	 
			} else {
				temporaryArray[--noOfIntervals] = dense[0] - 1;
				temporaryArray[--noOfIntervals] = 0;
			}
		}
		
		
		if ( maxNoOfIntervals * 2 - noOfIntervals != 0) {
			int[] result = new int[maxNoOfIntervals * 2 - noOfIntervals];
			System.arraycopy(temporaryArray, noOfIntervals, result, 0, result.length);
		
			return result;
		}
		else
			return fullLevel;

	}

	/**
	 * It allows to inform all objects which have changed at removedLevel
	 * that the backtracking from that level has occurred.
	 * 
	 * @param removedLevel it specifies the level which is being removed.
	 */
	@Override
	public void removeLevel(int removedLevel) {
	
		removeCount++;
		
		if (debug)
			System.out.println("Remove level count " + removeCount);
		
		if (debug)
			System.out.println(">" + this + "Remove level " + removedLevel + " current level " + currentLevel);
		
		if (currentLevel == removedLevel) {
			
			if (trailContainsAllChanges) {
				int lastLevel = levelInfo.remove( levelInfo.size() - 1 );
				
				assert (lastLevel == removedLevel) :
					"It is only possible to remove recently added level";
			
				int [] lastTrail = trail.remove( trail.size() - 1);
				
				if (intervalBasedTrail.remove( intervalBasedTrail.size() - 1) ) {

					// interval based representation for removed level.
					int currentPositionInHoles = 0;
					int left = 0;
					
					while(true) {
					
						while (currentPositionInHoles < lastTrail.length 
							   && lastTrail[currentPositionInHoles] == -1)
							currentPositionInHoles += 2;
						
						if (currentPositionInHoles == lastTrail.length)
							break;
						
						if (left < lastTrail[currentPositionInHoles])
							for (int i = left; i < lastTrail[currentPositionInHoles]; i++)
								objects[i].remove(removedLevel);				

						left = lastTrail[currentPositionInHoles+1] + 1;
						
						currentPositionInHoles += 2;
					} 
					
					for (int j = left; j < noOfObjects; j++)
						objects[j].remove(removedLevel);				
					
				} // non-interval based representation.
				else {
					
					if (lastTrail != emptyLevel && lastTrail != fullLevel)
						for (int i : lastTrail)
							objects[i].remove(removedLevel);
				
					if (lastTrail == fullLevel)
						for (int i = noOfObjects - 1; i >= 0; i--)
							objects[i].remove(removedLevel);
				}
				
			}
			else {

				if (addingToIntervals) {
					
					int currentPositionInHoles = 0;
					int left = 0;
					
					while(true) {
					
						while (currentPositionInHoles < currentIntervals.length 
							   && currentIntervals[currentPositionInHoles] == -1)
							currentPositionInHoles += 2;
						
						if (currentPositionInHoles == currentIntervals.length)
							break;
						
						if (left < currentIntervals[currentPositionInHoles])
							for (int i = left; i < currentIntervals[currentPositionInHoles]; i++)
								objects[i].remove(removedLevel);				

						left = currentIntervals[currentPositionInHoles+1] + 1;
						
						currentPositionInHoles += 2;
					} 
					
					for (int j = left; j < noOfObjects; j++)
						objects[j].remove(removedLevel);				
				
				
				} else { // non adding to intervals.

					if (!currentLevelMax) {
						if (!currentlyChanged.isEmpty())
							for (int i = currentlyChanged.members; i >= 0; i--)
								objects[ currentlyChanged.dense[i] ].remove(removedLevel);
					}	
					else {
						for (int i = noOfObjects - 1; i >= 0; i--)
							objects[i].remove(removedLevel);
					}
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
			
			addingToIntervals = false;
		}

		if (debug)
			System.out.println("<" + this + "Remove level " + removedLevel + "\n");

		assert (removedLevel >= currentLevel) : "It is only possible to remove the most recent not removed level";

		if ( checkRemoveInvariant(removedLevel) != null)
			System.out.println(" " + removeCount);

		assert (checkRemoveInvariant(removedLevel) == null ) : checkRemoveInvariant(removedLevel);
	}

	/**
	 * It checks all backtrackable objects that they have not retained any level equal or above removedLevel.
	 * 
	 * @param removedLevel the level which has been removed and should not exist in any object.
	 * @return the description of the inconsistency, not maintained invariant.
	 */
	public String checkRemoveInvariant(int removedLevel) {
		
		for (int i = 0; i < this.noOfObjects; i++)
			if (objects[i].level() >= removedLevel )
				return "The object " + objects[i] + " has retained the old level " + removedLevel + " index " + objects[i].index();
		
		return null;
	}
	
	private void addChangedToInterval(int index) {
		
		// assert (false);
		// Look at intervals and split hole if needed.
		
		int currentPosition = 0;
		while (currentPosition < currentIntervals.length) {
			
			int left = currentIntervals[currentPosition];
			if (left > index)
				// all the remaining holes are safe.
				return;

			int right = currentIntervals[currentPosition+1];

			if (right < index) {
				// proceed to next hole. 
				currentPosition += 2;
				continue;
			}
			
			if (right - left < minHoleSizeAfterSplit) {
				// Hole disapears. Update current intervals.
				currentIntervals[currentPosition ] = -1;
				currentIntervals[currentPosition + 1] = -1;
			}
			
			if (index - left > right - index) {
				// hole on the left is greater.
				currentIntervals[currentPosition ] = left;
				currentIntervals[currentPosition + 1] = index - 1;
			}
			else {
				// hole on the right is greater.
				currentIntervals[currentPosition ] = index + 1;
				currentIntervals[currentPosition + 1] = right;				
			}
			
			
		}
				
	}

	/**
	 * It specifies how many objects within objects array are being actually 
	 * managed. It allows to specify partially empty array. 
	 * 
	 * @param size the number of objects in the array.
	 */
	public void setSize(int size) {
		
		super.setSize(size);
		intervalCutOffValue = Math.max(noOfObjects / 2, cutOffValue + 1);
		
	} 
	
	
	/**
	 * It allows for easy testing if a given object is considered by 
	 * the manager as the object which has changed and needs being 
	 * informed about backtracking. 
	 * 
	 * @param index the position of the object which status is in question.
	 * @return it returns true if the manager recognizes object at position index as changed one. 
	 */
	@Override
	public boolean isRecognizedAsChanged(int index) {
		
		if (currentLevelMax)
			return true;
				
		if (trailContainsAllChanges) {
		
			if (addingToIntervals) {
				
				// trail used interval description.
				int[] trailLevel = trail.get(trail.size() - 1);
				
				for (int i = 0; i < trailLevel.length;) {
					if (trailLevel[i] <= index && index <= trailLevel[i+1])
						// within a hole.
						return false;
					if (trailLevel[i] > index)
						// before a hole.
						return true;
					i += 2;
				}
				// it did not hit any hole.
				return true;
		
			}

			// number of changes was too small to use intervals, just a list is used.
			int [] trailLevel = trail.get(trail.size() - 1);
			
			for (int i : trailLevel)
				if (i == index)
					return true;
			
			return false;
			
		} else {
			
			if (addingToIntervals) {
				
				for (int i = 0; i < currentIntervals.length;) {
					if (currentIntervals[i] <= index && index <= currentIntervals[i+1])
						// within a hole.
						return false;
					if (currentIntervals[i] > index)
						// before a hole.
						return true;
					i += 2;
				}
				// it did not hit any hole.
				return true;
		
			}

			// SparseSet contains all changes for the current level.
			return currentlyChanged.isMember(index);
			
		}
		
		
	}	

}
