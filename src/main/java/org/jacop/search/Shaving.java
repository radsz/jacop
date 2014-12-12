/**
 *  Shaving.java 
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

package org.jacop.search;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XneqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Defines functionality of shaving. Plugin in this object to search to
 * change your depth first search to a search with shaving capabilities.
 * 
 * Shaving
 * 
 * Each search level stores the variable value pairs which were shaved at a
 * given level.
 * 
 * Shaving speculation.
 * 
 * The right child is using all the shavable pairs from the subtree rooted at
 * the sibling of the current search node. If shaving fails then it is recorded
 * in non shavable.
 * 
 * Not-shavable speculation
 * 
 * Every time a variable value pair is being schedule for shavability check then
 * it is checked if that pair was not already checked for shavability before
 * with a negative results. If so, then check is not performed but also entry in
 * not-shavable is removed.
 * 
 * If variable value pair proofs to be not shavable then this variable value pair
 * is recorded into Not-shavable speculation.
 * 
 * Quick shave - upon exiting any subtree the variable value pair which was
 * choosen at the root of that subtree is recorded as shavable variable value
 * pair.
 * 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class Shaving<T extends IntVar> implements ExitChildListener<T>, ConsistencyListener {

	/**
	 * It contains list of constraints which suggest shaving explorations.
	 */

	ArrayList<Constraint> shavingConstraints = new ArrayList<Constraint>();

	/**
	 * It specifies if the search is in the left child.
	 */

	boolean leftChild = true;

	/**
	 * It specifies current store, so shaving can obtained information about
	 * recent failed constraint.
	 */

	Store store;

	Constraint recentlyFailedConstraint = null;

	boolean leftChildShaving = true;

	/**
	 * It specifies if only the last failed constraint is allowed to suggest shaving values.
	 */
	public boolean onlyFailedConstraint = false;

	boolean rightChild = false;

	/**
	 * It specifies if only variables in the scope of the last failed constraint are
	 * allowed to be used in shaving attempts.
	 */
	public boolean onlyIntVarsOfFailedConstraint = false;

	/**
	 * It stores the variables of the last failed constraints.
	 */
	public HashSet<IntVar> varsOfFailedConstraint = new HashSet<IntVar>();

	boolean wrongDecisionEncountered;

	private ExitChildListener[] exitChildListeners;

	private ConsistencyListener[] consistencyListeners;

	
	/**
	 * It specifies if the quickShave approach should be also used. Quickshave uses
	 * variable-value pairs which lead to wrong decisions as shaving values higher
	 * in the search tree (until the first time shaving attempt for this value fails).
	 */
	public boolean quickShave = false;

	private boolean leftChildWrongDecision = false;

	private int depth = 0;
	
	ArrayList<HashMap<IntVar, LinkedHashSet<Integer> >> shavable = new ArrayList<HashMap<IntVar, LinkedHashSet<Integer> >> ();

	HashMap<IntVar, LinkedHashSet<Integer>> notShavable = new HashMap<IntVar, LinkedHashSet<Integer>>();	
	
	/**
	 * It stores number of successful shaving attempts.
	 */
	public int successes = 0;
	
	/**
	 * It stores number of failed shaving attempts.
	 */
	public int failures = 0;
	
	public boolean leftChild(IntVar var, int value, boolean status) {

		leftChild = false;
		leftChildWrongDecision = true;
		depth--;

		return true;
	}

	public boolean leftChild(PrimitiveConstraint choice, boolean status) {
		
		leftChild = false;
		leftChildWrongDecision = true;
		depth--;
		return true;
	}

	public void rightChild(IntVar var, int value, boolean status) {
		
		leftChild = false;

		if (!status) {
			
			if (quickShave && leftChildWrongDecision) {
				
				int position = shavable.size() - 1;
				
				if (position > depth )
					position = depth - 1;
				
				if (position < 0)
					position = 0;
					
				HashMap<IntVar, LinkedHashSet<Integer>> current = shavable.get(position);
				LinkedHashSet<Integer> shaveVarList = current.get(var);
				
				if (shaveVarList == null) {
					shaveVarList = new LinkedHashSet<Integer>();
					current.put(var, shaveVarList);
				}
				shaveVarList.add(value);
			}
		}
		
		depth--;
		leftChildWrongDecision = false;
	}

	public void rightChild(PrimitiveConstraint choice, boolean status) {
		leftChild = false;
		depth--;
		leftChildWrongDecision = false;
	}

	public void setChildrenListeners(ConsistencyListener[] children) {
		consistencyListeners = children;
	}

	public void setChildrenListeners(ExitChildListener[] children) {

		exitChildListeners = children;
	}

	public void setChildrenListeners(ConsistencyListener child) {
		consistencyListeners = new ConsistencyListener[1];
		consistencyListeners[0] = child;
	}

	public void setChildrenListeners(ExitChildListener child) {
		exitChildListeners = new ExitChildListener[1];
		exitChildListeners[0] = child;
	}


	public boolean executeAfterConsistency(boolean consistent) {

		if (!consistent) {
			recentlyFailedConstraint = store.recentlyFailedConstraint;
			depth++;
			return false;
		}

		// Speculate based on neighbours
		HashMap<IntVar, LinkedHashSet<Integer>> shavableCurrent = new HashMap<IntVar, LinkedHashSet<Integer>>();
	
		int last = shavable.size();
		int current = depth;
		
		while (last > current) {
		
			HashMap<IntVar, LinkedHashSet<Integer>> shavableNeighbour = shavable.get(current);
			
			for (IntVar shaveVar : shavableNeighbour.keySet()) {
				LinkedHashSet<Integer> list = shavableNeighbour.get(shaveVar);
				
				for (Integer shaveVal : list) {

					if (!shaveVar.domain.contains(shaveVal) || 
						shaveVar.singleton())
						continue;
					
					boolean shavablePair = checkIfShavable(shaveVar, shaveVal);
					
					if (shavablePair) {
					
						LinkedHashSet<Integer> shaveVarList = shavableCurrent.get(shaveVar);
						if (shaveVarList == null) {
							shaveVarList = new LinkedHashSet<Integer>();
							shavableCurrent.put(shaveVar, shaveVarList);
						}
						shaveVarList.add(shaveVal);
				
						store.impose(new XneqC(shaveVar, shaveVal));
						boolean result = store.consistency();

						if (!result) {
							depth++;
							return false;
						}

					} else {

						// record that pair (shaveVar,shareValue) was not
						// shaved.
						LinkedHashSet<Integer> notShaveVarList = notShavable
								.get(shaveVar);
						if (notShaveVarList == null) {
							notShaveVarList = new LinkedHashSet<Integer>();
							notShavable.put(shaveVar, notShaveVarList);
						}
						notShaveVarList.add(shaveVal);

					}
				}
			}

			current++;
		}

		while (shavable.size() != 0 && shavable.size() != depth)
			shavable.remove(shavable.size() - 1);
		
		depth++;
		shavable.add(shavableCurrent);	
	
		if (!leftChildShaving || leftChild)
			for (Constraint g : shavingConstraints) {

				if (onlyFailedConstraint)
					if (recentlyFailedConstraint != g)
						continue;

				IntVar shaveVar = (T)g.getGuideVariable();

				if (shaveVar == null)
					continue;

				int shaveVal = g.getGuideValue();

				if (onlyIntVarsOfFailedConstraint)
					if (!varsOfFailedConstraint.contains(shaveVar))
						continue;

				LinkedHashSet<Integer> notShavableListShaveVar;

				notShavableListShaveVar = notShavable.get(shaveVar);

				if (notShavableListShaveVar != null
						&& notShavableListShaveVar.remove(shaveVal)) {
					continue;
				}

				boolean shavablePair = checkIfShavable(shaveVar, shaveVal);

				if (shavablePair) {
					
					LinkedHashSet<Integer> shaveVarList = shavableCurrent.get(shaveVar);
					
					if (shaveVarList == null) {
						shaveVarList = new LinkedHashSet<Integer>();
						shavableCurrent.put(shaveVar, shaveVarList);
					}
					shaveVarList.add(shaveVal);
			
					store.impose(new XneqC(shaveVar, shaveVal));
					boolean result = store.consistency();

					if (!result)
						return false;

				} else {

					// record that pair (shaveVar,shareValue) was not shaved.
					LinkedHashSet<Integer> notShaveVarList = notShavable
							.get(shaveVar);
					if (notShaveVarList == null) {
						notShaveVarList = new LinkedHashSet<Integer>();
						notShavable.put(shaveVar, notShaveVarList);
					}
					notShaveVarList.add(shaveVal);

				}
			}

		leftChild = true;

		return true;
	}

	boolean checkIfShavable(IntVar var, Integer val) {

		assert var.domain.contains(val) && !var.domain.singleton(): "var " + var + "val " + val + 
		" should not be checked for shavability";

		int depth = store.level;

		store.setLevel(++depth);
	//	store.currentConstraint = null;

		var.domain.in(store.level, var, val, val);

		boolean shavable = !(store.consistency());

		store.removeLevel(depth);
		store.setLevel(--depth);

		if (shavable)
			successes++;
		else
			failures++;
		
		return shavable;

	}

	/**
	 * It adds shaving constraint to the list of constraints guiding shaving.
	 * @param c constraint which is added to the list of guiding constraints.
	 */
	public void addShavingConstraint(Constraint c) {

		shavingConstraints.add(c);

	}

	/**
	 * It specifies the constraint store in which context the shaving will take place.
	 * @param store constraint store.
	 */
	public void setStore(Store store) {

		this.store = store;

	}

}
