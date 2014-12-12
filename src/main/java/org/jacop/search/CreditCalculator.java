/**
 *  CreditCalculator.java 
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

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * Defines functionality of credit search. Plugin in this object into search to
 * change your depth first search into credit search. It has to be plugin as
 * ExitChildListener, TimeOutListener, and Consistency Listener.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variable being used in the search.
 */

public class CreditCalculator<T extends Var> implements ExitChildListener<T>, TimeOutListener,
		ConsistencyListener {

	boolean timeOut = false;

	int backtracks;

	int currentLevel = -1;

	int currentBacktracks = 0;

	int[] creditsLeft;

	int[] creditsRight;

	boolean leftChild = true;

	@Override
	public String toString() {
		
		StringBuffer desc = new StringBuffer();
		
		desc.append("credit-right\n");
		for (int i = 0; i < creditsRight.length; i++)
			desc.append(String.valueOf(creditsRight[i])).append(" ");
		
		desc.append("\n");
		
		desc.append("credit-left\n");
		for (int i = 0; i < creditsLeft.length; i++)
			desc.append(String.valueOf(creditsLeft[i])).append(" ");
		
		desc.append("\n");
		
		desc.append("currentLevel ").append(String.valueOf(currentLevel)).append("\n");
		desc.append("currentBacktracks ").append(String.valueOf(currentBacktracks)).append("\n");
		desc.append("leftChild? ").append(String.valueOf(leftChild));
		return desc.toString();
		
	}
	
	ConsistencyListener[] consistencyListeners;

	ExitChildListener<T>[] exitChildListeners;

	TimeOutListener[] timeOutListeners;

	/**
	 * The constructor allows to specify number of credits. Credits of the
	 * parent are divided equally among children. As soon a node has only one
	 * credit, there is a restriction how many backtracks can be performed in
	 * search in the left and right child altogether. If nodes are at maxDepth
	 * then the credits are not splitted among children but sent back to the
	 * parent for use in other parts of the tree. In a nutshell, there are
	 * maximally credit number of search subtrees attached at depth no lower
	 * than max depth with a maximumally number of backtracks performed in those
	 * subtrees. This approach allows to limit detrimental effect of early
	 * mistake which can not be proven easily by a backtrack search.
	 * @param credit the number of credits given to a search. 
	 * @param backtracks the maximum number of allowed backtracks from the node which has no remaining credits.
	 * @param maxDepth the maximum depth at which it is still alowed to distribute credits.
	 */

	public CreditCalculator(int credit, int backtracks, int maxDepth) {

		assert (maxDepth >= 1);

		this.backtracks = backtracks;
		currentBacktracks = backtracks;
		creditsLeft = new int[maxDepth];
		creditsRight = new int[maxDepth];

		creditsRight[0] = credit / 2;
		creditsLeft[0] = credit - creditsRight[0];

	}

	
	 /** The constructor allows to specify number of credits. Credits of the
	 * parent are divided equally among children. As soon a node has only one
	 * credit, there is a restriction how many backtracks can be performed in
	 * search in the left and right child altogether. This approach allows to 
	 * limit detrimental effect of early mistake which can not be proven easily 
	 * by a backtrack search.
	 * @param credit the number of credits given to a search. 
	 * @param backtracks the maximum number of allowed backtracks from the node which has no remaining credits.
	 */
	public CreditCalculator(int credit, int backtracks) {

		this.backtracks = backtracks;
		currentBacktracks = backtracks;
		
		int no = 0;

		int temp = credit;
		while (temp > 1) {
			temp = temp / 2;
			no++;
		}
		creditsLeft = new int[no + 2];
		creditsRight = new int[no + 2];

		creditsRight[0] = credit / 2;
		creditsLeft[0] = credit - creditsRight[0];

	}

	/**
	 * It is executed right after consistency of the current search node. The
	 * return code specifies if the search should continue with or exit the
	 * current search node.
	 */

	public boolean executeAfterConsistency(boolean consistent) {

		currentLevel++;

		//TODO, if not consistent in left child then transfer credits to right child?
		
		if (!consistent && leftChild) {
			currentLevel--;
				if (currentLevel > 0 && currentLevel < creditsLeft.length) {
				
					//TODO, do we need that?	if (creditsLeft[currentLevel - 1] > 1)	
					creditsRight[currentLevel] += creditsLeft[currentLevel];
					creditsLeft[currentLevel] = 0;
			
				}
		}
		
		if (consistent)
			if (currentLevel > 0 && currentLevel < creditsLeft.length) {

				if (leftChild)
					if (creditsLeft[currentLevel - 1] > 1) {
						creditsRight[currentLevel] = creditsLeft[currentLevel - 1] / 2;
						creditsLeft[currentLevel] = creditsLeft[currentLevel - 1]
								- creditsRight[currentLevel];
						creditsLeft[currentLevel - 1] = 0;
					} else if (creditsLeft[currentLevel - 1] == 1) {
						currentBacktracks = backtracks;
						creditsLeft[currentLevel - 1] = 0;
					}

				if (!leftChild)
					if (creditsRight[currentLevel - 1] > 1) {
						creditsRight[currentLevel] = creditsRight[currentLevel - 1] / 2;
						creditsLeft[currentLevel] = creditsRight[currentLevel - 1]
								- creditsRight[currentLevel];
						creditsRight[currentLevel - 1] = 0;
					} else if (creditsRight[currentLevel - 1] == 1) {
						currentBacktracks = backtracks;
						creditsRight[currentLevel - 1] = 0;
					}

			} else if (currentLevel == creditsLeft.length) {

				if (leftChild) {
					if (creditsLeft[currentLevel - 1] >= 1) {
						creditsLeft[currentLevel - 1]--;
						currentBacktracks = backtracks;
					}
				} else {
					if (creditsRight[currentLevel - 1] >= 1) {
						creditsRight[currentLevel - 1]--;
						currentBacktracks = backtracks;
					}
				}
			}

		if (consistencyListeners != null) {
			boolean code = false;
			for (int i = 0; i < consistencyListeners.length; i++)
				code |= consistencyListeners[i]
						.executeAfterConsistency(consistent);
			if (code)
				leftChild = true;

			return code && true;
		}

		if (consistent)
			leftChild = true;
		return consistent;
	}

	/**
	 * It is executed right after time out is determined.
	 */

	public void executedAtTimeOut(int noSolutions) {

		if (noSolutions == 0) {
			timeOut = true;
		}

		if (timeOutListeners != null)
			for (int i = 0; i < timeOutListeners.length; i++)
				timeOutListeners[i].executedAtTimeOut(noSolutions);

	}

	/**
	 * It is executed after exiting the left child. The parameters specify the
	 * variable and value used in the choice point. The parameter status
	 * specifies the return code from the child. The return parameter of this
	 * function specifies if the search should continue undisturbed or exit the
	 * current search node with false.
	 */

	public boolean leftChild(T var, int value, boolean status) {

		//TODO if credits are encountered in the node then backtracks should be set to zero. where?
		
		if (!status) {

			if (currentLevel > 0 && currentLevel < creditsLeft.length) {
				creditsRight[currentLevel - 1] += creditsLeft[currentLevel];
				creditsLeft[currentLevel] = 0;
			}

			if (currentBacktracks < 0
					&& !(currentLevel < creditsLeft.length && creditsRight[currentLevel] > 0)) {

				if (exitChildListeners != null) {
					for (int i = 0; i < exitChildListeners.length; i++)
						exitChildListeners[i].leftChild(var, value, status);
				}

				currentLevel--;
				return false;
			}
		}

		if (status) {
			if (exitChildListeners != null) {
				boolean code = false;
				for (int i = 0; i < exitChildListeners.length; i++)
					code |= exitChildListeners[i].leftChild(var, value, status);

				if (!code)
					currentLevel--;
				return code;
			}
			return true;
		}

		// !status since, status if clause is earlier and must cause exit.
		if (timeOut) {
			if (exitChildListeners != null) {
				for (int i = 0; i < exitChildListeners.length; i++)
					exitChildListeners[i].leftChild(var, value, status);
				// return code is an and relationship with a parent
			}

			currentLevel--;
			return false;
		} else {

			leftChild = false;

			if (exitChildListeners != null) {
				boolean code = false;
				for (int i = 0; i < exitChildListeners.length; i++)
					code |= exitChildListeners[i].leftChild(var, value, status);
				if (!code) {
					currentLevel--;
					return false;
				}
			}

			return true;
		}

	}

	/**
	 * It is executed after exiting the left child. The parameters specify the
	 * choice point. The parameter status specifies the return code from the
	 * child. The return parameter of this function specifies if the search
	 * should continue undisturbed or exit the current search node. If the left
	 * child has exhausted backtracks allowance then this function will return
	 * false so the right child will not be explored.
	 */

	public boolean leftChild(PrimitiveConstraint choice, boolean status) {

		if (!status) {

			if (currentLevel + 1 < creditsLeft.length) {
				creditsRight[currentLevel] += creditsLeft[currentLevel + 1];
				creditsLeft[currentLevel + 1] = 0;
			}

			// If credits of the right child are zero then right child will not be explored.
			if (currentBacktracks < 0
					&& !(currentLevel < creditsLeft.length && creditsRight[currentLevel] > 0)) {

				if (exitChildListeners != null) {
					for (int i = 0; i < exitChildListeners.length; i++)
						exitChildListeners[i].leftChild(choice, status);
				}

				currentLevel--;
				return false;
			}
		}

		if (status) {
			if (exitChildListeners != null) {
				boolean code = false;
				for (int i = 0; i < exitChildListeners.length; i++)
					code |= exitChildListeners[i].leftChild(choice, status);
				return code;
			}
			return true;
		}

		if (timeOut) {
			if (exitChildListeners != null) {
				for (int i = 0; i < exitChildListeners.length; i++)
					exitChildListeners[i].leftChild(choice, status);
			}

			currentLevel--;
			return false;
		} else {

			leftChild = false;

			if (exitChildListeners != null) {
				boolean code = false;
				for (int i = 0; i < exitChildListeners.length; i++)
					code |= exitChildListeners[i].leftChild(choice, status);
				if (!code) {
					currentLevel--;
					return false;
				}
			}

			return true;
		}

	}

	/**
	 * Exiting the right children if no credits have been distributed to a right
	 * child involves increasing the number of backtracks occurred.
	 */

	public void rightChild(T var, int value, boolean status) {

		currentLevel--;

		leftChild = false;

		if (currentLevel > 0 && currentLevel < creditsLeft.length) {
			creditsRight[currentLevel - 1] += creditsRight[currentLevel];
			creditsRight[currentLevel] = 0;
		}

		if (!timeOut) {

			if (currentLevel >= creditsLeft.length
					|| creditsLeft[currentLevel] == 0)
				currentBacktracks--;
			
		}

		if (exitChildListeners != null)
			for (int i = 0; i < exitChildListeners.length; i++)
				exitChildListeners[i].rightChild(var, value, status);

	}

    public void rightChild(PrimitiveConstraint choice, boolean status) {

		currentLevel--;

		leftChild = false;

		if (currentLevel + 1 < creditsLeft.length) {
			creditsRight[currentLevel] += creditsLeft[currentLevel + 1];
			creditsLeft[currentLevel + 1] = 0;
		}

		if (!timeOut) {

			if (currentLevel >= creditsLeft.length
					|| creditsLeft[currentLevel] == 0)
				currentBacktracks--;

		}

		if (exitChildListeners != null)
			for (int i = 0; i < exitChildListeners.length; i++)
				exitChildListeners[i].rightChild(choice, status);

	}

    public void setChildrenListeners(ConsistencyListener[] children) {
		consistencyListeners = children;
	}

	public void setChildrenListeners(ExitChildListener<T>[] children) {

		exitChildListeners = children;
	}

	public void setChildrenListeners(TimeOutListener[] children) {

		timeOutListeners = children;

	}

	public void setChildrenListeners(ConsistencyListener child) {
		consistencyListeners = new ConsistencyListener[1];
		consistencyListeners[0] = child;
	}

	public void setChildrenListeners(ExitChildListener<T> child) {
		exitChildListeners = new ExitChildListener[1];
		exitChildListeners[0] = child;
	}

	public void setChildrenListeners(TimeOutListener child) {

		timeOutListeners = new TimeOutListener[1];
		timeOutListeners[0] = child;

	}

}
