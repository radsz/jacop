/**
 *  NoGoodsCollector.java 
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

import org.jacop.constraints.NoGood;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * NoGoodCollector collects no-goods from search when timeout has occurred. As
 * time-out is executed the search will exit from deeper search levels and
 * no-goods collector will collect neccessary information to create no-goods
 * when finally exiting the search. The no-goods will be immmediately imposed
 * when collector is informed about exiting the search.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class NoGoodsCollector<T extends IntVar> implements ExitChildListener<T>, TimeOutListener, ExitListener {

	ArrayList<ArrayList<T>> noGoodsVariables;

	ArrayList<ArrayList<Integer>> noGoodsValues;

	/**
	 * It specifies if the timeout has occurred and search is being terminated.
	 */
	public boolean timeOut = false;

	ExitChildListener<T>[] exitChildListeners;

	TimeOutListener[] timeOutListeners;

	ExitListener[] exitListeners;

	/**
	 * It is executed right after time out is determined.
	 */

	public void executedAtTimeOut(int noSolutions) {

		if (noSolutions == 0) {
			timeOut = true;
			noGoodsVariables = new ArrayList<ArrayList<T>>();
			noGoodsValues = new ArrayList<ArrayList<Integer>>();
		}

		if (timeOutListeners != null)
			for (int i = 0; i < timeOutListeners.length; i++)
				timeOutListeners[i].executedAtTimeOut(noSolutions);
	}

	/**
	 * It is executed after exiting left child. Status specifies if the solution
	 * is found or not. The return parameter specifies if the search should
	 * continue according to its course or be forced to exit the parent node of
	 * the left child.
	 */

	public boolean leftChild(T var, int value, boolean status) {

		if (timeOut) {
			for (ArrayList<T> noGood : noGoodsVariables)
				noGood.add(var);

			for (ArrayList<Integer> noGood : noGoodsValues)
				noGood.add(value);

			if (exitChildListeners != null)
				for (int i = 0; i < exitChildListeners.length; i++)
					exitChildListeners[i].leftChild(var, value, status);

			return false;
		} else {
			if (exitChildListeners == null)
				return true;
			else {
				boolean code = false;
				for (int i = 0; i < exitChildListeners.length; i++)
					code |= exitChildListeners[i].leftChild(var, value, status);
				return code;
			}
		}
	}

	public boolean leftChild(PrimitiveConstraint choice, boolean status) {
		if (exitChildListeners == null)
			return true;
		else {
			boolean code = false;
			for (int i = 0; i < exitChildListeners.length; i++)
				code |= exitChildListeners[i].leftChild(choice, status);
			return code;
		}
	}

	public void rightChild(T var, int value, boolean status) {

		if (timeOut) {
			ArrayList<T> newNoGoodVar = new ArrayList<T>();
			newNoGoodVar.add(var);
			ArrayList<Integer> newNoGoodVal = new ArrayList<Integer>();
			newNoGoodVal.add(value);

			noGoodsVariables.add(newNoGoodVar);
			noGoodsValues.add(newNoGoodVal);
		}

		if (exitChildListeners != null)
			for (int i = 0; i < exitChildListeners.length; i++)
				exitChildListeners[i].rightChild(var, value, status);

	}

    public void rightChild(PrimitiveConstraint choice, boolean status) {
		if (exitChildListeners != null)
			for (int i = 0; i < exitChildListeners.length; i++)
				exitChildListeners[i].rightChild(choice, status);
		return;
	}

    public void executedAtExit(Store store, int solutionsNo) {

		if (timeOut && solutionsNo == 0) {
			for (int i = 0; i < noGoodsVariables.size(); i++)
				store.impose(new NoGood(noGoodsVariables.get(i), noGoodsValues.get(i)));

		}

		if (exitListeners != null)
			for (int i = 0; i < exitChildListeners.length; i++)
				exitListeners[i].executedAtExit(store, solutionsNo);
	}

	public void setChildrenListeners(ExitChildListener<T>[] children) {
		exitChildListeners = children;
	}

	public void setChildrenListeners(ExitListener[] children) {

		exitListeners = children;
	}

	public void setChildrenListeners(TimeOutListener[] children) {

		timeOutListeners = children;

	}

	public void setChildrenListeners(TimeOutListener child) {
		timeOutListeners = new TimeOutListener[1];
		timeOutListeners[0] = child;
	}

	public void setChildrenListeners(ExitListener child) {
		exitListeners = new ExitListener[1];
		exitListeners[0] = child;
	}

	public void setChildrenListeners(ExitChildListener<T> child) {
		exitChildListeners = new ExitChildListener[1];
		exitChildListeners[0] = child;
	}

	@Override
	public String toString() {
		
		if (noGoodsVariables != null ) {
			StringBuffer sb = new StringBuffer(noGoodsVariables.toString());
			sb.append(noGoodsValues.toString());
			return sb.toString(); 
		}
		else return "[]";
		
	}
}
