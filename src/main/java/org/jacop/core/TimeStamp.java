/**
 *  TimeStamp.java 
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

package org.jacop.core;

/**
 * This class provides mutable variable functionality. The variable value
 * depends on the store level. Each value is time stamped with different store
 * level. This class lets you avoid recomputation every time a solver
 * backtracks. It will simply use the value with older time stamp. It is
 * appropriate for objects which do not share data across store levels. If you
 * have objects which share data across store levels than you need to make your
 * own implementation of mutable variable using MutableVar interface.
 * 
 * It will (it has to) store the same object at different levels as users of the
 * timestamp may ask for the level at which the timestamp was recently updated.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> a class being stored at different time stamps. 
 */

public class TimeStamp<T> {

	final static boolean debug = false;

	int index;

	public int pointer4Last = -1;

	public transient int[] stamps = new int[10];

	Store store;

	@SuppressWarnings("unchecked")
	public transient T[] values = (T[]) new Object[10];

	/**
	 * The constructor.
	 * @param store the store where the timestamp is registered.
	 * @param input the value of the stamp to be stored.
	 */
	public TimeStamp(Store store, T input) {

		addLast(input, store.level);

		index = store.putMutableVar(this);
		this.store = store;
	}

	final void addLast(T input, int level) {
		pointer4Last++;
		ensureCapacity(pointer4Last + 1);
		values[pointer4Last] = input;
		stamps[pointer4Last] = level;
	}

	/**
	 * Specify  least number of different values to be used by Timestamp.
	 * @param minCapacity
	 */
	@SuppressWarnings("unchecked")
	public void ensureCapacity(int minCapacity) {
		int oldCapacity = stamps.length;
		if (minCapacity > oldCapacity) {
			T oldValues[] = values;
			int oldStamps[] = stamps;

			int newCapacity = (oldCapacity * 3) / 2 + 1;

			// Here if there was no pointer4Last++ instruction
			// before calling ensureCapacity then it would need
			// to use pointer4Last+1
			values = (T[]) new Object[newCapacity];
			System.arraycopy(oldValues, 0, values, 0, pointer4Last);

			stamps = new int[newCapacity];
			System.arraycopy(oldStamps, 0, stamps, 0, pointer4Last);

		}
	}

	final int index() {
		return index;
	}

	/**
	 * @return the previous value according to the stamp. 
	 */
	final public T previousValue() {
		if (pointer4Last > 0)
			return values[pointer4Last - 1];
		else
			return null;
	}

	/**
	 * The function removes the level specified by the stamp. It assumes that
	 * it removes all the levels from the most recent until the level (inclusive)
	 * specified by the parameter.
	 * 
	 * @param level the number of the level. 
	 */
	public void removeLevel(int level) {

		while (pointer4Last >= 0 && stamps[pointer4Last] >= level) {
			
			// Not necessary, makes it possible to immediately collect garbage.
			// More memory friendly at the expense of the additional
			// instruction.
			values[pointer4Last] = null;
			pointer4Last--;
		}

	}

	/**
	 * It returns the value of the most recent stamp used within that timestamp. 
	 * @return the stamp value.
	 */
	public final int stamp() {
		return stamps[pointer4Last];
	}

	@Override
	public String toString() {
		StringBuffer S = new StringBuffer();

		S.append("TimeStamp<").append(index).append("> = ");

		for (int i = pointer4Last; i >= 0; i--) {
			S.append("v").append(values[i]).append("s").append(stamps[i]);
		}
		return S.toString();
	}

	/**
	 * It updates the value of the timestamp with the provided value.
	 * @param val value to which the timestamp needs to be updated.
	 */
	public void update(T val) {

        assert (stamps[pointer4Last] <= store.level) : "Error - Timestamp" + this	+ "has greater level than store "
							 + "- missing remove";

		if (stamps[pointer4Last] == store.level) {
			if (debug)
				System.out.print("1. Level: " + store.level + ", In " + this
						+ ",  New value " + val + "replaces old");

			values[pointer4Last] = val;
		} else if (stamps[pointer4Last] < store.level) {
			if (debug)
				System.out.print("2. Level: " + store.level + ", IN " + this
						+ ",  New value" + val);

			addLast(val, store.level);
		}
		
	}

	/**
	 * It returns the most recent value of the timestamp.
	 * 
	 * @return the most recent value of the timestamp. 
	 */
	final public T value() {
		return values[pointer4Last];
	}

}
