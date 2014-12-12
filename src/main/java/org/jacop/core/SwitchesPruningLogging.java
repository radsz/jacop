/**
 *  SwitchesPruningLogging.java
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
 *
 * It is a container class which specifies all different switches to turn
 * on debugging information.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public final class SwitchesPruningLogging {

	/**
	 * It is a general switch which can be turned off to switch off all printouts.
	 */
	public static final boolean trace = false;
	
	/**
	 * It turns on all trace printouts in variables.
	 */
	public static boolean traceVar = trace && true;

	/**
	 * It turns on all trace printouts in constraints.
	 */
	public static boolean traceConstraint = trace && true;

	/**
	 * The switch which enables to switch on/off the switches concerning Store operation.
	 */
	public static final boolean traceStore = trace && true;
	
	/**
	 * This switch enables to trace constraints which are being checked for consistency.
	 */
	public static boolean traceConsistencyCheck = trace && traceStore && true;
	
	/**
	 * This switch enables tracing the constraint added to the constraint queue.
	 */
	public static boolean traceQueueingConstraint = trace && traceStore && true;
	
	/**
	 * This switch enables tracing attempt to add the constraint to a queue when
	 * it is already added. 
	 */
	public static boolean traceAlreadyQueuedConstraint = trace && traceStore && true;

	/**
	 * This switch enables to traces the constraints which are being imposed.
	 */
	public static boolean traceConstraintImposition = trace && traceStore && true;
	
	/**
	 * It informs what traced constraints failed.
	 */
	public static boolean traceFailedConstraint = trace && traceStore && true;

	
	/**
	 * This switch enables to trace remove level operation. 
	 */
	public static boolean traceLevelRemoval = trace && traceStore && true;
	
	/**
	 * It traces all constraints have failed.
	 */
	public static boolean traceConstraintFailure = trace && true;
	
	/**
	 * This switch enables to trace removal of the store level.
	 */
	public static boolean traceStoreRemoveLevel = trace && true;

	/**
	 * This switch enables to trace creation of the variable.
	 */
	public static boolean traceVariableCreation = trace && true;

	/**
	 * This switch enables to trace set the store level.
	 */
	public static boolean traceOperationsOnLevel = trace && traceStore && true;

	/**
	 * It specifies if the search traces are active.
	 */
	public static final boolean traceSearch = trace && true;

	/**
	 * It traces the decisions within search.
	 */
	public static boolean traceSearchTree = trace && traceSearch && true;
	
	
	public final static void log(boolean isEnabled, Class fromClass, String pattern, Object[] args) {
	};

	public final static void log(boolean isEnabled, Class fromClass, String pattern, Object arg1) {
	};

	public final static void log(boolean isEnabled, Class fromClass, String pattern, Object arg1, Object arg2) {
	};

	private SwitchesPruningLogging() {
	}
	
}
