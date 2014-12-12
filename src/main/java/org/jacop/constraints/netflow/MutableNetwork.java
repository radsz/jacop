/**
 *  MutableNetwork.java 
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

package org.jacop.constraints.netflow;

import org.jacop.constraints.netflow.simplex.Arc;

/**
 * Interface to the network used by VarHandlers.
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public interface MutableNetwork {

	/**
	 * Removes an arc from the network. The arc must be at its lower or upper
	 * bound before it can be removed.
	 * 
	 * @param arc
	 *            The arc to be removed
	 */
	public abstract void remove(Arc arc);

	/**
	 * Tells the network that an arc has been modified. The network will then
	 * restore the arc upon backtracking.
	 * 
	 * @param companion
	 *            The arc that was modified
	 */
	public abstract void modified(ArcCompanion companion);

	/**
	 * Retrieves the current store level for domain pruning.
	 * 
	 * @return the store level
	 */
	 public abstract int getStoreLevel();

	/**
	 * Changes the cost offset by some value.
	 * 
	 * @param delta
	 *            the change in cost
	 */
	public abstract void changeCostOffset(long delta);

}
