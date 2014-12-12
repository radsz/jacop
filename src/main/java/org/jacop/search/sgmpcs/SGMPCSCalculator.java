/**
 *  SGMPCSCalculator.java 
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

package org.jacop.search.sgmpcs;

import org.jacop.core.Var;
import org.jacop.search.ConsistencyListener;

/**
 * Defines functionality for SGMPCS search
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

public class SGMPCSCalculator<T extends Var> implements ConsistencyListener {

    int numberFails = 0;

    int failLimit;

    public SGMPCSCalculator(int limit) {
	failLimit = limit;
    }

    /**
     * It is executed right after consistency of the current search node. The
     * return code specifies if the search should continue with or exit the
     * current search node.
     */

    public boolean executeAfterConsistency(boolean consistent) {

	if (numberFails >= failLimit)
	    return false;
	else {
	    if (!consistent)
		numberFails++;

	    return consistent;
	}
    }

    public void setFailLimit(int limit) {

	failLimit = limit;
    }

    public int getFailLimit() {

	return failLimit;
    }

    public int getNumberFails() {

	return numberFails;
    }

    public void setChildrenListeners(ConsistencyListener[] children) {
    }

    public void setChildrenListeners(ConsistencyListener child) {
    }

}
