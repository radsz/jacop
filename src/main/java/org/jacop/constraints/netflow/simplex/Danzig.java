/**
 *  Danzig.java
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

package org.jacop.constraints.netflow.simplex;

/**
 * A simple rule that always chooses the arc with maximum violation.
 * It minimizes the number of iterations but the computational overhead
 * might be large.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 *
 */

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class Danzig implements PivotRule { private static Logger logger = LoggerFactory.getLogger(Danzig.class);

	public NetworkSimplex network;

	public Danzig(NetworkSimplex network) {
		this.network = network;
	}


	/**
	 * Finds the lower arc which violates optimality the most
	 * (If all lower arcs satisfy optimality then all upper arcs do too.
	 * In this case null is returned)
	 */
	public Arc next() {
		Arc next = null;
		int minimumCost = 0;
		for (int i = 0; i < network.numArcs; i++) {
			Arc arc = network.lower[i];
			int reducedCost = arc.reducedCost();
			if (minimumCost > reducedCost) {
				minimumCost = reducedCost;
				next = arc;
			}
		}
		return next;
	}


	public void reset() {
		// TODO Auto-generated method stub

	}

}
