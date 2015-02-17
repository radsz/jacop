/**
 *  ComparatorVariable.java 
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

import org.jacop.core.Var;

/**
 * Defines an interface for comparing variables.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 * @param <T> Variable type being compared.
 */

public interface ComparatorVariable<T extends Var> {

	/**
	 * It compares the baseline metric to the variable metric. 
	 * @param metric the baseline for comparison.
	 * @param var variable which is compared to baseline.
	 * @return 1 if metric is larger than variable, 0 if equal, -1 if baseline is smaller.
	 */
	int compare(float metric, T var);

	/**
	 * It compares the metric of the left variable against the right one.
	 * @param leftVar left variable
	 * @param rightVar right variable
	 * @return 1 if metric for left variable is greater, 0 is they are equal, -1 if smaller.
	 */
	int compare(T leftVar, T rightVar);

	/**
	 * It returns the metric of the variable given according to the comparator.
	 * @param var variable for which metric is computed.
	 * @return the metric of the variable according to the comparator.
	 */
	float metric(T var);

}
