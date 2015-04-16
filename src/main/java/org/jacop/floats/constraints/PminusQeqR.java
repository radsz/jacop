/**
 *  PminusQeqR.java
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

package org.jacop.floats.constraints;

import org.jacop.floats.core.FloatVar;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Constraint P - Q = R
 *
 * Bound consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class PminusQeqR extends PplusQeqR { private static Logger logger = LoggerFactory.getLogger(PminusQeqR.class);


    /** It constructs constraint P-Q=R.
     * @param p variable p.
     * @param q variable q.
     * @param r variable r.
     */
    public PminusQeqR(FloatVar p, FloatVar q, FloatVar r) {
	super(r, q, p);
    }

    @Override
    public String toString() {

	return id() + " : PminusQeqR(" + r + ", " + q + ", " + p + " )";
    }

}
