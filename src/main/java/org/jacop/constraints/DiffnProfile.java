/**
 *  DiffnProfile.java 
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


package org.jacop.constraints;

import java.util.ArrayList;

import org.jacop.core.IntDomain;

/**
 * Defines a basic data structure to keep the profile for the diff2/1
 * constraints. It consists of ordered pair of time points and the current
 * value.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

class DiffnProfile extends Profile {

	private static final long serialVersionUID = 8683452581100000011L;

	static final boolean trace = false;

	DiffnProfile() {
	}

	void make(int i, int j, Rectangle r, int begin, int end,
			ArrayList<Rectangle> Rs) {
		// Rectangle t;

		clear();
		maxProfileItemHeight = 0;
		IntDomain rOrigin_i_Dom = r.origin[i].dom();
		IntDomain rLength_i_Dom = r.length[i].dom();
		int rOriginMin = rOrigin_i_Dom.min(), rOriginMax = rOrigin_i_Dom.max(), rLengthMax = rLength_i_Dom
				.max();
		IntRectangle R = new IntRectangle(r.dim);

		for (Rectangle t : Rs) {
			IntDomain tOrigin_i_Dom = t.origin[i].dom();
			if (t != r
					&& tOrigin_i_Dom.min() >= rOriginMin
					&& tOrigin_i_Dom.max() + t.length[i].max() <= rOriginMax
							+ rLengthMax) {
				R.dim = 0;
				if (t.minUse(i, R)) {
					if (trace)
						System.out.println("Update profile " + "["
								+ R.origin[j] + ".."
								+ (R.origin[j] + R.length[j]) + ")="
								+ t.length(i).min());
					addToProfile(R.origin[j], R.origin[j] + R.length[j],
							t.length[i].min());
				}
			}
		}
	}

	@Override
	public int max() {
		return super.max();
	}
}
