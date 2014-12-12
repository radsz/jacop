/**
 *  CumulativeProfiles.java 
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

/**
 * Defines a basic data structure to keep two profiles for the cumulative
 * constraints. It consists of ordered pair of time points and the current
 * value.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

class CumulativeProfiles {

	static final boolean trace = false;

	Profile maxProfile = null;

	Profile minProfile = null;

	CumulativeProfiles() {
	}

	void make(Task[] Ts) {
		Task t;
		IntTask iTask = new IntTask();
		int strt, stp, value;
		int tDurMin, tResMin;

		minProfile = new Profile();
		maxProfile = new Profile();
		for (int i = 0; i < Ts.length; i++) {
			t = Ts[i];

			tDurMin = t.dur.min();
			tResMin = t.res.min();

			strt = t.EST();
			stp = t.LaCT();
			value = t.res.max();
			if (trace)
				System.out.println("Update profile " + "[" + strt + ".." + stp
						+ ")=" + value);
			maxProfile.addToProfile(strt, stp, value);

			if (tDurMin > 0 && tResMin > 0) {
				if (t.minUse(iTask)) {
					if (trace)
						System.out.println("Update profile " + t + " ["
								+ iTask.start() + ".." + iTask.stop() + ")="
								+ tResMin);
					minProfile.addToProfile(iTask.start(), iTask.stop(),
							tResMin);
				}
			}
		}
	}

	Profile maxProfile() {
		return maxProfile;
	}

	Profile minProfile() {
		return minProfile;
	}
}
