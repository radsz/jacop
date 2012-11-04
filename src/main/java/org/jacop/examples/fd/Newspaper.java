/**
 *  Newspaper.java 
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

package org.jacop.examples.fd;

import java.util.ArrayList;

import org.jacop.constraints.Cumulative;
import org.jacop.constraints.In;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;


/**
 * 
 * It is a simple newspaper reading job-shop like scheduling problem.
 * 
 * @author Radoslaw Szymanek
 *
 * There are four students: Algy, Bertie, Charlie and Digby, who share a flat. 
 * Four newspapers are delivered to the house: the Financial Times, the Guardian, 
 * the Daily Express and the Sun. Each of the students reads all of the newspapers, 
 * in particular order and for a specified amount of time (see below). 
 * 
 * Question: Given that Algy gets up at 8:30, Bertie and Charlie at 8:45 
 * and Digby at 9:30, what is the earliest that they can all set off for college? 
 *
 *			Algy 		Bertie		Charlie		Digby
 * Guardian		30		75		15		1
 * FinancialTime (FT)	60		25		10		1
 * Express		2		3 		5		1
 * Sun			5		10		30		90
 *
 * Algy order - FT, Guardian, Express, Sun
 * Bertie order - Guardian, Express, FT, Sun
 * Charlie order - Express, Guardian, FT, Sun
 * Digby order - Sun, FT, Guardian, Express
 */		

public class Newspaper extends ExampleFD {

	@Override
	public void model() {

		// Creating constraint store
		store = new Store();
		vars = new ArrayList<IntVar>();
		
		// algy[0], bertie[0], charlie[0], digby[0]
		// - when a person starts reading guardian
		IntVar[] algy = new IntVar[4];
		IntVar[] bertie = new IntVar[4];
		IntVar[] charlie = new IntVar[4];
		IntVar[] digby = new IntVar[4];

		IntVar[] guardian = new IntVar[4];
		guardian[0] = new IntVar(store, "durationAlgyGuardian", 30, 30);
		guardian[1] = new IntVar(store, "durationBertieGuardian", 75, 75);
		guardian[2] = new IntVar(store, "durationCharlieGuardian", 15, 15);
		guardian[3] = new IntVar(store, "durationDigbyGuardian", 1, 1);
		IntVar[] ft = new IntVar[4];
		ft[0] = new IntVar(store, "durationAlgyFT", 60, 60);
		ft[1] = new IntVar(store, "durationBertieFT", 25, 25);
		ft[2] = new IntVar(store, "durationCharlieFT", 10, 10);
		ft[3] = new IntVar(store, "durationDigbyFT", 1, 1);
		IntVar[] express = new IntVar[4];
		express[0] = new IntVar(store, "durationAlgyExpress", 2, 2);
		express[1] = new IntVar(store, "durationBertieExpress", 3, 3);
		express[2] = new IntVar(store, "durationCharlieExpress", 5, 5);
		express[3] = new IntVar(store, "durationDigbyExpress", 1, 1);
		IntVar[] sun = new IntVar[4];
		sun[0] = new IntVar(store, "durationAlgySun", 5, 5);
		sun[1] = new IntVar(store, "durationBertieSun", 10, 10);
		sun[2] = new IntVar(store, "durationCharlieSun", 30, 30);
		sun[3] = new IntVar(store, "durationDigbySun", 90, 90);

		IntVar[][] durations = new IntVar[4][];
		durations[0] = guardian;
		durations[1] = ft;
		durations[2] = express;
		durations[3] = sun;

		for (int i = 0; i < 4; i++) {
			
			// Variables can be enforced to have proper initial domains
			// in four different ways.
			
			// The first one if possible to use is by providing minimal and maximal 
			// values within the constructor of the variable.
			algy[i] = new IntVar(store, "algy[" + i + "]", 0, 1000);
			
			// bertie[i] = new Variable(store, "bertie[" + i + "]", 15, 1000);
			bertie[i] = new IntVar(store, "bertie[" + i + "]", -1000, 1000);
			// Bertie wakes up 15 minutes after Algy
			// The second one is by imposing In constraint after initially creating
			// a variable with too large domain.
			store.impose(new In(bertie[i], new IntervalDomain(15, 1000)));
			
			// Charlie wakes up 15 minutes after Algy
			// The third is to create a domain before creating a variable 
			// and using it. Please use clone() function, so one domain 
			// object is not used in multiple variables.
			IntervalDomain dom = new IntervalDomain();
			dom.unionAdapt(15, 1000);
			charlie[i] = new IntVar(store, "charlie[" + i + "]", dom);

			// Digby wakes up 60 minutes after Algy
			// digby[i] = new Variable(store, "digby[" + i + "]", 60, 1000);
			// The fourth way which is the slight variation of the third is 
			// by creating it directly in the constructor of the variable. 
			digby[i] = new IntVar(store, "digby[" + i + "]", new IntervalDomain(60, 1000));
			
			vars.add(algy[i]); vars.add(bertie[i]); vars.add(charlie[i]); vars.add(digby[i]);
		}

		IntVar one = new IntVar(store, "one", 1, 1);
		IntVar[] four = new IntVar[4];
		IntVar[] fourOnes = { one, one, one, one };

		four[0] = algy[0];
		four[1] = bertie[0];
		four[2] = charlie[0];
		four[3] = digby[0];
		// Guardian newspaper is read at any time by only one person
		store.impose(new Cumulative(four, guardian, fourOnes, one));

		four[0] = algy[1];
		four[1] = bertie[1];
		four[2] = charlie[1];
		four[3] = digby[1];
		// FT newspaper is read at any time by only one person
		store.impose(new Cumulative(four, ft, fourOnes, one));

		four[0] = algy[2];
		four[1] = bertie[2];
		four[2] = charlie[2];
		four[3] = digby[2];
		// Express newspaper is read at any time by only one person
		store.impose(new Cumulative(four, express, fourOnes, one));

		four[0] = algy[3];
		four[1] = bertie[3];
		four[2] = charlie[3];
		four[3] = digby[3];
		// Sun newspaper is read at any time by only one person
		store.impose(new Cumulative(four, sun, fourOnes, one));

		IntVar makespan = new IntVar(store, "makespan", 0, 1000);

		int[] algyPrecedence = { 2, 1, 3, 4 };
		// Constraints imposed below in for loop make sure that
		// algy reads newspapers sequentially and in the right order
		for (int i = 0; i < 3; i++)
			store.impose(new XplusYlteqZ(algy[algyPrecedence[i] - 1],
					durations[algyPrecedence[i] - 1][0],
					algy[algyPrecedence[i + 1] - 1]));

		// Make sure that makespan is at least equal to
		// the time point when algy finishes reading sun
		store.impose(new XplusYlteqZ(algy[3], sun[0], makespan));

		int[] bertiePrecedence = { 1, 3, 2, 4 };
		// Constraints imposed below in for loop make sure that
		// bertie reads newspapers sequentially and in the right order
		for (int i = 0; i < 3; i++)
			store.impose(new XplusYlteqZ(bertie[bertiePrecedence[i] - 1],
					durations[bertiePrecedence[i] - 1][1],
					bertie[bertiePrecedence[i + 1] - 1]));

		// Make sure that makespan is at least equal to
		// the time point when bertie finishes reading sun
		store.impose(new XplusYlteqZ(bertie[3], sun[1], makespan));

		int[] charliePrecedence = { 3, 1, 2, 4 };
		// Constraints imposed below in for loop make sure that
		// charlie reads newspapers sequentially and in the right order
		for (int i = 0; i < 3; i++)
			store.impose(new XplusYlteqZ(charlie[charliePrecedence[i] - 1],
					durations[charliePrecedence[i] - 1][2],
					charlie[charliePrecedence[i + 1] - 1]));

		// Make sure that makespan is at least equal to
		// the time point when charlie finishes reading sun
		store.impose(new XplusYlteqZ(charlie[3], sun[2], makespan));

		int[] digbyPrecedence = { 4, 2, 1, 3 };
		// Constraints imposed below in for loop make sure that
		// digby reads newspapers sequentially and in the right order
		for (int i = 0; i < 3; i++)
			store.impose(new XplusYlteqZ(digby[digbyPrecedence[i] - 1],
					durations[digbyPrecedence[i] - 1][3],
					digby[digbyPrecedence[i + 1] - 1]));

		// Make sure that makespan is at least equal to
		// the time point when digby finishes reading express
		store.impose(new XplusYlteqZ(digby[2], express[3], makespan));

		cost = makespan;
		vars.add(makespan);
		
	}
	
	
	/**
	 * It executes the program which solves this newspaper problem.
	 * 
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		Newspaper example = new Newspaper();
		
		example.model();

		if (example.searchSmallestMin())
			System.out.println("Solution(s) found");
		
	}	
	
}
