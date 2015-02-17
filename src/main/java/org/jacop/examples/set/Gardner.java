/**
 *  Gardner.java 
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

package org.jacop.examples.set;

import java.util.ArrayList;

import org.jacop.constraints.Not;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.set.constraints.AeqB;
import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.set.constraints.CardA;
import org.jacop.set.constraints.CardAeqX;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;

/**
 * It specifies a simple Gardner problem which use set functionality from JaCoP. 
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Gardner extends ExampleSet {

	/**
	 * It executes the program which solves this gardner problem.
	 * @param args
	 */
	public static void main(String args[]) {

		Gardner example = new Gardner();
		example.model();

		example.search();

	}

	public void model() {

		int num_days = 35;
		int num_persons_per_meeting = 3;
		int persons = 15;

		System.out.println("Gardner dinner problem ");
		store = new Store();

		SetVar[] days = new SetVar[num_days];
		
		for (int i = 0; i < days.length; i++)
			days[i] = new SetVar(store, "days[" + i + "]", new BoundSetDomain(1, persons));

	    vars = new ArrayList<SetVar>();
	    
	    for(SetVar d: days) 
	    	vars.add(d);

		// all_different(days)
		for (int i = 0; i < days.length - 1; i++)
			for (int j = i + 1; j < days.length; j++)
				store.impose(new Not(new AeqB(days[i], days[j])));

		// card(days[i]) = num_persons_per_meeting
		for (int i = 0; i < days.length; i++)
			store.impose(new CardA(days[i], num_persons_per_meeting));

		for (int i = 0; i < days.length - 1; i++)
			for (int j = i + 1; j < days.length; j++) {
				SetVar intersect = new SetVar(store, "intersect" + i + "-" + j, 
												  new BoundSetDomain(1, persons));
				store.impose(new AintersectBeqC(days[i], days[j], intersect));
				IntVar card = new IntVar(store, 0, 1);
				store.impose(new CardAeqX(intersect, card));
			}

		System.out.println( "\nVariable store size: "+ store.size()+
				"\nNumber of constraints: " + store.numberConstraints()
		);

	}
	
	public boolean search() {

		Thread tread = java.lang.Thread.currentThread();
		java.lang.management.ThreadMXBean b = java.lang.management.ManagementFactory.getThreadMXBean();

		long startCPU = b.getThreadCpuTime(tread.getId());
		long startUser = b.getThreadUserTime(tread.getId());

		boolean result = store.consistency();
		System.out.println("*** consistency = " + result);

		Search<SetVar> label = new DepthFirstSearch<SetVar>();

		SelectChoicePoint<SetVar> select = new SimpleSelect<SetVar>(vars.toArray(new SetVar[vars.size()]), 
				null,
				new IndomainSetMin<SetVar>());

	//	label.setSolutionListener(new SimpleSolutionListener());
		label.getSolutionListener().searchAll(false);
		label.getSolutionListener().recordSolutions(false);

		result = label.labeling(store, select);

		if (result) {
			System.out.println("*** Yes");
			for (int i=0; i< vars.size(); i++) {
				System.out.println(vars.get(i));
			}
		}
		else
			System.out.println("*** No");


		System.out.println( "ThreadCpuTime = " + (b.getThreadCpuTime(tread.getId()) - startCPU)/(long)1e+6 + "ms");
		System.out.println( "ThreadUserTime = " + (b.getThreadUserTime(tread.getId()) - startUser)/(long)1e+6 + "ms" );
		
		return result;

	}

}
