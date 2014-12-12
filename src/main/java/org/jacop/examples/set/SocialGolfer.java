/**
 *  SocialGolfer.java 
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

import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XlteqY;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.set.constraints.AdisjointB;
import org.jacop.set.constraints.AeqS;
import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.set.constraints.AunionBeqC;
import org.jacop.set.constraints.CardA;
import org.jacop.set.constraints.Match;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;
import org.jacop.set.search.MaxGlbCard;
import org.jacop.set.search.MinLubCard;

/**
 * It is a Social Golfer example based on set variables.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

public class SocialGolfer extends ExampleSet {

	// 2, 7, 4
	
	int weeks = 3;

	int groups = 2;

	int players = 2;

	SetVar[][] golferGroup;

	/**
	 * 
	 * It runs a number of social golfer problems.
	 * 
	 * @param args
	 */
	public static void main (String args[]) {

		SocialGolfer example = new SocialGolfer();

		example.setup(3, 2, 2);
		example.model();
		example.search();
		
		// Solved
		example.setup(2,5,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(2,6,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(2,7,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(3,5,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(3,6,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(3,7,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(4,5,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(4,6,5); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(4,7,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(4,9,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(5,5,3); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(5,7,4); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(5,8,3); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(6,6,3); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(5,3,2); // weeks - groups - players in each group
		example.model();
		example.search();
		
		example.setup(4,3,3); // weeks - groups - players in each group
		example.model();
		example.search();
		
	}

	/**
	 * It sets the parameters for the model creation function. 
	 * 
	 * @param weeks
	 * @param groups
	 * @param players
	 */
	public void setup(int weeks, int groups, int players) {

		this.weeks = weeks;
		this.groups = groups;
		this.players = players;

	}

	public  void model() {

		int N = groups * players;
		
		int[] weights = new int[players];
		
		int base = Math.max(10, players + 1); //at least players + 1
		
		weights[players - 1] = 1;
		
		for (int i = players - 2; i >= 0; i --)
			weights[i] = weights[i+1]*base;

		System.out.println("Social golfer problem " + weeks + "-" + groups + "-" + players);

		store = new Store();
		
		golferGroup = new SetVar[weeks][groups];

		vars = new ArrayList<SetVar>();

		for (int i=0; i<weeks; i++)
			for (int j=0; j<groups; j++) {
				golferGroup[i][j] = new SetVar(store, "g_"+i+"_"+j, new BoundSetDomain(1, N));
				vars.add(golferGroup[i][j]);
				store.impose(new CardA(golferGroup[i][j], players));
			}

		for (int i=0; i<weeks; i++) 
			for (int j=0; j<groups; j++) 
				for (int k=j+1; k<groups; k++) {
					store.impose(new AdisjointB(golferGroup[i][j], golferGroup[i][k]));
				}

		for (int i=0; i<weeks; i++) {
			
			SetVar t = golferGroup[i][0];

			for (int j = 1; j < groups; j++) {
				SetVar r = new SetVar(store, "r-" + i + "-" + j, new BoundSetDomain(1, N));
				store.impose(new AunionBeqC(t, golferGroup[i][j], r));
				t = r;
			}
			
			// store.impose(new AinB(new SetVar(store, new BoundSetDomain(new IntervalDomain(1,N), new IntervalDomain(1,N))), t));
			store.impose(new AeqS(t, new IntervalDomain(1, N)));
			
		}

		for (int i=0; i<weeks; i++)
			for (int j=i+1; j<weeks; j++) 
				if (i != j) 
					for (int k=0; k<groups; k++)
						for (int l=0; l<groups; l++) {
							SetVar result = new SetVar(store, "res"+i+"-"+j+"-"+k+"-"+l, new BoundSetDomain(1,N));
							store.impose(new AintersectBeqC(golferGroup[i][k], golferGroup[j][l], result));
							store.impose(new CardA(result, 0, 1));
						}

		IntVar[] v = new IntVar[weeks];
		IntVar[][] var = new IntVar[weeks][players];
		for (int i=0; i<weeks; i++) {
			v[i] = new IntVar(store, "v"+i, 0, 100000000);
			for (int j=0; j<players; j++)
				var[i][j] = new IntVar(store, "var"+i+"-"+j, 1, N);
			store.impose(new Match(golferGroup[i][0], var[i]));
			store.impose(new SumWeight(var[i], weights, v[i]));
		}
		
		for (int i=0; i<weeks-1; i++)
			store.impose(new XlteqY(v[i], v[i+1]));

		
		
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
				new MinLubCard<SetVar>(),
				new MaxGlbCard<SetVar>(),
				new IndomainSetMin<SetVar>());

	//	label.setSolutionListener(new SetSimpleSolutionListener<SetVar>());
		label.getSolutionListener().searchAll(false);
		label.getSolutionListener().recordSolutions(false);

		result = label.labeling(store, select);

		if (result) {
			System.out.println("*** Yes");
			for (int i=0; i<weeks; i++) {
				for (int j=0; j<groups; j++) {
					System.out.print(golferGroup[i][j].dom()+" ");
				}
				System.out.println();
			}
		}
		else
			System.out.println("*** No");

		System.out.println( "ThreadCpuTime = " + (b.getThreadCpuTime(tread.getId()) - startCPU)/(long)1e+6 + "ms");
		System.out.println( "ThreadUserTime = " + (b.getThreadUserTime(tread.getId()) - startUser)/(long)1e+6 + "ms" );

		return result;
	}



}
