/**
 *  Steiner.java 
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

import org.jacop.constraints.Reified;
import org.jacop.constraints.Sum;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.set.constraints.CardA;
import org.jacop.set.constraints.EinA;
import org.jacop.set.constraints.Lex;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMax;
import org.jacop.set.search.MaxCardDiff;

/**
 * It models and solves Steiner problem.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Steiner extends ExampleSet {

	/**
	 * It specifies the length of the problem.
	 */
	public int n = 3;

	Var[] vs;

	/**
	 * It executes the program which solves this Steiner problem.
	 * @param args
	 */
	public static void main(String args[]) {

		Steiner example = new Steiner();
		example.n = 7;
		example.model();

		example.search();

	}
	
	public void model () {

		int t = n * (n - 1 ) / 6;

		System.out.println("Steiner problem with n = "+ n +" and T = " + t);

		int r = n % 6;

		if (r==1 || r==3) {

			store = new Store();

			vars = new ArrayList<SetVar>();
			SetVar[] s = new SetVar[t];

			for (int i = 0; i < t; i++) {
				s[i] = new SetVar(store, "s"+i, new BoundSetDomain(1, n));
				vars.add(s[i]);
				store.impose( new CardA(s[i], 3));
			}

			for (int i = 0; i < t; i++)
				for (int j = i + 1; j < t; j++) {
					SetVar temp = new SetVar(store, "temp" + i + "," + j, new BoundSetDomain(1, n));
					store.impose(new AintersectBeqC(s[i],s[j],temp));
					store.impose( new CardA(temp, 0, 1));
				}

			for (int i = 0; i < s.length - 1; i++)
				store.impose(new Lex(s[i], s[i+1]));
			
			// implied constraints to get better pruning
			for (int i=1; i<=n; i++) {
				IntVar[] b = new IntVar[t];
				for (int j=0; j<t; j++) {
					b[j] = new IntVar(store, "b"+i+","+j, 0, 1);
					store.impose( new Reified(new EinA(i, s[j]), b[j]));
				}
				IntVar sum = new IntVar(store, "sum_"+i, (n-1)/2, (n-1)/2);
				store.impose(new Sum(b, sum));
			}
			
		}

	}

	public boolean search() {

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		int r = n % 6;

		if (r==1 || r==3) {

			boolean result = store.consistency();

			Search<SetVar> label = new DepthFirstSearch<SetVar>();

			SelectChoicePoint<SetVar> select = new SimpleSelect<SetVar>(vars.toArray(new SetVar[vars.size()]), 
					new MaxCardDiff<SetVar>(), 
					new IndomainSetMax<SetVar>());

			label.getSolutionListener().searchAll(true);
			label.getSolutionListener().recordSolutions(true);

			result = label.labeling(store, select);

			if (result) {
				System.out.println("*** Yes");
				label.getSolutionListener().printAllSolutions();
			}
			else
				System.out.println("*** No");

			T2 = System.currentTimeMillis();
			T = T2 - T1;
			System.out.println("\n\t*** Execution time = "+ T + " ms");
			return result;
		}
		else {
			System.out.println("Problem has no solution");
			return false;
		}
		
	}

}
