/**
 *  Values.java 
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
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Stack;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Constraint Values counts number of different values on a list of Variables.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 * @version 4.2
 */

public class Values extends Constraint {

	static int counter = 1;

	/**
	 * It specifies a list of variables which are counted. 
	 */
	IntVar[] list;

	/**
	 * It specifies the counter of different values among variables on a given list. 
	 */
	IntVar count;

	Comparator<IntVar> minFDV = new FDVminimumComparator<IntVar>();

	static final boolean debug = false;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list", "count"};

	/**
	 * It constructs Values constraint.
	 * 
	 * @param list list of variables for which different values are being counted.
	 * @param count specifies the number of different values in the list. 
	 */
	public Values(IntVar[] list, IntVar count) {

		assert (list != null) : "List argument is null";
		assert (count != null) : "count argument is null";

		this.queueIndex = 1;

		numberId = counter++;
		numberArgs = (short) (list.length + 1);

		this.count = count;
		this.list = new IntVar[list.length];

		for (int i = 0; i < list.length; i++) {

			assert (list[i] != null) : i + "-th element of list is null";			
			this.list[i] = list[i];

		}
	}


	/**
	 * It constructs Values constraint.
	 * 
	 * @param list list of variables for which different values are being counted.
	 * @param count specifies the number of different values in the list. 
	 */
	public Values(ArrayList<? extends IntVar> list, IntVar count) {

		this(list.toArray(new IntVar[list.size()]), count);

	}

	@Override
	public void impose(Store store) {
		count.putConstraint(this);
		for (Var v : list)
			v.putConstraint(this);
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void consistency(Store store) {

		do {
			
			store.propagationHasOccurred = false;

			Arrays.sort(list, minFDV);

			if (debug)
				System.out.println("Sorted : \n" + this);

			int minNumberDifferent = 1, minimumMax = list[0].max();

			ArrayList<HashSet<Integer>> graph = new ArrayList<HashSet<Integer>>();
			int numberSingleton = 0;
			IntDomain singletonValues = new IntervalDomain();

			for (IntVar v : list) {

				// compute information for pruning list of Variables
				if (v.singleton()) {
					numberSingleton++;
					singletonValues.unionAdapt(v.min(), v.min());
				}

				// compute minimal value for count
				if (v.min() > minimumMax) {
					minNumberDifferent++;
					minimumMax = v.max();
				}
				if (v.max() < minimumMax)
					minimumMax = v.max();

				// build bi-partite graph for computing maximal value for count
				HashSet<Integer> nodeConnections = new HashSet<Integer>();
				for (ValueEnumeration e = v.dom().valueEnumeration(); e.hasMoreElements();)
					nodeConnections.add(e.nextElement());
				
				graph.add(nodeConnections);
			}

			// compute maximal value for count
			int maxNumberDifferent = bipartiteGraphMatching(graph);

			if (debug)
				System.out.println("Minimum number of different values = "
						+ minNumberDifferent);
			if (debug)
				System.out.println("Maximum number of different values = "
						+ maxNumberDifferent);

			count.domain.in(store.level, count, minNumberDifferent,
					maxNumberDifferent);

			if (debug)
				System.out.println("Number singleton values = "
						+ numberSingleton + " Values = " + singletonValues);

			if (count.max() == singletonValues.getSize() && numberSingleton < list.length) {
				for (IntVar v : list)
					if (!v.singleton())
						v.domain.in(store.level, v, singletonValues);
			} else {
				
				int diffMin = count.min() - singletonValues.getSize();
				int diffSingleton = list.length - numberSingleton;
				
				if (diffMin == diffSingleton)
					for (IntVar v : list)
						if (!v.singleton())
							v.domain.in(store.level, v, singletonValues.complement());
				
			}
			
		} while (store.propagationHasOccurred);
		
	}

	@Override
	public boolean satisfied() {
		boolean sat = true;
		int i = 0;
		if (count.singleton())
			while (sat && i < list.length) {
				sat = list[i].singleton();
				i++;
			}
		else
			return false;
		return sat;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(list.length + 1);

		variables.add(count);
		for (Var v : list)
			variables.add(v);
		return variables;
	}

	@Override
	public void removeConstraint() {
		count.removeConstraint(this);
		for (Var v : list)
			v.removeConstraint(this);
	}

	@Override
	public String toString() {

		StringBuffer result = new StringBuffer ( id () );
		result.append(" : Values([");
		for (int i = 0; i < list.length; i++) {
			if (i < list.length - 1)
				result.append( list[i] ).append( ", " );
			else
				result.append( list[i] );
		}
		result.append( "], " ).append( count ).append( " )" );
		return result.toString();
	}

	@SuppressWarnings("unchecked")
	int bipartiteGraphMatching(ArrayList<HashSet<Integer>> graph) {

		int u = 0;

		HashMap<Integer, Integer> matching = new HashMap<Integer, Integer>();
		HashMap<Integer, Integer> reverseMatching = new HashMap<Integer, Integer>();

		// Gready matching that creates initial matching
		u = 0;
		for (HashSet<Integer> s : graph) {
			for (Integer v : s) {
				if (!matching.containsValue(v)) {
					matching.put(u, v);
					reverseMatching.put(v, u);
					break;
				}
			}
			u++;
		}

		HashSet<Integer> values = new HashSet<Integer>();
		for (HashSet<Integer> s : graph)
			for (Integer v : s)
				values.add(v);

		u = 0;
		HashMap<Integer, Integer> valuesMap = new HashMap<Integer, Integer>();
		HashMap<Integer, Integer> valuesKeyMap = new HashMap<Integer, Integer>();
		for (Integer v : values) {
			valuesMap.put(v, u);
			valuesKeyMap.put(u, v);
			u++;
		}

		int uLength = graph.size();
		int vLength = values.size();
		int sink = 1 + uLength + vLength;

		HashSet<Integer>[] g = (HashSet<Integer>[]) new HashSet[1 + uLength + vLength];
		boolean done = false;
		byte[] b = new byte[g.length];
		Stack<Integer> stack = new Stack<Integer>();

		while (!done) {

			// Create G
			HashSet<Integer> nextNodesForSource = new HashSet<Integer>();
			u = 0;
			for (HashSet<Integer> hg : graph) {
				HashSet<Integer> next = new HashSet<Integer>();
				for (Integer v : hg)
					if (matching.containsKey(u)) {
						if (matching.get(u) != v)
							next.add(valuesMap.get(v) + uLength + 1);
					} else {
						next.add(valuesMap.get(v) + uLength + 1);
						nextNodesForSource.add(u + 1);
					}

				g[u + 1] = next;
				u++;
			}
			g[0] = nextNodesForSource;

			for (Integer v : values) {
				u = 1 + uLength + valuesMap.get(v);
				HashSet<Integer> next = new HashSet<Integer>();
				if (!reverseMatching.containsKey(v)) {
					next.add(sink);
					g[u] = next;
				} else {
					next.add(reverseMatching.get(v) + 1);
					g[u] = next;
				}
			}

			for (int i = 0; i < b.length; i++)
				b[i] = 0;

			done = true;

			// Alternating paths
			stack.push(0);
			while (!stack.empty()) {
				int top = stack.peek();
				while (g[top].size() > 0) {

					Iterator<Integer> nextNode = g[top].iterator();

					int first = (Integer) nextNode.next();

					if (debug)
						System.out.println("PUSH " + first);
					// remove edge (TOP, FIRST) from G

					if (debug) 
						System.out.println("Checking edge (" + top + ", " + first + ")");

					g[top].remove(first);
					if (first == sink)
						while (stack.size() >= 2) {
							int v = stack.pop();
							u = stack.pop();
							int vKey = valuesKeyMap.get(v - 1 - uLength);
							if (debug) 
								System.out.println("("+u+", "+v+")" + "("+ (int)(u-1) + ", " + vKey + ")");
							matching.remove(u - 1);
							matching.put(u - 1, vKey);
							reverseMatching.remove(vKey);
							reverseMatching.put(vKey, u - 1);
							done = false;
							if (debug)
								System.out.println("Improved matching " + matching);
						}
					else if (b[first] == 0) {
						b[first] = 1;
						stack.push(first);
						top = first;
					}
				}
				stack.pop();
			}
		}

		if (debug) {

			System.out.println("Final graph G");

			for (HashSet<Integer> s : g)
				System.out.println(u++ + ":" + s);

			System.out.println("Final matching (u, v): " + matching);
		}

		return matching.size();
	}


	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode

		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		//@todo, why so restrictive?
		return IntDomain.GROUND;
	}



	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			count.weight++;
			for (Var v : list)
				v.weight++;
		}
	}
}

class FDVminimumComparator<T extends IntVar> implements Comparator<T> {

	FDVminimumComparator() {
	}

	public int compare(T o1, T o2) {
		return (o1.min() - o2.min());
	}

}
