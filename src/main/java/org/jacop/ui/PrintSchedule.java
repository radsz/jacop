/**
 *  PrintSchedule.java 
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

package org.jacop.ui;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;

/**
 * Prints the computed schedule
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class PrintSchedule {

	class TaskScheduleComparator<T> implements Comparator<T> {

		TaskScheduleComparator() {
		}

		@SuppressWarnings("unchecked")
		public int compare(T o1, T o2) {
			return ((((ArrayList<IntVar>) o1).get(1)).min() * 1000 + 
					(((ArrayList<IntVar>) o1).get(3)).min())
					- (( ((ArrayList<IntVar>) o2).get(1)).min() * 1000 +
					  ( ((ArrayList<IntVar>) o2).get(3)).min());
		}
	}

	int[] d;

	ArrayList<String> n;

	IntVar[] t, r;

	/**
	 * It constructs PrintSchedule object.
	 * @param name name of the operations.
	 * @param t start time of the operations.
	 * @param d duration time of the operations.
	 * @param r resource usage of the operations.
	 */
	public PrintSchedule(String[] name, IntVar[] t, int[] d, IntVar[] r) {
		n = new ArrayList<String>();
		for (int i = 0; i < name.length; i++)
			n.add(name[i]);
		this.t = t;
		this.r = r;
		this.d = d;
	}

	/**
	 * It constructs PrintSchedule object.
	 * @param name name of the operations.
	 * @param t start time of the operations.
	 * @param d duration time of the operations.
	 * @param r resource usage of the operations.
	 */
	public PrintSchedule(String[] name, IntVar[] t, IntVar[] d, IntVar[] r) {
		n = new ArrayList<String>();
		this.t = t;
		this.r = r;
		this.d = new int[d.length];
		for (int i = 0; i < d.length; i++) {
			this.d[i] = d[i].min();
			n.add(name[i]);
		}
	}

	/**
	 * It constructs PrintSchedule object.
	 * @param name name of the operations.
	 * @param t start time of the operations.
	 * @param d duration time of the operations.
	 * @param r resource usage of the operations.
	 */
	public PrintSchedule(ArrayList<String> name, 
						ArrayList<? extends IntVar> t,
						ArrayList<Integer> d, 
						ArrayList<? extends IntVar> r) {
		n = name;
		this.t = new IntVar[t.size()];
		for (int i = 0; i < t.size(); i++)
			this.t[i] = t.get(i);
		this.r = new IntVar[r.size()];
		for (int i = 0; i < r.size(); i++)
			this.r[i] = r.get(i);
		this.d = new int[d.size()];
		for (int i = 0; i < d.size(); i++)
			this.d[i] = d.get(i);
	}

	/**
	 * It constructs PrintSchedule object.
	 * @param name name of the operations.
	 * @param t start time of the operations.
	 * @param d duration time of the operations.
	 * @param r resource usage of the operations.
	 */
	public PrintSchedule(ArrayList<String> name, 
						ArrayList<? extends IntVar> t,
						int[] d, 
						ArrayList<? extends IntVar> r) {
		n = name;
		this.t = new IntVar[t.size()];
		for (int i = 0; i < t.size(); i++)
			this.t[i] = t.get(i);
		this.r = new IntVar[r.size()];
		for (int i = 0; i < r.size(); i++)
			this.r[i] = r.get(i);
		this.d = d;
	}

	/**
	 * It constructs PrintSchedule object.
	 * @param name name of the operations.
	 * @param t start time of the operations.
	 * @param d duration time of the operations.
	 * @param r resource usage of the operations.
	 */

	public PrintSchedule(ArrayList<String> name, 
						 IntVar[] t, int[] d,
						 IntVar[] r) {
		n = name;
		this.t = t;
		this.r = r;
		this.d = d;
	}

	/**
	 * It constructs PrintSchedule object.
	 * @param name name of the operations.
	 * @param t start time of the operations.
	 * @param d duration time of the operations.
	 * @param r resource usage of the operations.
	 */
	public PrintSchedule(ArrayList<String> name, 
						IntVar[] t, IntVar[] d,
						IntVar[] r) {
		n = name;
		this.t = t;
		this.r = r;
		this.d = new int[d.length];
		for (int i = 0; i < d.length; i++)
			this.d[i] = d[i].min();
	}

	int findMaxR() {
		int m = 0;
		for (int i = 0; i < r.length; i++)
			if (m < r[i].min())
				m = r[i].min();
		return m;
	}

	int findMaxT() {
		int m = 0;
		for (int i = 0; i < d.length; i++)
			if (m < t[i].min() + d[i] - 1)
				m = t[i].min() + d[i] - 1;
		return m;
	}

	int findMinR() {
		int m = IntDomain.MaxInt;
		for (int i = 0; i < r.length; i++)
			if (m > r[i].min())
				m = r[i].min();
		return m;
	}

	String tab(int i) {
		String s = "";
		for (int k = 0; k < i; k++)
			s = s + " ";
		return s;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer("\n");

		ArrayList<?>[] TaskArr = new ArrayList[n.size()];
		for (int i = 0; i < n.size(); i++) {
			ArrayList<Object> V = new ArrayList<Object>();

			V.add(n.get(i));
			V.add(t[i]);
			V.add(d[i]);
			V.add(r[i]);

			TaskArr[i] = V;

		}

		Comparator<ArrayList<?>> c = new TaskScheduleComparator<ArrayList<?>>();
		Arrays.sort(TaskArr, c);

		int maxR = findMaxR();
		int minR = findMinR();
		int resSize = maxR - minR + 1;
		int maxT = findMaxT();
		
		result.append("\t").append(minR);
		
		//s = s + "\t" + minR;
		
		for (int i = minR + 1; i <= maxR; i++)
			result.append("\t\t").append(i);
		
		//	s = s + "\t\t" + i;
		
		result.append("\n");
		
		//s = s + "\n";

		for (int i = 0; i <= maxT; i++) {
			
			result.append(i).append("\t");
		//	s = s + i + "\t";
			int j = 0;
			// int k = 1;
			int start = ((IntVar) TaskArr[j].get(1)).min();
			int dur = (Integer) TaskArr[j].get(2);

			ArrayList<ArrayList<Integer>> Line = new ArrayList<ArrayList<Integer>>(resSize);

			for (int n = 0; n < resSize; n++)
				Line.add(new ArrayList<Integer>());

			while (start <= i && j < TaskArr.length) {
				int res = ((IntVar) TaskArr[j].get(3)).min();
				start = ((IntVar) TaskArr[j].get(1)).min();
				dur = (Integer) TaskArr[j].get(2);
				if (start <= i && start + dur > i) {
					Line.get(res - minR).add(j);
				}
				j++;
			}

			for (int r = 0; r < Line.size(); r++) {
				int sp = result.length();
				for (int ri = 0; ri < Line.get(r).size(); ri++) 
					result.append("[").append(TaskArr[Line.get(r).get(ri)].get(0)).append("]");
				
				if (Line.get(r).size() == 0)
					result.append("-");
			//		s = s + "-";
					
				result.append(tab(16 - result.length() + sp));
			//	s = s + tab(16 - s.length() + sp);

			}
			
			result.append("\n");
			// s = s + "\n";
		}
		
		return result.toString();
	//	return s;
	}

}
