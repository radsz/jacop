/**
 *  Arithmetic.java 
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

package org.jacop.constraints.netflow;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class Arithmetic extends DecomposedConstraint {

	public static final IntVar NULL_VAR = new IntVar(){
		@Override
		public String toString() {
			return "NULL-var";
		}
	};

	private List<int[]> eqns;
	private List<IntVar> vars;
	private Map<IntVar, Integer> map;

	ArrayList<Constraint> decomposition;
	
	public Arithmetic() {
		this.eqns = new ArrayList<int[]>();
		this.vars = new ArrayList<IntVar>();
		this.map = new HashMap<IntVar, Integer>();

		vars.add(NULL_VAR);
		map.put(NULL_VAR, 0);
	}

	private int lookup(IntVar var) {
		Integer id = map.get(var);
		if (id == null) {
			map.put(var, id = vars.size());
			vars.add(var);
		}
		return id;
	}

	public void addEquation(IntVar[] vars, int[] coeffs) {
		addEquation(vars, coeffs, 0);
	}

	public void addEquation(IntVar[] vars, int[] coeffs, int constant) {
		if (vars.length == 0 || vars.length != coeffs.length)
			throw new IllegalArgumentException();

		int max = 1;
		for (int i = 0; i < vars.length; i++) {
			int id = lookup(vars[i]);
			if (max <= id)
				max = id + 1;
		}

		int[] eqn = new int[max];
		for (int i = 0; i < vars.length; i++) {
			int id = lookup(vars[i]);
			eqn[id] = coeffs[i];
		}
		eqn[0] = constant;
		eqns.add(eqn);
	}

	public void addXplusYeqZ(IntVar x, IntVar y, IntVar z) {
		IntVar[] vars = { x, y, z };
		int[] coeffs = { 1, 1, -1 };
		addEquation(vars, coeffs);
	}

	public void addXsubYeqZ(IntVar x, IntVar y, IntVar z) {
		addXplusYeqZ(z, y, x);
	}

	public void addSum(IntVar[] vars, IntVar sum) {
		int n = vars.length;
		IntVar[] _vars = Arrays.copyOf(vars, n + 1);
		int[] coeffs = new int[n + 1];

		Arrays.fill(coeffs, 1);
		_vars[n] = sum;
		coeffs[n] = -1;

		addEquation(_vars, coeffs);
	}


	public ArrayList<Constraint> primitiveDecomposition(Store store) {

		if (decomposition == null) {

			decomposition = new ArrayList<Constraint>();

			final IntVar ZERO = new IntVar(store, "Zero", 0, 0);

			for (int[] eqn : eqns) {
				ArrayList<IntVar> variables = new ArrayList<IntVar>();
				ArrayList<Integer> weights = new ArrayList<Integer>();

				for (int i = 0; i < eqn.length; i++)
					if (eqn[i] != 0) {
						variables.add(vars.get(i));
						weights.add(eqn[i]);
					}

				decomposition.add(new SumWeight(variables, weights, ZERO));
			}

			return decomposition;
		}
		else {

			ArrayList<Constraint> result = new ArrayList<Constraint>();

			final IntVar ZERO = new IntVar(store, "Zero", 0, 0);

			for (int[] eqn : eqns) {
				ArrayList<IntVar> variables = new ArrayList<IntVar>();
				ArrayList<Integer> weights = new ArrayList<Integer>();

				for (int i = 0; i < eqn.length; i++)
					if (eqn[i] != 0) {
						variables.add(vars.get(i));
						weights.add(eqn[i]);
					}

				result.add(new SumWeight(variables, weights, ZERO));
			}

			return result;

		}
		
	}

	private boolean optimize(final int[] sum) {
		boolean change = false;
		int[] sum1 = sum;
		int w1 = weight(sum1);

		for (int[] eqn : eqns) {
			int[] sum2 = transform(sum1, eqn);
			int w2 = weight(sum2);

			if (w1 > w2) {
				w1 = w2;
				sum1 = sum2;
				flip(eqn);
				change = true;
			}
		}
		System.arraycopy(sum1, 0, sum, 0, sum.length);
		return change;
	}

	private static int weight(int[] array) {
		int weight = 0;
		for (int i : array)
			weight += Math.abs(i);
		return weight;
	}

	private static int[] transform(int[] sum, int[] eqn) {
		int[] result = Arrays.copyOf(sum, sum.length);
		for (int i = 0; i < eqn.length; i++)
			result[i] -= 2 * eqn[i];
		return result;
	}

	private static void flip(int[] eqn) {
		for (int i = 0; i < eqn.length; i++)
			eqn[i] = -eqn[i];
	}

	private class ArithmeticBuilder extends NetworkBuilder {

		private ArithmeticBuilder(Store store, int[] sum) {
			
			super(new IntVar(store, "Zero-cost", 0, 0));

			// copy equations
			int size = Arithmetic.this.eqns.size();
			int[][] eqns = new int[size][];
			for (int i = 0; i < size; i++) {
				int[] eqn = Arithmetic.this.eqns.get(i);
				eqns[i] = Arrays.copyOf(eqn, eqn.length);
			}

			// create nodes
			Node root = addNode("source/sink", -sum[0]);
			Node[] nodes = new Node[eqns.length];
			flip(sum);
			
			for (int i = 0; i < nodes.length; i++)
				nodes[i] = addNode("Equation " + (i + 1), -eqns[i][0]);

			// create arcs
			for (int i = 0; i < nodes.length; i++) {
				int[] eqn = eqns[i];

				for (int var = 1; var < eqn.length; var++) {
					if (eqn[var] == 0)
						continue;

					int found = -1;
					for (int j = 1; j < nodes.length; j++) {
						int k = (i + j) % nodes.length;
						int[] eqn2 = eqns[k];
						if (var >= eqn2.length)
							continue;

						if (eqn[var] > 0 && eqn[var] <= -eqn2[var]) {
							found = k;
							break;
						}
						if (eqn[var] < 0 && -eqn[var] <= eqn2[var]) {
							found = k;
							break;
						}
					}

					int[] eqn2 = (found == -1) ? sum : eqns[found];
					Node n1 = nodes[i];
					Node n2 = (found == -1) ? root : nodes[found];

					if (eqn[var] > 0) {
						// TODO use variable-view instead
						for (int cnt = eqn[var]; cnt-- > 0;)
							addArc(n2, n1, 0, vars.get(var));
					} else {
						// TODO use variable-view instead
						for (int cnt = -eqn[var]; cnt-- > 0;)
							addArc(n1, n2, 0, vars.get(var));
					}

					eqn2[var] += eqn[var];
					eqn[var] = 0;
				}
			}

			// Assertions
			for (int[] eqn : eqns)
				for (int i = 1; i < eqn.length; i++)
					if (eqn[i] != 0)
						throw new AssertionError();

			for (int i = 1; i < sum.length; i++)
				if (sum[i] != 0)
					throw new AssertionError(Arrays.toString(sum));
		}
	}

	@Override
	public ArrayList<Constraint> decompose(Store store) {
	
		if (decomposition == null || decomposition.size() > 1) {
			
			decomposition = new ArrayList<Constraint>();
			int[] sum = new int[vars.size()];
			for (int[] eqn : eqns)
				for (int i = 0; i < eqn.length; i++)
					sum[i] += eqn[i];

			//		System.out.println(vars);
			//		System.out.println("sum   = " + Arrays.toString(sum));
			//		for (int i = 0; i < eqns.size(); i++)
			//			System.out.println("eqn[" + i +"] = "+Arrays.toString(eqns.get(i)));

			// System.out.println("Before: w = " + weight(sum) + "   " + Arrays.toString(sum));

			for (int it = 0; optimize(sum); it++)
				if (it > 2 * eqns.size())
					throw new AssertionError(it + " iterations");

			// System.out.println("After: w = " + weight(sum) + "   " + Arrays.toString(sum));
			
			decomposition.add( new ArithmeticBuilder(store, sum).build() );

		}

		return decomposition;
		
	}

	@Override
	public void imposeDecomposition(Store store) {

		if (decomposition == null)
			decompose(store);
		
		for (Constraint c : decomposition)
			store.impose(c);
				
	}
}
