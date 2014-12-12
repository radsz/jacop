/**
 *  FilterBenchmark.java 
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

package org.jacop.examples.fd.filters;

import java.util.ArrayList;

import org.jacop.constraints.Cumulative;
import org.jacop.constraints.Diff2;
import org.jacop.constraints.Max;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.CreditCalculator;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleMatrixSelect;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SmallestMax;
import org.jacop.search.SmallestMin;
import org.jacop.ui.PrintSchedule;

/**
 * This is a set of filter scheduling examples, commonly used in High-Level Synthesis.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class FilterBenchmark {

	static ArrayList<IntVar> Tc, Ts, Rs;

	static ArrayList<Integer> Ds;

	static ArrayList<String> Ns;

	static IntVar cost;

	/**
	 * It executes the program for number of filters, 
	 * number of resources (adders, multipliers) and
	 * number of different synthesis techniques (
	 * algorithmic pipelining, multiplier pipelining, 
	 * chaining, no special techniques).
	 * 
	 * @param args
	 */
	public static void main(String args[]) {

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		schedule();

		pipeMulSchedule();

		chainingSchedule();

		pipelineSchedule();

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

	}

	/**
	 * It solves available filters for different scenario
	 * consisting of different number of resources. 
	 */
	public static void schedule() {

		int dfqEx[][] = { { 1, 1 }, { 1, 2 }, { 1, 3 }, { 2, 2 }, { 1, 4 },
				{ 2, 3 } };
		for (int i = 0; i < dfqEx.length; i++) {
			int a = dfqEx[i][0], m = dfqEx[i][1];
			Store store = new Store();
			DFQ dfq = new DFQ();
			experiment1(store, dfq, a, m);
		}

		int firEx[][] = { { 1, 1 }, { 1, 2 }, { 2, 2 }, { 2, 3 } };
		for (int i = 0; i < firEx.length; i++) {
			int a = firEx[i][0], m = firEx[i][1];
			FIR fir = new FIR();
			Store store = new Store();
			experiment1(store, fir, a, m);
		}

		int arEx[][] = { { 1, 1 }, { 1, 2 }, { 1, 3 }, { 2, 3 }, { 2, 4 } };
		for (int i = 0; i < arEx.length; i++) {
			int a = arEx[i][0], m = arEx[i][1];
			AR ar = new AR(1, 1);
			Store store = new Store();
			experiment2(store, ar, a, m);
		}

		int ewfEx[][] = { { 1, 1 }, { 2, 1 }, { 2, 2 }, { 3, 3 } };
		for (int i = 0; i < ewfEx.length; i++) {
			int a = ewfEx[i][0], m = ewfEx[i][1];
			EWF ewf = new EWF();
			Store store = new Store();
			experiment1(store, ewf, a, m);
		}

		int ewfEx2[][] = { { 1, 1 }, { 2, 1 }, { 2, 2 }, { 3, 3 } };
		for (int i = 0; i < ewfEx2.length; i++) {
			int a = ewfEx2[i][0], m = ewfEx2[i][1];
			EWF ewf = new EWF(1, 1);
			Store store = new Store();
			experiment1(store, ewf, a, m);
		}

		int dctEx[][] = { { 1, 1 }, { 1, 2 }, { 2, 2 }, { 2, 3 }, { 3, 3 },
				{ 3, 4 }, { 4, 4 } };
		for (int i = 0; i < dctEx.length; i++) {
			int a = dctEx[i][0], m = dctEx[i][1];
			DCT dct = new DCT();
			Store store = new Store();
			experiment1(store, dct, a, m);
		}

	}

	
	/**
	 * It solves available filters for different scenario
	 * consisting of different number of resources. It
	 * performs pipelining of multiplier operations.
	 * 
	 */
	public static void pipeMulSchedule() {

		int dfqEx[][] = { { 1, 1 }, { 1, 2 } };
		for (int i = 0; i < dfqEx.length; i++) {
			int a = dfqEx[i][0], m = dfqEx[i][1];
			Store store = new Store();
			DFQ dfq = new DFQ();
			experiment1PM(store, dfq, a, m);
		}

		int firEx[][] = { { 1, 1 }, { 2, 1 }, { 2, 2 } };
		for (int i = 0; i < firEx.length; i++) {
			int a = firEx[i][0], m = firEx[i][1];
			FIR fir = new FIR();
			Store store = new Store();
			experiment1PM(store, fir, a, m);
		}

		int arEx[][] = { { 1, 1 }, { 1, 2 }, { 2, 2 }, { 2, 4 } };
		for (int i = 0; i < arEx.length; i++) {
			int a = arEx[i][0], m = arEx[i][1];
			AR ar = new AR();
			Store store = new Store();
			experiment2PM(store, ar, a, m);
		}

		int ewfEx[][] = { { 2, 1 }, { 3, 1 }, { 3, 2 } };
		for (int i = 0; i < ewfEx.length; i++) {
			int a = ewfEx[i][0], m = ewfEx[i][1];
			EWF ewf = new EWF();
			Store store = new Store();
			experiment1PM(store, ewf, a, m);
		}

		int dctEx[][] = { { 1, 1 }, { 2, 1 }, { 2, 2 }, { 3, 2 }, { 4, 3 },
				{ 5, 4 }, { 6, 5 } };
		for (int i = 0; i < dctEx.length; i++) {
			int a = dctEx[i][0], m = dctEx[i][1];
			DCT dct = new DCT();
			Store store = new Store();
			experiment1PM(store, dct, a, m);
		}

	}

	/**
	 * It solves available filters for different scenario
	 * consisting of different number of resources. It
	 * performs chaining of operations.
	 * 
	 */
	public static void chainingSchedule() {

		int dfqEx[][] = { { 1, 1, 3 }, { 1, 2, 3 }, { 2, 2, 3 } };
		;
		for (int i = 0; i < dfqEx.length; i++) {
			int a = dfqEx[i][0], m = dfqEx[i][1], s = dfqEx[i][2];
			Store store = new Store();
			DFQ dfq = new DFQ();
			experiment1C(store, dfq, a, m, s);
		}

		int firEx[][] = { { 2, 1, 2 }, { 2, 2, 2 }, { 3, 2, 2 }, { 1, 1, 3 },
				{ 2, 1, 3 }, { 3, 2, 3 } };
		for (int i = 0; i < firEx.length; i++) {
			int a = firEx[i][0], m = firEx[i][1], s = firEx[i][2];
			FIR fir = new FIR();
			Store store = new Store();
			experiment1C(store, fir, a, m, s);
		}

		int arEx[][] = { { 2, 2, 2 }, { 2, 3, 2 }, { 4, 4, 2 }, { 1, 1, 3 },
				{ 1, 2, 3 }, { 2, 2, 3 }, { 2, 3, 3 }, { 2, 4, 3 },
				{ 3, 4, 3 }, { 2, 2, 4 }, { 2, 3, 4 }, { 3, 4, 4 } };
		for (int i = 0; i < arEx.length; i++) {
			int a = arEx[i][0], m = arEx[i][1], s = arEx[i][2];
			AR ar = new AR();
			Store store = new Store();
			experiment1C(store, ar, a, m, s);
		}

		int ewfEx[][] = { { 2, 1, 2 }, { 3, 1, 2 }, { 1, 1, 3 }, { 2, 1, 3 },
				{ 3, 1, 3 }, { 1, 1, 4 }, { 2, 1, 4 }, { 3, 1, 4 } };
		for (int i = 0; i < ewfEx.length; i++) {
			int a = ewfEx[i][0], m = ewfEx[i][1], s = ewfEx[i][2];
			EWF ewf = new EWF();
			Store store = new Store();
			experiment1C(store, ewf, a, m, s);
		}

		int dctEx[][] = { { 2, 1, 2 }, { 2, 2, 2 }, { 3, 2, 2 }, { 4, 2, 2 },
				{ 4, 3, 2 }, { 5, 4, 2 }, { 1, 1, 3 }, { 2, 1, 3 },
				{ 3, 2, 3 }, { 4, 2, 3 }, { 5, 3, 3 } };
		for (int i = 0; i < dctEx.length; i++) {
			int a = dctEx[i][0], m = dctEx[i][1], s = dctEx[i][2];
			DCT dct = new DCT();
			Store store = new Store();
			experiment1C(store, dct, a, m, s);
		}

	}

	/**
	 * It solves available filters for different scenario
	 * consisting of different number of resources. It
	 * performs algorithmic pipelining.
	 * 
	 */
	public static void pipelineSchedule() {

		// **************** Pipeline schedules

		int dfqEx[][] = { { 1, 3 }, { 2, 3 } };
		;
		for (int i = 0; i < dfqEx.length; i++) {
			int a = dfqEx[i][0], m = dfqEx[i][1];
			Store store = new Store();
			DFQ dfqP = new DFQ();
			experiment1P(store, dfqP, a, m);
		}

		int firEx[][] = { { 2, 2 }, { 3, 3 }, { 3, 4 } };
		for (int i = 0; i < firEx.length; i++) {
			int a = firEx[i][0], m = firEx[i][1];
			FIR firP = new FIR();
			Store store = new Store();
			experiment1P(store, firP, a, m);
		}

		int arEx[][] = { { 2, 4 }, { 2, 6 }, { 3, 8 } };
		for (int i = 0; i < arEx.length; i++) {
			int a = arEx[i][0], m = arEx[i][1];
			AR arP = new AR();
			Store store = new Store();
			experiment1P(store, arP, a, m);
		}

		int ewfEx[][] = { { 3, 2 }, { 4, 2 }, { 4, 3 }, { 5, 4 } };
		for (int i = 0; i < ewfEx.length; i++) {
			int a = ewfEx[i][0], m = ewfEx[i][1];
			EWF ewfP = new EWF();
			Store store = new Store();
			experiment1P(store, ewfP, a, m);
		}

		int dctEx[][] = { { 4, 4 }, { 4, 5 }, { 5, 6 }, { 6, 7 }, { 7, 8 } };
		for (int i = 0; i < dctEx.length; i++) {
			int a = dctEx[i][0], m = dctEx[i][1];
			DCT dctP = new DCT();
			Store store = new Store();
			experiment1P(store, dctP, a, m);
		}

		int fftEx[][] = { { 1, 1 }, { 1, 2 }, { 2, 2 }, { 3, 4 } };
		for (int i = 0; i < fftEx.length; i++) {
			int a = fftEx[i][0], m = fftEx[i][1];
			FFT fftP = new FFT();
			Store store = new Store();
			experiment1P(store, fftP, a, m);
		}

	}

	/**
	 * It optimizes scheduling of filter operations.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 */
	public static void experiment1(Store store, 
								   Filter filter, 
								   int addNum,
								   int mulNum) {
		boolean result;

		System.out.println("\n\nTest of scheduling for " + filter.name()
				+ " example"); // without cumulative constraint");
		System.out.println("with " + addNum + " adders and " + mulNum
				+ " multipliers");
		System.out.println("add duration " + filter.addDel()
				+ " and mul duration " + filter.mulDel());

		ArrayList<ArrayList<IntVar>> TR = makeConstraints(store, filter, addNum,
				mulNum);

		IntVar[][] vars = new IntVar[TR.size()][];
		for (int i = 0; i < vars.length; i++) {
			vars[i] = new IntVar[TR.get(i).size()];
			for (int j = 0; j < vars[i].length; j++)
				vars[i][j] = TR.get(i).get(j);
		}

		SelectChoicePoint<IntVar> select = new SimpleMatrixSelect<IntVar>(vars,
				new SmallestMin<IntVar>(), new MostConstrainedStatic<IntVar>(),
				new IndomainMin<IntVar>(), 0);

		System.out.println("\nVariable store size: " + store.size()
				+ "\nNumber of constraints: " + store.numberConstraints());

		result = store.consistency();

		System.out.println("1. Constraints consistent = " + result);

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		Search<IntVar> label = new DepthFirstSearch<IntVar>();

		result = label.labeling(store, select, cost);

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

		if (result) {
			System.out.println("\n*** Yes");
			PrintSchedule Sch = new PrintSchedule(Ns, Ts, Ds, Rs);
			System.out.println(Sch);
		} else
			System.out.println("*** No");
	}

	/**
	 * It optimizes scheduling of filter operation in fashion allowing
	 * chaining of operations within one clock cycle.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 * @param clock number of time units within a clock.
	 */
	public static void experiment1C(Store store, 
								    Filter filter, 
								    int addNum,
								    int mulNum, 
								    int clock) {
		boolean result;

		System.out.println("\n\nTest of scheduling for " + filter.name()
				+ " example");
		System.out.println("with " + addNum + " adders and " + mulNum
				+ " multipliers;\nclock length: " + clock);
		System.out.println("add duration " + filter.addDel()
				+ " and mul duration " + filter.mulDel());

		ArrayList<ArrayList<IntVar>> TR = makeConstraintsChain(store, filter,
				addNum, mulNum, clock);

		IntVar[][] vars = new IntVar[TR.size()][];
		for (int i = 0; i < vars.length; i++) {
			vars[i] = new IntVar[TR.get(i).size()];
			for (int j = 0; j < vars[i].length; j++)
				vars[i][j] = TR.get(i).get(j);
		}

		SelectChoicePoint<IntVar> select = new SimpleMatrixSelect<IntVar>(vars,
				new SmallestMin<IntVar>(), new MostConstrainedStatic<IntVar>(),
				new IndomainMin<IntVar>(), 0);

		System.out.println("\nVariable store size: " + store.size()
				+ "\nNumber of constraints: " + store.numberConstraints());

		result = store.consistency();

		System.out.println("2. Constraints consistent = " + result);

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		Search<IntVar> label = new DepthFirstSearch<IntVar>();

		result = label.labeling(store, select, cost);

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

		if (result) {
			System.out.println("\n*** Yes");
			System.out.println("Schedule length: " + div(cost.min(), clock));
			PrintSchedule Sch = new PrintSchedule(Ns, Ts, Ds, Rs);
			System.out.println(Sch);
		} else
			System.out.println("*** No");
	}

	private static int div(int A, int B) {
		int Div, Rem;

		Div = A / B;
		Rem = A % B;
		return (Rem > 0) ? Div + 1 : Div;
	}

	/**
	 * It optimizes scheduling of filter operations in a fashion allowing
	 * pipelining of multiplication operations.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 */
	public static void experiment1PM(Store store, 
									 Filter filter, 
									 int addNum,
									 int mulNum) {
		boolean result;

		System.out.println("\n\nTest of scheduling for " + filter.name()
				+ " example with pipeline multiplier"); // without cumulative
														// constraint");
		System.out.println("with " + addNum + " adders and " + mulNum
				+ " multipliers");
		System.out.println("add duration " + filter.addDel()
				+ " and mul duration " + filter.mulDel());

		ArrayList<ArrayList<IntVar>> TR = makeConstraintsPipeMultiplier(store,
				filter, addNum, mulNum);

		IntVar[][] vars = new IntVar[TR.size()][];
		for (int i = 0; i < vars.length; i++) {
			vars[i] = new IntVar[TR.get(i).size()];
			for (int j = 0; j < vars[i].length; j++)
				vars[i][j] = TR.get(i).get(j);
		}

		SelectChoicePoint<IntVar> select = new SimpleMatrixSelect<IntVar>(vars,
				new SmallestMax<IntVar>(), new MostConstrainedStatic<IntVar>(),
				new IndomainMin<IntVar>(), 0);

		System.out.println("\nVariable store size: " + store.size()
				+ "\nNumber of constraints: " + store.numberConstraints());

		result = store.consistency();

		System.out.println("3. Constraints consistent = " + result);

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		Search<IntVar> label = new DepthFirstSearch<IntVar>();

		result = label.labeling(store, select, cost);

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

		if (result) {
			System.out.println("\n*** Yes");
			PrintSchedule Sch = new PrintSchedule(Ns, Ts, Ds, Rs);
			System.out.println(Sch);
		} else
			System.out.println("*** No");
	}

	/**
	 * It optimizes scheduling of filter operation in fashion allowing
	 * pipelining of multiplication operations.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 */
	public static void experiment2PM(Store store, 
									 Filter filter, 
									 int addNum,
									 int mulNum) {

		boolean result;

		System.out.println("\n\nTest of scheduling for " + filter.name()
				+ " example with pipeline multiplier"); // without cumulative
														// constraint");
		System.out.println("with " + addNum + " adders and " + mulNum
				+ " multipliers");
		System.out.println("add duration " + filter.addDel()
				+ " and mul duration " + filter.mulDel());

		makeConstraintsPipeMultiplier(store, filter, addNum, mulNum);

		IntVar[] varsTs = new IntVar[Ts.size()];
		for (int j = 0; j < varsTs.length; j++)
			varsTs[j] = Ts.get(j);

		IntVar[] varsRs = new IntVar[Rs.size()];
		for (int j = 0; j < varsRs.length; j++)
			varsRs[j] = Rs.get(j);

		SelectChoicePoint<IntVar> selectMC = new SimpleSelect<IntVar>(varsTs,
				new MostConstrainedStatic<IntVar>(), new SmallestDomain<IntVar>(),
				new IndomainMin<IntVar>());
		SelectChoicePoint<IntVar> selectIO = new SimpleSelect<IntVar>(varsRs, null, null,
				new IndomainMin<IntVar>());

		System.out.println("\nVariable store size: " + store.size()
				+ "\nNumber of constraints: " + store.numberConstraints());

		result = store.consistency();

		System.out.println("4. Constraints consistent = " + result);

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		Search<IntVar> label = new DepthFirstSearch<IntVar>();

		result = label.labeling(store, selectMC, cost);

		if (result) {
			label = new DepthFirstSearch<IntVar>();
			result = label.labeling(store, selectIO);
		}

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

		if (result) {
			System.out.println("\n*** Yes");
			PrintSchedule Sch = new PrintSchedule(Ns, Ts, Ds, Rs);
			System.out.println(Sch);
		} else
			System.out.println("*** No");
	}

	

	
	/**
	 * It optimizes scheduling of filter operations. It performs algorithmic 
	 * pipelining. 
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 */
	public static void experiment1P(Store store, 
									Filter filter, 
									int addNum,
									int mulNum) {
		
		boolean result;

		System.out.println("\n\nTest of pipeline scheduling for "
				+ filter.name() + " example without cumulative constraint");
		System.out.println("with " + addNum + " adders and " + mulNum
				+ " multipliers");
		System.out.println("add duration " + filter.addDel()
				+ " and mul duration " + filter.mulDel());

		ArrayList<ArrayList<IntVar>> TR = makeConstraintsPipeline(store, filter,
				addNum, mulNum);

		int tAdd = (filter.noAdd() * filter.addDel()) / addNum;
		int rAdd = (filter.noAdd() * filter.addDel()) % addNum;
		int addLB = (rAdd == 0) ? tAdd : tAdd + 1;
		int tMul = (filter.noMul() * filter.mulDel()) / mulNum;
		int rMul = (filter.noMul() * filter.mulDel()) % mulNum;
		int mulLB = (rMul == 0) ? tMul : tMul + 1;
		int pipeLB = (addLB > mulLB) ? addLB : mulLB;
		System.out.println("Lower bound = " + pipeLB);

		ArrayList<IntVar> cc = new ArrayList<IntVar>();
		cc.add(new IntVar(store, 10000, 10000));
		cc.add(cost);
		TR.add(cc);

		IntVar[][] vars = new IntVar[TR.size()][];
		for (int i = 0; i < vars.length; i++) {
			vars[i] = new IntVar[TR.get(i).size()];
			for (int j = 0; j < vars[i].length; j++)
				vars[i][j] = TR.get(i).get(j);
		}

		SelectChoicePoint<IntVar> select = new SimpleMatrixSelect<IntVar>(vars,
				new SmallestMax<IntVar>(), new MostConstrainedStatic<IntVar>(),
				new IndomainMin<IntVar>(), 0);

		CreditCalculator<IntVar> credit = new CreditCalculator<IntVar>(TR.size(), 20, 10);

		Search<IntVar> search = new DepthFirstSearch<IntVar>();

		if (search.getConsistencyListener() == null)
			search.setConsistencyListener(credit);
		else
			search.getConsistencyListener().setChildrenListeners(credit);

		if (search.getExitChildListener() == null)
			search.setExitChildListener(credit);
		else
			search.getExitChildListener().setChildrenListeners(credit);
		
		if (search.getTimeOutListener() == null)
			search.setTimeOutListener(credit);
		else
			search.getTimeOutListener().setChildrenListeners(credit);

		System.out.println("\nVariable store size: " + store.size()
				+ "\nNumber of constraints: " + store.numberConstraints());

		store.impose(new XgteqC(cost, pipeLB));
		result = store.consistency();

		System.out.println("6. Constraints consistent = " + result);

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		result = search.labeling(store, select, cost);

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

		if (result) {
			System.out.println("\n*** Yes");
			PrintSchedule Sch = new PrintSchedule(Ns, Ts, Ds, Rs);
			System.out.println(Sch);
		} else
			System.out.println("*** No");
	}

	/**
	 * It optimizes scheduling of filter operations. It performs
	 * algorithmic pipelining three times.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 */
	public static void experiment2P(Store store, 
									Filter filter, 
									int addNum,
									int mulNum) {
		
		boolean result;

		System.out.println("\n\nTest of pipeline scheduling for "
				+ filter.name() + " example without cumulative constraint");
		System.out.println("with " + addNum + " adders and " + mulNum
				+ " multipliers");
		System.out.println("add duration " + filter.addDel()
				+ " and mul duration " + filter.mulDel());

		ArrayList<ArrayList<IntVar>> TR = makeConstraintsPipeline(store, filter,
				addNum, mulNum);

		int tAdd = (filter.noAdd() * filter.addDel()) / addNum;
		int rAdd = (filter.noAdd() * filter.addDel()) % addNum;
		int addLB = (rAdd == 0) ? tAdd : tAdd + 1;
		int tMul = (filter.noMul() * filter.mulDel()) / mulNum;
		int rMul = (filter.noMul() * filter.mulDel()) % mulNum;
		int mulLB = (rMul == 0) ? tMul : tMul + 1;
		int pipeLB = (addLB > mulLB) ? addLB : mulLB;
		System.out.println("Lower bound = " + pipeLB);

		IntVar[] varsTs = new IntVar[Ts.size()];
		for (int j = 0; j < varsTs.length; j++)
			varsTs[j] = Ts.get(j);

		IntVar[] varsRs = new IntVar[Rs.size()];
		for (int j = 0; j < varsRs.length; j++)
			varsRs[j] = Rs.get(j);

		SelectChoicePoint<IntVar> selectMC = new SimpleSelect<IntVar>(varsTs,
				new SmallestMin<IntVar>(), new MostConstrainedStatic<IntVar>(),
				new IndomainMin<IntVar>());
		SelectChoicePoint<IntVar> selectIO = new SimpleSelect<IntVar>(varsRs, null, null,
				new IndomainMin<IntVar>());

		CreditCalculator<IntVar> credit = new CreditCalculator<IntVar>(TR.size() / 2, 5, 10);

		Search<IntVar> search = new DepthFirstSearch<IntVar>();

		if (search.getConsistencyListener() == null)
			search.setConsistencyListener(credit);
		else
			search.getConsistencyListener().setChildrenListeners(credit);

		search.getExitChildListener().setChildrenListeners(credit);
		search.getTimeOutListener().setChildrenListeners(credit);

		System.out.println("\nVariable store size: " + store.size()
				+ "\nNumber of constraints: " + store.numberConstraints());

		store.impose(new XgteqC(cost, pipeLB));

		result = store.consistency();

		System.out.println("7. Constraints consistent = " + result);

		result = search.labeling(store, selectMC, cost);

		if (result) {
			search = new DepthFirstSearch<IntVar>();
			result = search.labeling(store, selectIO);
		}

		if (result) {
			System.out.println("\n*** Yes");
			PrintSchedule Sch = new PrintSchedule(Ns, Ts, Ds, Rs);
			System.out.println(Sch);
		} else
			System.out.println("*** No");
	}

	/**
	 * It optimizes scheduling of filter operations.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 */
	public static void experiment2(Store store, 
								   Filter filter, 
								   int addNum,
								   int mulNum) {
		
		boolean result;

		System.out.println("\n\nTest of scheduling for " + filter.name()
				+ " example"); // without cumulative constraint");
		System.out.println("with " + addNum + " adders and " + mulNum
				+ " multipliers");
		System.out.println("add duration " + filter.addDel()
				+ " and mul duration " + filter.mulDel());

		makeConstraints(store, filter, addNum, mulNum);

		IntVar[] varsTs = new IntVar[Ts.size()];
		for (int j = 0; j < varsTs.length; j++)
			varsTs[j] = Ts.get(j);

		IntVar[] varsRs = new IntVar[Rs.size()];
		for (int j = 0; j < varsRs.length; j++)
			varsRs[j] = Rs.get(j);

		SelectChoicePoint<IntVar> selectMC = new SimpleSelect<IntVar>(varsTs,
				new MostConstrainedStatic<IntVar>(), new SmallestDomain<IntVar>(),
				new IndomainMin<IntVar>());
		SelectChoicePoint<IntVar> selectIO = new SimpleSelect<IntVar>(varsRs, null, null,
				new IndomainMin<IntVar>());

		System.out.println("\nVariable store size: " + store.size()
				+ "\nNumber of constraints: " + store.numberConstraints());

		result = store.consistency();

		System.out.println("8. Constraints consistent = " + result);

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		Search<IntVar> search = new DepthFirstSearch<IntVar>();
	
		result = search.labeling(store, selectMC, cost);

		if (result) {
			search = new DepthFirstSearch<IntVar>();
			result = search.labeling(store, selectIO);
		}

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

		if (result) {
			System.out.println("\n*** Yes");
			PrintSchedule Sch = new PrintSchedule(Ns, Ts, Ds, Rs);
			System.out.println(Sch);
		} else
			System.out.println("*** No");
	}

	/**
	 * It optimizes scheduling of filter operation in fashion allowing
	 * chaining of operations within one clock cycle.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 * @param clock number of time units within a clock.
	 */
	public static void experiment2C(Store store, 
									Filter filter, 
									int addNum,
									int mulNum, 
									int clock) {

		boolean result;

		System.out.println("\n\nTest of scheduling for " + filter.name()
				+ " example");// without cumulative constraint");
		System.out.println("with " + addNum + " adders and " + mulNum
				+ " multipliers;\nclock length: " + clock);
		System.out.println("add duration " + filter.addDel()
				+ " and mul duration " + filter.mulDel());

		makeConstraintsChain(store, filter, addNum, mulNum, clock);

		IntVar[] varsTs = new IntVar[Ts.size()];
		for (int j = 0; j < varsTs.length; j++)
			varsTs[j] = Ts.get(j);

		IntVar[] varsRs = new IntVar[Rs.size()];
		for (int j = 0; j < varsRs.length; j++)
			varsRs[j] = Rs.get(j);

		SelectChoicePoint<IntVar> selectMC = new SimpleSelect<IntVar>(varsTs,
				new SmallestMin<IntVar>(), new MostConstrainedStatic<IntVar>(),
				new IndomainMin<IntVar>());
		SelectChoicePoint<IntVar> selectIO = new SimpleSelect<IntVar>(varsRs, null, null,
				new IndomainMin<IntVar>());

		System.out.println("\nVariable store size: " + store.size()
				+ "\nNumber of constraints: " + store.numberConstraints());

		result = store.consistency();

		System.out.println("10. Constraints consistent = " + result);

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		Search<IntVar> search = new DepthFirstSearch<IntVar>();

		result = search.labeling(store, selectMC, cost);

		if (result) {
			search = new DepthFirstSearch<IntVar>();
			result = search.labeling(store, selectIO);
		}

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

		if (result) {
			System.out.println("\n*** Yes");
			System.out.println("Schedule length: " + div(cost.min(), clock));
			PrintSchedule Sch = new PrintSchedule(Ns, Ts, Ds, Rs);
			System.out.println(Sch);
		} else
			System.out.println("*** No");
	}

	/**
	 * It creates constraint model for scheduling of filter operations.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 * @return start time and resource assignment variables describing the scheduling problem.
	 */
	public static ArrayList<ArrayList<IntVar>> makeConstraints(Store store,
																 Filter filter, 
																 int addNum, 
																 int mulNum) {
		
		final int addMin = 1;
		final int addMax = addMin + addNum - 1;
		final int mulMin = addMax + 1;
		final int mulMax = mulMin + mulNum - 1;
		
		String nameT = "T";
		String nameR = "R";

		int[][] dependencies = filter.dependencies();
		int[] delays = filter.delays();
		int[] lastOp = filter.lastOp();
		IntVar addDelay = new IntVar(store, filter.addDel(), filter.addDel());
		IntVar mulDelay = new IntVar(store, filter.mulDel(), filter.mulDel());
		IntVar one = new IntVar(store, 1, 1);

		IntVar T[] = new IntVar[delays.length];
		IntVar R[] = new IntVar[delays.length];
		int D[] = new int[delays.length];

		IntVar Tadd[] = new IntVar[filter.noAdd()];
		IntVar Radd[] = new IntVar[filter.noAdd()];
		IntVar Dadd[] = new IntVar[filter.noAdd()];
		IntVar ResAdd[] = new IntVar[filter.noAdd()];

		IntVar Tmul[] = new IntVar[filter.noMul()];
		IntVar Rmul[] = new IntVar[filter.noMul()];
		IntVar Dmul[] = new IntVar[filter.noMul()];
		IntVar ResMul[] = new IntVar[filter.noMul()];

		int j = 0, k = 0;
		for (int i = 0; i < delays.length; i++) {
			String t = nameT + i;
			String r = nameR + i;

			T[i] = new IntVar(store, t, 0, 100);

			if (filter.ids()[i] == filter.addId()) {
				R[i] = new IntVar(store, r, addMin, addMax);
				Tadd[j] = T[i];
				Radd[j] = R[i];
				Dadd[j] = addDelay;
				D[i] = filter.addDel();
				ResAdd[j] = one;

				j++;
			} else {
				R[i] = new IntVar(store, r, mulMin, mulMax);
				Tmul[k] = T[i];
				Rmul[k] = R[i];
				Dmul[k] = mulDelay;
				D[i] = filter.mulDel();
				ResMul[k] = one;

				k++;
			}
		}

		for (int i = 0; i < dependencies.length; i++) {
			store.impose(new XplusClteqZ(T[dependencies[i][0]],
					delays[dependencies[i][0]], T[dependencies[i][1]]));
		}

		ArrayList<IntVar> endOp = new ArrayList<IntVar>();
		for (int i = 0; i < lastOp.length; i++) {
			IntVar end = new IntVar(store, 0, 100);
			store.impose(new XplusCeqZ(T[lastOp[i]], D[lastOp[i]], end));
			endOp.add(end);
		}
		
		cost = new IntVar(store, 0, 100);
		store.impose(new Max(endOp, cost));

		store.impose(new Diff2(Tadd, Radd, Dadd, ResAdd));
		store.impose(new Diff2(Tmul, Rmul, Dmul, ResMul));

		IntVar limitAdd = new IntVar(store, 1, addNum);
		store.impose(new Cumulative(Tadd, Dadd, ResAdd, limitAdd, true, false));
		IntVar limitMul = new IntVar(store, 1, mulNum);
		store.impose(new Cumulative(Tmul, Dmul, ResMul, limitMul, true, false));

		Ts = new ArrayList<IntVar>();
		for (IntVar v : T)
			Ts.add(v);
		Rs = new ArrayList<IntVar>();
		for (IntVar v : R)
			Rs.add(v);
		Ds = new ArrayList<Integer>();
		for (Integer v : D)
			Ds.add(v);

		Ns = filter.names();

		return makeLabelingList(T, R);
	}

	/**
	 * It creates constraint model for scheduling of filter operation in fashion allowing
	 * pipelining of multiplication operations.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 * @return start time and resource assignment variables describing the scheduling problem.
	 */
	public static ArrayList<ArrayList<IntVar>> 
				makeConstraintsPipeMultiplier(Store store, 
											  Filter filter, 
											  int addNum, 
											  int mulNum) {
		
		final int addMin = 1;
		final int addMax = addMin + addNum - 1;
		final int mulMin = addMax + 1;
		final int mulMax = mulMin + mulNum - 1;
		
		String nameT = "T";
		String nameR = "R";

		int[][] dependencies = filter.dependencies();
		int[] delays = filter.delays();
		int[] lastOp = filter.lastOp();
		
		IntVar addDelay = new IntVar(store, filter.addDel(), filter.addDel());
		IntVar mulDelay = new IntVar(store, 1, 1); // since pipelined multiplier
		// the effective delay is 1; filter.mulDel(), filter.mulDel());
		IntVar one = new IntVar(store, 1, 1);

		IntVar T[] = new IntVar[delays.length];
		IntVar R[] = new IntVar[delays.length];
		int D[] = new int[delays.length];

		IntVar Tadd[] = new IntVar[filter.noAdd()];
		IntVar Radd[] = new IntVar[filter.noAdd()];
		IntVar Dadd[] = new IntVar[filter.noAdd()];
		IntVar ResAdd[] = new IntVar[filter.noAdd()];

		IntVar Tmul[] = new IntVar[filter.noMul()];
		IntVar Rmul[] = new IntVar[filter.noMul()];
		IntVar Dmul[] = new IntVar[filter.noMul()];
		IntVar ResMul[] = new IntVar[filter.noMul()];

		int j = 0, k = 0;
		for (int i = 0; i < delays.length; i++) {
			String t = nameT + i;
			String r = nameR + i;

			T[i] = new IntVar(store, t, 0, 100);

			if (filter.ids()[i] == filter.addId()) {

				R[i] = new IntVar(store, r, addMin, addMax);
				Tadd[j] = T[i];
				Radd[j] = R[i];
				Dadd[j] = addDelay;
				D[i] = filter.addDel();
				ResAdd[j] = one;

				j++;
			} else {
				R[i] = new IntVar(store, r, mulMin, mulMax);
				Tmul[k] = T[i];
				Rmul[k] = R[i];
				Dmul[k] = mulDelay;
				D[i] = filter.mulDel();
				ResMul[k] = one;
				k++;
			}
		}

		for (int i = 0; i < dependencies.length; i++) {
			store.impose(new XplusClteqZ(T[dependencies[i][0]],
					delays[dependencies[i][0]], T[dependencies[i][1]]));
		}

		ArrayList<IntVar> endOp = new ArrayList<IntVar>();
		for (int i = 0; i < lastOp.length; i++) {
			IntVar end = new IntVar(store, 0, 100);
			store.impose(new XplusCeqZ(T[lastOp[i]], D[lastOp[i]], end));
			endOp.add(end);
		}
		
		cost = new IntVar(store, 0, 100);
		store.impose(new Max(endOp, cost));

		store.impose(new Diff2(Tadd, Radd, Dadd, ResAdd));
		store.impose(new Diff2(Tmul, Rmul, Dmul, ResMul));

		IntVar limitAdd = new IntVar(store, 0, addNum);
		store.impose(new Cumulative(Tadd, Dadd, ResAdd, limitAdd, true, false));
		IntVar limitMul = new IntVar(store, 0, mulNum);
		store.impose(new Cumulative(Tmul, Dmul, ResMul, limitMul, true, false));

		Ts = new ArrayList<IntVar>();
		for (IntVar v : T)
			Ts.add(v);
		Rs = new ArrayList<IntVar>();
		for (IntVar v : R)
			Rs.add(v);
		Ds = new ArrayList<Integer>();
		for (Integer v : D)
			Ds.add(v);

		Ns = filter.names();
		
		return makeLabelingList(T, R);
	}

	
	/**
	 * It creates constraint model for scheduling of filter operation in fashion allowing
	 * chaining of operations within one clock cycle.
	 * 
	 * @param store the constraint store in which the constraints are imposed.
	 * @param filter the filter being scheduled.
	 * @param addNum number of adders available.
	 * @param mulNum number of multipliers available.
	 * @param clk number of time units within a clock.
	 * @return start time and resource assignment variables describing the scheduling problem.
	 */
	public static ArrayList<ArrayList<IntVar>> 
						makeConstraintsChain(Store store,
											 Filter filter, 
											 int addNum, 
											 int mulNum, 
											 int clk) {
		
		final int addMin = 1;
		final int addMax = addMin + addNum - 1;
		final int mulMin = addMax + 1;
		final int mulMax = mulMin + mulNum - 1;
		
		String nameT = "T";
		String nameR = "R";

		int[][] dependencies = filter.dependencies();
		int[] delays = filter.delays();
		int[] lastOp = filter.lastOp();
		
		IntVar addDelay = new IntVar(store, filter.addDel(), filter.addDel());
		IntVar mulDelay = new IntVar(store, filter.mulDel(), filter.mulDel());
		IntVar one = new IntVar(store, 1, 1);

		IntVar T[] = new IntVar[delays.length];
		IntVar Tclock[] = new IntVar[delays.length];
		IntVar Tstep[] = new IntVar[delays.length];
		IntVar R[] = new IntVar[delays.length];
		int D[] = new int[delays.length];

		IntVar Tadd[] = new IntVar[filter.noAdd()];
		IntVar TaddClock[] = new IntVar[filter.noAdd()];
		IntVar Radd[] = new IntVar[filter.noAdd()];
		IntVar Dadd[] = new IntVar[filter.noAdd()];
		IntVar ResAdd[] = new IntVar[filter.noAdd()];

		IntVar Tmul[] = new IntVar[filter.noMul()];
		IntVar TmulClock[] = new IntVar[filter.noMul()];
		IntVar Rmul[] = new IntVar[filter.noMul()];
		IntVar Dmul[] = new IntVar[filter.noMul()];
		IntVar DmulClock[] = new IntVar[filter.noMul()];
		IntVar ResMul[] = new IntVar[filter.noMul()];

		int j = 0, k = 0;
		for (int i = 0; i < delays.length; i++) {
			String t = nameT + i;
			String r = nameR + i;

			T[i] = new IntVar(store, t, 0, 1000);
			Tclock[i] = new IntVar(store, "Tclock" + i, 0, 100);

			if (filter.ids()[i] == filter.addId()) {

				Tstep[i] = new IntVar(store, "Tstep" + i, 0, clk - filter.addDel());
				R[i] = new IntVar(store, r, addMin, addMax);
				Tadd[j] = T[i];
				TaddClock[j] = Tclock[i];
				Radd[j] = R[i];
				Dadd[j] = addDelay;
				D[i] = filter.addDel();
				ResAdd[j] = one;

				j++;
			} else {
				Tstep[i] = new IntVar(store, "Tstep" + i, 0, clk - filter.mulDel());
				R[i] = new IntVar(store, r, mulMin, mulMax);
				Tmul[k] = T[i];
				TmulClock[k] = Tclock[i];
				Rmul[k] = R[i];
				D[i] = filter.mulDel();
				Dmul[k] = mulDelay;
				DmulClock[k] = addDelay;
				ResMul[k] = one;

				k++;
			}

			IntVar temp = new IntVar(store, 0, 1000);
			store.impose(new XmulCeqZ(Tclock[i], clk, temp));
			store.impose(new XplusYeqZ(temp, Tstep[i], T[i]));
		}

		for (int i = 0; i < dependencies.length; i++) {
			store.impose(new XplusClteqZ(T[dependencies[i][0]],
					delays[dependencies[i][0]], T[dependencies[i][1]]));
		}

		ArrayList<IntVar> endOp = new ArrayList<IntVar>();
		for (int i = 0; i < lastOp.length; i++) {
			IntVar end = new IntVar(store, 0, 1000);
			store.impose(new XplusCeqZ(T[lastOp[i]], D[lastOp[i]], end));
			endOp.add(end);
		}
		
		cost = new IntVar(store, 0, 1000);
		store.impose(new Max(endOp, cost));

		store.impose(new Diff2(Tadd, Radd, Dadd, ResAdd));
		store.impose(new Diff2(Tmul, Rmul, Dmul, ResMul));

		store.impose(new Diff2(TmulClock, Rmul, DmulClock, ResMul));

		store.impose(new Diff2(TaddClock, Radd, Dadd, ResAdd));

		IntVar limitAdd = new IntVar(store, 1, addNum);
		store.impose(new Cumulative(TaddClock, Dadd, ResAdd, limitAdd, true,
				false));
		IntVar limitMul = new IntVar(store, 1, mulNum);
		store.impose(new Cumulative(Tmul, Dmul, ResMul, limitMul, true, false));

		Ts = new ArrayList<IntVar>();
		for (IntVar v : T)
			Ts.add(v);
		Rs = new ArrayList<IntVar>();
		for (IntVar v : R)
			Rs.add(v);
		Ds = new ArrayList<Integer>();
		for (Integer v : D)
			Ds.add(v);

		Ns = filter.names();

		return makeLabelingList(T, R);
	}

	
	/**
	 * It creates a model for optimization of scheduling of operations of a given filter. 
	 * The pipelined model assumes that the filter is unrolled three times.
	 * 
	 * @param store constraint store in which the constraints are imposed.
	 * @param filter filter for which pipelined execution is optimized.
	 * @param addNum number of available adders
	 * @param mulNum number of available multipliers.
	 * @return variables corresponding to start time and resource assignment of the filter operations.
	 */
	public static ArrayList<ArrayList<IntVar>> 
				makeConstraintsPipeline(Store store, 
										Filter filter, 
										int addNum, 
										int mulNum) {
		
		final int addMin = 1;
		final int addMax = addMin + addNum - 1;
		final int mulMin = addMax + 1;
		final int mulMax = mulMin + mulNum - 1;
		
		String nameT = "T";
		String nameR = "R";

		int[][] dependencies = filter.dependencies();
		int[] delays = filter.delays();
		int[] lastOp = filter.lastOp();
		IntVar addDelay = new IntVar(store, filter.addDel(), filter.addDel());
		IntVar mulDelay = new IntVar(store, filter.mulDel(), filter.mulDel());
		IntVar pipe = new IntVar(store, "InitRate", 1, 100);
		IntVar pipe2 = new IntVar(store, "InitRate*2", 1, 100);
		store.impose(new XmulCeqZ(pipe, 2, pipe2));
		IntVar pipe3 = new IntVar(store, "InitRate*3", 1, 100);
		store.impose(new XmulCeqZ(pipe, 3, pipe3));
		IntVar one = new IntVar(store, 1, 1);

		IntVar T[] = new IntVar[delays.length];
		IntVar Ta[] = new IntVar[delays.length];
		IntVar Tb[] = new IntVar[delays.length];
		IntVar R[] = new IntVar[delays.length];
		int D[] = new int[delays.length];

		IntVar Tadd[] = new IntVar[3 * filter.noAdd()];
		IntVar Radd[] = new IntVar[3 * filter.noAdd()];
		IntVar Dadd[] = new IntVar[3 * filter.noAdd()];
		IntVar ResAdd[] = new IntVar[3 * filter.noAdd()];

		IntVar Tmul[] = new IntVar[3 * filter.noMul()];
		IntVar Rmul[] = new IntVar[3 * filter.noMul()];
		IntVar Dmul[] = new IntVar[3 * filter.noMul()];
		IntVar ResMul[] = new IntVar[3 * filter.noMul()];

		int j = 0, k = 0;

		for (int i = 0; i < delays.length; i++) {
			String t = nameT + i;
			String ta = nameT + "a" + i;
			String tb = nameT + "b" + i;
			String r = nameR + i;

			T[i] = new IntVar(store, t, 0, 100);
			Ta[i] = new IntVar(store, ta, 0, 100);
			Tb[i] = new IntVar(store, tb, 0, 100);
			store.impose(new XplusYeqZ(T[i], pipe, Ta[i]));
			store.impose(new XplusYeqZ(T[i], pipe2, Tb[i]));

			if (filter.ids()[i] == filter.addId()) {

				R[i] = new IntVar(store, r, addMin, addMax);
				Tadd[3 * j] = T[i];
				Tadd[3 * j + 1] = Ta[i];
				Tadd[3 * j + 2] = Tb[i];
				Radd[3 * j] = R[i];
				Radd[3 * j + 1] = R[i];
				Radd[3 * j + 2] = R[i];
				Dadd[3 * j] = addDelay;
				Dadd[3 * j + 1] = addDelay;
				Dadd[3 * j + 2] = addDelay;
				D[i] = filter.addDel();
				ResAdd[3 * j] = one;
				ResAdd[3 * j + 1] = one;
				ResAdd[3 * j + 2] = one;

				j++;
			} else {
				R[i] = new IntVar(store, r, mulMin, mulMax);
				Tmul[3 * k] = T[i];
				Tmul[3 * k + 1] = Ta[i];
				Tmul[3 * k + 2] = Tb[i];
				Rmul[3 * k] = R[i];
				Rmul[3 * k + 1] = R[i];
				Rmul[3 * k + 2] = R[i];
				Dmul[3 * k] = mulDelay;
				Dmul[3 * k + 1] = mulDelay;
				Dmul[3 * k + 2] = mulDelay;
				D[i] = filter.mulDel();
				ResMul[3 * k] = one;
				ResMul[3 * k + 1] = one;
				ResMul[3 * k + 2] = one;

				IntVar temp1 = new IntVar(store, 0, 100);
				store.impose(new XplusCeqZ(T[i], 1, temp1));
				store.impose(new XneqY(temp1, pipe));
				IntVar temp2 = new IntVar(store, 0, 100);
				store.impose(new XplusCeqZ(T[i], 1, temp2));
				store.impose(new XneqY(temp2, pipe2));

				k++;
			}
		}

		for (int i = 0; i < dependencies.length; i++) {
			store.impose(new XplusClteqZ(T[dependencies[i][0]],
					delays[dependencies[i][0]], T[dependencies[i][1]]));
		}

		ArrayList<IntVar> endOp = new ArrayList<IntVar>();
		for (int i = 0; i < lastOp.length; i++) {
			IntVar end = new IntVar(store, 0, 100);
			store.impose(new XplusCeqZ(T[lastOp[i]], D[lastOp[i]], end));
			endOp.add(end);
		}
		IntVar cost = new IntVar(store, 0, 100);
		store.impose(new Max(endOp, cost));

		store.impose(new XlteqY(cost, pipe3));

		store.impose(new Diff2(Tadd, Radd, Dadd, ResAdd));
		store.impose(new Diff2(Tmul, Rmul, Dmul, ResMul));

		Ts = new ArrayList<IntVar>();
		for (IntVar v : T)
			Ts.add(v);
		for (IntVar v : Ta)
			Ts.add(v);
		for (IntVar v : Tb)
			Ts.add(v);

		Rs = new ArrayList<IntVar>();
		for (IntVar v : R)
			Rs.add(v);
		for (IntVar v : R)
			Rs.add(v);
		for (IntVar v : R)
			Rs.add(v);

		Ds = new ArrayList<Integer>();
		for (Integer v : D)
			Ds.add(v);
		for (int v : D)
			Ds.add(v);
		for (int v : D)
			Ds.add(v);

		Ns = filter.namesPipeline();
		FilterBenchmark.cost = pipe;

		return makeLabelingList(T, R);
	}

	
	/**
	 * It creates an array of arrays using two arrays.
	 * 
	 * @param T an array of variables corresponding to start time of an operation.
	 * @param R an array of variables corresponding to resource of an operation.
	 * @return an array of arrays, each array containing one starttime and one resource assignment variable.
	 */
	public static ArrayList<ArrayList<IntVar>> makeLabelingList(IntVar[] T, 
																  IntVar[] R) {
		
		ArrayList<ArrayList<IntVar>> list = new ArrayList<ArrayList<IntVar>>();
		
		for (int i = 0; i < T.length; i++) {
			ArrayList<IntVar> TR = new ArrayList<IntVar>();
			TR.add(T[i]);
			TR.add(R[i]);
			list.add(TR);
		}
		return list;
	}
}
