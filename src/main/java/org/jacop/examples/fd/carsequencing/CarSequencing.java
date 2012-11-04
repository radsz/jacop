/**
 *  CarSequencing.java 
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

package org.jacop.examples.fd.carsequencing;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.regex.Pattern;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.ExtensionalSupportMDD;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.util.fsm.FSM;
import org.jacop.util.fsm.FSMState;
import org.jacop.util.fsm.FSMTransition;

/**
 * 
 * It is program to model and solve simple problems of car sequencing problem (CSPLIB-p1).
 * 
 * @author Radoslaw Szymanek
 * 
 */

public class CarSequencing extends ExampleFD {

	/**

	The format of the data files is as follows:

	 * First line: number of cars; number of options; number of classes.
	 * Second line: for each option, the maximum number of cars with that option in a block.
	 * Third line: for each option, the block size to which the maximum number refers.
	 * Then for each class: index no.; no. of cars in this class; for each option, whether or not this class requires it (1 or 0). 

	This is the example given in (Dincbas et al., ECAI88):

	 */

	/**
	 * A simple car sequencing problem.
	 */
	public static String[] problem = {
		"10 5 6", 
		"1 2 1 2 1",
		"2 3 3 5 5",
		"0 1 1 0 1 1 0", 
		"1 1 0 0 0 1 0",
		"2 2 0 1 0 0 1", 
		"3 2 0 1 0 1 0", 
		"4 2 1 0 1 0 0", 
		"5 2 1 1 0 0 0" 
	};

	
	/** Not easy car sequencing problem.
	100 5 22
	1 2 1 2 1
	2 3 3 5 5
	0 6 1 0 0 1 0 
	1 10 1 1 1 0 0 
	2 2 1 1 0 0 1 
	3 2 0 1 1 0 0 
	4 8 0 0 0 1 0 
	5 15 0 1 0 0 0 
	6 1 0 1 1 1 0 
	7 5 0 0 1 1 0 
	8 2 1 0 1 1 0 
	9 3 0 0 1 0 0 
	10 2 1 0 1 0 0 
	11 1 1 1 1 0 1 
	12 8 0 1 0 1 0 
	13 3 1 0 0 1 1 
	14 10 1 0 0 0 0 
	15 4 0 1 0 0 1 
	16 4 0 0 0 0 1 
	17 2 1 0 0 0 1 
	18 4 1 1 0 0 0 
	19 6 1 1 0 1 0 
	20 1 1 0 1 0 1 
	21 1 1 1 1 1 1 
	*/

	/**

	A valid sequence for this set of cars is:
	Class 	Options req.
	0 	1 0 1 1 0
	1 	0 0 0 1 0
	5 	1 1 0 0 0
	2 	0 1 0 0 1
	4 	1 0 1 0 0
	3 	0 1 0 1 0
	3 	0 1 0 1 0
	4 	1 0 1 0 0
	2 	0 1 0 0 1
	5 	1 1 0 0 0 

	*/

	/**
	 * It specifies number of cars.
	 */

	public int noCar;

	/**
	 * It specifies the no of options in the car sequencing problem. 
	 */
	public int noOption;

	/**
	 * It specifies the number of different car classes.
	 */
	public int noClass;

	/**
	 * For a given sequence length then can be different maximum number of cars with a given option.
	 */
	public int[] maxNoOfCarsPerOption; 

	/**
	 * The sequence length for which the maximum number restriction is specified.
	 */
	public int[] blockSizePerOption;

	/**
	 * It specifies how many cars of each option should be produced.
	 */
	public int[] noOfCarsPerClass;

	/**
	 * It specifies if the given class (the first dimension) requires 
	 * given option (the second dimension). 
	 */
	public boolean required[][];

	/**
	 * It specifies if the slide based decomposition of the regular constraint
	 * should be applied. This decomposition uses ternary extensional support 
	 * constraints. It achieves GAC if FSM is deterministic. 
	 */
	public boolean slideDecomposition = false;

	/**
	 * It specifies if the regular constraint should be used.
	 */
	public boolean regular = true;

	/**
	 * It specifies if one extensional constraint based on MDD created from FSM
	 * should be used. The translation process works if FSM is deterministic.
	 */
	public boolean extensionalMDD = false;

	/**
	 * It transforms string representation of the problem into an array of ints
	 * representation. It stores the whole description in the internal attributes. 
	 * 
	 * @param description array of strings representing the problem.
	 * @param example example in which the passed instance is stored.
	 */
	public static void readFromArray(String[] description, CarSequencing example) {

		Pattern pat = Pattern.compile(" ");
		String[] result = pat.split(description[0]);

		example.noCar = Integer.valueOf(result[0]);
		example.noOption = Integer.valueOf(result[1]);
		example.noClass = Integer.valueOf(result[2]);

		result = pat.split(description[1]);

		example.maxNoOfCarsPerOption = new int[example.noOption];

		for (int i = 0; i < result.length; i++)
			example.maxNoOfCarsPerOption[i] = Integer.valueOf(result[i]); 

		result = pat.split(description[2]);

		example.blockSizePerOption = new int[example.noOption];

		for (int i = 0; i < result.length; i++)
			example.blockSizePerOption[i] = Integer.valueOf(result[i]); 

		example.noOfCarsPerClass = new int[example.noClass];
		example.required = new boolean[example.noClass][example.noOption];

		for (int i = 3; i < description.length; i++) {
			// Reading info about each class.

			result = pat.split(description[i]);

			int classNo = Integer.valueOf(result[0]);

			example.noOfCarsPerClass[classNo] = Integer.valueOf(result[1]);

			for (int j = 2; j < result.length; j++)
				if (Integer.valueOf(result[j]) == 1)
					example.required[classNo][j-2] = true;

		} 

	}


	/**
	 * It creates a String representation of the problem being supplied.
	 * 
	 * @param example example in which the passed instance is stored.
	 * @return the string representation of the problem instance.
	 */
	public static String[] toStringArray(CarSequencing example) {

		String[] result = new String[example.noClass+3];

		result[0] = example.noCar + " " + example.noOption + " " + example.noClass;

		StringBuffer resultBuffer = new StringBuffer();

		for (int i = 0; i < example.noOption; i++) {
			resultBuffer.append(example.maxNoOfCarsPerOption[i]).append(" ");
		}

		result[1] = resultBuffer.toString().trim();

		resultBuffer = new StringBuffer();

		for (int i = 0; i < example.noOption; i++) {
			resultBuffer.append(example.blockSizePerOption[i]).append(" ");
		}

		result[2] = resultBuffer.toString().trim();

		for (int i = 0; i < example.noClass; i++) {

			resultBuffer = new StringBuffer();

			resultBuffer.append(i).append(" ");
			resultBuffer.append(example.noOfCarsPerClass[i]);

			for (int j = 0; j < example.noOption; j++)
				if (example.required[i][j])
					resultBuffer.append(" 1");
				else
					resultBuffer.append(" 0");

			result[i+3] = resultBuffer.toString();

		}	

		return result;

	}


	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();

		IntVar[] cars = new IntVar[noCar];

		for (int i = 0; i < noCar; i++) {
			cars[i] = new IntVar(store, "car" + (i+1), 0, noClass);
			vars.add(cars[i]);
		}

		for (int i = 0; i < noOption; i++) {

			IntervalDomain classesWithGivenOption = new IntervalDomain();
			for (int j = 0; j < noClass; j++)
				if (required[j][i])
					classesWithGivenOption.unionAdapt(j, j);

			// It uses Regular constraint.
			if (regular)
				store.imposeDecomposition(new Sequence(cars, classesWithGivenOption, blockSizePerOption[i], 0, maxNoOfCarsPerOption[i]));

			// It uses decomposition of Regular into ternary constraints.
			if (slideDecomposition) {
				DecomposedConstraint c = new Sequence(cars, classesWithGivenOption, blockSizePerOption[i], 0, maxNoOfCarsPerOption[i]);
				ArrayList<Constraint> decomposition = c.decompose(store);

				for (Constraint regular : decomposition)
					store.imposeDecomposition(regular);
			}

			// It uses replacement for Regular, namely one extensional support constraint
			// based on MDDs.
			if (extensionalMDD) {
				DecomposedConstraint c = new Sequence(cars, classesWithGivenOption, blockSizePerOption[i], 0, maxNoOfCarsPerOption[i]);
				ArrayList<Constraint> decomposition = c.decompose(store);

				for (Constraint constraint : decomposition) {
					Regular regular = (Regular) constraint;
					store.impose(new ExtensionalSupportMDD( regular.fsm.transformDirectlyIntoMDD(regular.list)));
				}
			}


		}

		for (int i = 0; i < noClass; i++) {

			IntVar counter = new IntVar(store, "counter" + i, noOfCarsPerClass[i], noOfCarsPerClass[i]);

			store.impose(new Count(cars, counter, i));

			// Possible replacement for Count constraint.
			// IntervalDomain dom = new IntervalDomain(i, i);
			// store.impose(new Among(cars, dom, counter));
			//

		}

	}

	/*
	public void modelNestedDecomposed() {

		store = new FDstore();
		vars = new ArrayList<Variable>();

		Variable[] cars = new Variable[noCar];

		for (int i = 0; i < noCar; i++) {
			cars[i] = new Variable(store, "car" + (i+1), 0, noClass);
			vars.add(cars[i]);
		}

		for (int i = 0; i < noOption; i++) {

			IntervalDomain classesWithGivenOption = new IntervalDomain();
			for (int j = 0; j < noClass; j++)
				if (required[j][i])
					classesWithGivenOption.addDom(j, j);

			DecomposedConstraint c = new Sequence(cars, classesWithGivenOption, blockSizePerOption[i], 0, maxNoOfCarsPerOption[i]);
			ArrayList<Constraint> decomposition = c.decompose(store);

			for (Constraint regular : decomposition)
				store.imposeDecomposition(regular);
		}

		for (int i = 0; i < noClass; i++) {

			Variable counter = new Variable(store, "counter" + i, noOfCarsPerClass[i], noOfCarsPerClass[i]);
			store.impose(new Count(i, cars, counter));

		    // Possible replacement for Count constraint.
			//IntervalDomain dom = new IntervalDomain(i, i);
			//store.impose(new Among(cars, dom, counter));
			///

		}

	}

	 */

	/* @TODO Add functionality to FSM to be able to do intersections and use the model below.
	public void modelIntersection() {

		store = new FDstore();
		vars = new ArrayList<Variable>();

		Variable[] cars = new Variable[noCar];

		for (int i = 0; i < noCar; i++) {
			cars[i] = new Variable(store, "car" + (i+1), 0, noClass);
			vars.add(cars[i]);
		}

		ArrayList<Constraint> regulars = new ArrayList<Constraint>();

		for (int i = 0; i < noOption; i++) {

			IntervalDomain classesWithGivenOption = new IntervalDomain();
			for (int j = 0; j < noClass; j++)
				if (required[j][i])
					classesWithGivenOption.addDom(j, j);

			DecomposedConstraint c = new Sequence(cars, classesWithGivenOption, blockSizePerOption[i], 0, maxNoOfCarsPerOption[i]);
			ArrayList<Constraint> decomposition = c.decompose(store);

			regulars.addAll(decomposition);

			for (Constraint regular : decomposition)
				store.imposeDecomposition(regular);
		}

		FSM union = null;

		for (Constraint constraint : regulars)
			if (union == null)
				union = ((Regular) constraint).fsm;
			else
				union = union.union( ((Regular) constraint).fsm );

		System.out.println("Size +++++++++++ " + union.states.size());

		store.impose(new Regular(union, cars));

		for (int i = 0; i < noClass; i++) {

			IntervalDomain yes = new IntervalDomain(i, i);
			IntervalDomain no = new IntervalDomain(0, noClass);
			no = (IntervalDomain) no.subtract(i);

			FSM counter = createFSM(noOfCarsPerClass[i], yes, no);

			System.out.println( counter );

		//	store.impose(new Regular(counter, cars));

			if (i == 0)
				union = counter;
			else
				//union = union.concatenation( counter );
				union = union.union( counter );

			System.out.println("Union +++++++++++ " + union);

		}

		System.out.println(union);

		store.impose(new Regular(union, cars));


	}
	 */

	/**
	 * @param count The number of times a value from yes domain needs to be encountered.
	 * @param yes the values which are counted.
	 * @param no the values which are not counted.
	 * 
	 * @return FSM for simple count constraint.
	 */
	public static FSM createFSM(int count, IntervalDomain yes, IntervalDomain no) {

		FSM result = new FSM();

		result.initState = new FSMState();
		FSMState currentState = result.initState;

		int current = 0;
		while (current <= count) {

			FSMState nextStateYes = new FSMState();

			if (current < count)
				currentState.transitions.add(new FSMTransition(yes, nextStateYes));


			for (ValueEnumeration enumer = no.valueEnumeration(); enumer.hasMoreElements();) {
				int value = enumer.nextElement();
				IntervalDomain transitionCondition = new IntervalDomain(value, value);
				currentState.transitions.add(new FSMTransition(transitionCondition, currentState));
			}

			result.allStates.add(currentState);

			if (current == count)
				result.finalStates.add(currentState);

			currentState = nextStateYes;

			current++;

		}

		return result;

	}

	/**
	 * It reads the problem description from the file and returns string representation
	 * of the problem. 
	 * 
	 * @param file the file containing the problem description.
	 * @return the problem description
	 */
	public static String[] readFile(String file) {

		ArrayList<String> result = new ArrayList<String>();

		System.out.println("readFile(" + file + ")");

		try {

			BufferedReader inr = new BufferedReader(new FileReader(file));
			String str;

			while ((str = inr.readLine()) != null && str.length() > 0) {

				str = str.trim();

				// ignore comments
				if(str.startsWith("#") || str.startsWith("%")) {
					continue;
				}

				result.add(str);

			} // end while

			inr.close();

		} catch (IOException e) {
			System.out.println(e);
		}

		return result.toArray(new String[result.size()]);

	} // end readFile

	/**
	 * It executes the program to solve car sequencing problem.
	 * @param args
	 */
	public static void main(String args[]) {

		CarSequencing example = new CarSequencing();

		readFromArray(CarSequencing.problem, example);

		example.model();

		String[] description = toStringArray(example);

		for (String line : description)
			System.out.println(line);

		example.searchAllAtOnce();

	}	

	
	/**
	 * It executes the program to solve car sequencing problem.
	 * @param args
	 */
	public static void test(String args[]) {

		CarSequencing example = new CarSequencing();

		readFromArray(CarSequencing.problem, example);

		example.model();

		String[] description = toStringArray(example);

		for (String line : description)
			System.out.println(line);

		example.searchAllAtOnce();

		String [] problemDescription = readFile("ExamplesJaCoP/carSeq1.txt");

		readFromArray(problemDescription, example);
		example.model();

		example.searchLDS(3);

	}	


}
