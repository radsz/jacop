/**
 *  TanExample.java
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

package org.jacop.examples.floats;

/**
 *
 * It models tan(x) = -x for floating solver.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 */

import org.jacop.core.Store;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.TanPeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.search.DepthFirstSearch;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TanExample { private static Logger logger = LoggerFactory.getLogger(TanExample.class);

    public void model() {

	logger.info("\nProgram to solve tan(x) = -x problem in interval -4*pi..4*pi");

	long T1, T2;
	T1 = System.currentTimeMillis();

	Store store = new Store();

	FloatDomain.setPrecision(1.0e-11);
	FloatDomain.intervalPrint(false);

	FloatVar p = new FloatVar(store, "p", -4*FloatDomain.PI, 4*FloatDomain.PI);
	FloatVar q = new FloatVar(store, "q", FloatDomain.MinFloat, FloatDomain.MaxFloat);

	store.impose(new TanPeqR(p, q));
	store.impose(new PplusQeqR(p, q, new FloatVar(store, 0.0, 0.0)));

	logger.info( "\bVar store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );

	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {p, q}, null); //new SmallestDomainFloat<FloatVar>());
	label.setAssignSolution(true);
	// label.setSolutionListener(new PrintOutListener<FloatVar>());
	label.getSolutionListener().recordSolutions(true);
	label.getSolutionListener().searchAll(true);
	s.roundRobin = false;
	//s.leftFirst = false;

	boolean result = label.labeling(store, s);


	if (result)
	    label.printAllSolutions();
	else
	    logger.info ("NO SOLUTION");

	logger.info ("\nPrecision = " + FloatDomain.precision());

	T2 = System.currentTimeMillis();

	logger.info("\n\t*** Execution time = " + (T2 - T1) + " ms");

    }

    /**
     * It executes the program which computes values for tan(x) = -x.
     *
     * @param args no arguments
     */
    public static void main(String args[]) {

	TanExample example = new TanExample();

	example.model();

    }
}
