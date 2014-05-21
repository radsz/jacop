/**
 *  Cyclohexane.java 
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
 * This model is based on
 * minizinc model cyclohexane.mzn by Håkan Kjellerstrand
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 */

import java.util.ArrayList;

import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PplusCeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.floats.search.SmallestDomainFloat;

public class Cyclohexane {

    double MIN_FLOAT = -1e+150;
    double MAX_FLOAT =  1e+150;

    void cyclohexane() {

       long T1, T2, T;
	T1 = System.currentTimeMillis();

	System.out.println ("========= cyclohexane =========");

	Store store = new Store();

	FloatDomain.setPrecision(1e-13);
	FloatDomain.intervalPrint(false);

	// equations:
        // 13.0 + y*y*(1.0+z*z) + z*(z - 24.0*y)  = 0.0 /\
        // 13.0 + z*z*(1.0+x*x) + x*(x - 24.0*z)  = 0.0 /\
        // 13.0 + x*x*(1.0+y*y) + y*(y - 24.0*x)  = 0.0 

	FloatVar x = new FloatVar(store, "x", -20.0, 20.0);
	FloatVar y = new FloatVar(store, "y", -20.0, 20.0);
	FloatVar z = new FloatVar(store, "z", -20.0, 20.0);

	// x*x
	FloatVar xx = new FloatVar(store, "xx", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(x, x, xx));
	// y*y
	FloatVar yy = new FloatVar(store, "yy", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(y, y, yy));
	// z*z
	FloatVar zz = new FloatVar(store, "zz", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(z, z, zz));

	// x*x + 1.0
	FloatVar t1 = new FloatVar(store, "t1", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PplusCeqR(xx, 1.0, t1));
	// y*y + 1.0
	FloatVar t2 = new FloatVar(store, "t2", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PplusCeqR(yy, 1.0, t2));
	// z*z + 1.0
	FloatVar t3 = new FloatVar(store, "t3", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PplusCeqR(zz, 1.0, t3));

	/// y*y*(1.0+z*z))
	FloatVar t4 = new FloatVar(store, "t4", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(yy, t3, t4));
	/// z*z*(1.0+x*x))
	FloatVar t5 = new FloatVar(store, "t5", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(zz, t1, t5));
	/// x*x*(1.0+y*y))
	FloatVar t6 = new FloatVar(store, "t6", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(xx, t2, t6));

	// z - 24.0*y
	FloatVar t7 = new FloatVar(store, "t7", MIN_FLOAT, MAX_FLOAT);
	store.impose(new LinearFloat(store, new FloatVar[] {z, y, t7}, new double[] {1.0, -24.0, -1.0}, "==", 0.0));
	// x - 24.0*z
	FloatVar t8 = new FloatVar(store, "t8", MIN_FLOAT, MAX_FLOAT);
	store.impose(new LinearFloat(store, new FloatVar[] {x, z, t8}, new double[] {1.0, -24.0, -1.0}, "==", 0.0));
	// y - 24.0*x
	FloatVar t9 = new FloatVar(store, "t9", MIN_FLOAT, MAX_FLOAT);
	store.impose(new LinearFloat(store, new FloatVar[] {y, x, t9}, new double[] {1.0, -24.0, -1.0}, "==", 0.0));

	// z*(z - 24.0*y)
	FloatVar t10 = new FloatVar(store, "t10", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(z, t7, t10));
	// x*(x - 24.0*z)
	FloatVar t11 = new FloatVar(store, "t11", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(x, t8, t11));
	// y*(y - 24.0*x)
	FloatVar t12 = new FloatVar(store, "t12", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(y, t9, t12));

	// FloatVar t = new FloatVar(store, -13.0, -13.0);
	// store.impose(new PplusQeqR(t4, t10, t));
	// store.impose(new PplusQeqR(t5, t11, t));
	// store.impose(new PplusQeqR(t6, t12, t));

	store.impose(new LinearFloat(store, new FloatVar[] {t4, t10}, new double[] {1.0, 1.0}, "==", -13.0));
	store.impose(new LinearFloat(store, new FloatVar[] {t5, t11}, new double[] {1.0, 1.0}, "==", -13.0));
	store.impose(new LinearFloat(store, new FloatVar[] {t6, t12}, new double[] {1.0, 1.0}, "==", -13.0));

	System.out.println( "\bVar store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );

	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {x, y, z}, null); //new SmallestDomainFloat<FloatVar>());
	label.setSolutionListener(new PrintOutListener<FloatVar>());
	label.getSolutionListener().recordSolutions(true); 
	// label.getSolutionListener().searchAll(true); 
	label.setAssignSolution(true);
	// s.leftFirst = false;

	label.labeling(store, s);

	// label.printAllSolutions();


	System.out.println ("\nPrecision = " + FloatDomain.precision());

	T2 = System.currentTimeMillis();
	T = T2 - T1;

	System.out.println("\n\t*** Execution time = "+ T + " ms");

    }

    /**
     * It executes the program. 
     * 
     * @param args no arguments
     */
    public static void main(String args[]) {
		
	Cyclohexane example = new Cyclohexane();
		
	example.cyclohexane();

    }			
}
