/**
 *  BasicLogicPascal.java 
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

package org.jacop.examples.fd;

import java.util.ArrayList;

import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It solves an arithmetic puzzle BASIC+LOGIC=PASCAL.
 * 
 * @author Radoslaw Szymanek
 * 
 * 	Find for the equation on the left
 *	what digits are represented by the letters
 *	different letters represent different digits
 *
 *	BASIC 			9567
 * +LOGIC =======> +1085
 * PASCAL 		   10652
 *
 */
public class BasicLogicPascal extends ExampleFD {


	@Override
	public void model() {

		// Creating constraint store
		store = new Store();
		vars = new ArrayList<IntVar>();
		
		// Creating FDV (finite domain variables)
		IntVar b = new IntVar(store, "B", 0, 9);
		IntVar a = new IntVar(store, "A", 0, 9);
		IntVar s = new IntVar(store, "S", 0, 9);
		IntVar i = new IntVar(store, "I", 0, 9);
		IntVar l = new IntVar(store, "L", 0, 9);
		IntVar o = new IntVar(store, "O", 0, 9);
		IntVar g = new IntVar(store, "G", 0, 9);
		IntVar c = new IntVar(store, "C", 0, 9);
		IntVar p = new IntVar(store, "P", 0, 9);

		// Creating arrays for FDVs
		IntVar digits[] = { b, a, s, i, l, o, g, c, p };
		IntVar basic[] = { b, a, s, i, c };
		IntVar logic[] = { l, o, g, i, c };
		IntVar pascal[] = { p, a, s, c, a, l };

		for (IntVar v : digits) vars.add(v);
		
 		// Imposing inequalities constraints between letters
		// Only one global constraint
		store.impose(new Alldifferent(digits));

		int[] weights5 = { 10000, 1000, 100, 10, 1 };
		int[] weights6 = { 100000, 10000, 1000, 100, 10, 1 };

		IntVar valueBASIC = new IntVar(store, "v(BASIC)", 0, 99999);
		IntVar valueLOGIC = new IntVar(store, "v(LOGIC)", 0, 99999);
		IntVar valuePASCAL = new IntVar(store, "v(PASCAL)", 0, 999999);

		// Constraints for getting value for words
		// BASIC = 10000 * B + 1000 * A + 100 * S + I * 10 + C * 1
		// LOGIC = 10000 * L + 1000 * O + 100 * G + I * 10 + C * 1
		// PASCAL = 100000 * P + 10000 * A + 1000 * S + 100 * C + 10 * A + L * 1
		store.impose(new SumWeight(basic, weights5, valueBASIC));
		store.impose(new SumWeight(logic, weights5, valueLOGIC));
		store.impose(new SumWeight(pascal, weights6, valuePASCAL));

		// Main equation of the problem BASIC+ LOGIC = PASCAL
		store.impose(new XplusYeqZ(valueBASIC, valueLOGIC, valuePASCAL));
		// Since B is the first digit of BASIC
		// and L is the first digit of LOGIC or PASCAL
		// both letters can not be equal to zero
		store.impose(new XneqC(basic[0], 0));
		store.impose(new XneqC(logic[0], 0));
		store.impose(new XneqC(pascal[0], 0));
		
	}
	
	/**
	 * It executes the program to solve this puzzle.
	 * @param args no arguments are read.
	 */
	public static void main(String args[]) {

		BasicLogicPascal example = new BasicLogicPascal();
		
		example.model();

		if (example.searchMostConstrainedStatic())
			System.out.println("Solution(s) found");
		
	}	
	
	
}
