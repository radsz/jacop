/**
 *  BabySitting.java 
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
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It is a simple logic puzzle about babysitting.
 * 
 * @author Radoslaw Szymanek
 * 
 * Each weekday, Bonnie takes care of five of the neighbors'
 * children. The children's names are Keith, Libby, Margo, Nora, and
 * Otto; last names are Fell, Grant, Hall, Ivey, and Jule. Each is a
 * different number of years old, from two to six. Can you find each
 * child's full name and age?

 * 1. One child is named Libby Jule.
 * 2. Keith is one year older than the Ivey child, who is one year older than Nora.
 * 3. The Fell child is three years older than Margo.
 * 4. Otto is twice as many years old as the Hall child.

 * Determine: First name - Last name - Age


 * Given solution : 

 * Keith Fell, five years old
 * Libby Jule, six years old
 * Margo Hall, two years old
 * Nora Grant, three years old
 * Otto Ivey, four years old 
 *
 *
 */

public class BabySitting extends ExampleFD {
	
	@Override
	public void model() {		

		vars = new ArrayList<IntVar>();
		store = new Store();

		System.out.println("Program to solve Babysitting problem ");

		// arrays with surnames
		String[] surnameNames = { "Fell", "Grant", "Hall", "Ivey", "Jule" };

		int ifell = 0, /* igrant = 1, */ ihall = 2, iivey = 3, ijule = 4;

		// arrays with names
		String[] nameNames = { "Keith", "Libby", "Margo", "Nora", "Otto" };

		int ikeith = 0, ilibby = 1, imargo = 2, inora = 3, iotto = 4;

		// FDV's in the model
		IntVar surname[] = new IntVar[5];
		IntVar name[] = new IntVar[5];

		for (int i = 0; i < 5; i++) {
			// Values encode actual age of the child.
			surname[i] = new IntVar(store, surnameNames[i], 2, 6);
			name[i] = new IntVar(store, nameNames[i], 2, 6);
			vars.add(surname[i]); vars.add(name[i]);
		}

		
		// Each person has to have a different surname and different name.
		store.impose(new Alldifferent(surname));
		store.impose(new Alldifferent(name));

		// 1. One child is named Libby Jule.
		store.impose(new XeqY(name[ilibby], surname[ijule]));

		// 2. Keith is one year older than the Ivey child.....
		store.impose(new XplusCeqZ(surname[iivey], 1, name[ikeith]));
		// ..... who is one year older than Nora.
		store.impose(new XplusCeqZ(name[inora], 1, surname[iivey]));

		// 3. The Fell child is three years older than Margo
		store.impose(new XplusCeqZ(name[imargo], 3, surname[ifell]));

		// 4. Otto is twice as many years old as the Hall child.
		store.impose(new XmulCeqZ(surname[ihall], 2, name[iotto]));

	}
	

	/**
	 * It runs the program solving this puzzle.
	 * @param args no arguments are read.
	 */
	public static void main(String args[]) {

		BabySitting example = new BabySitting();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}
	
}
