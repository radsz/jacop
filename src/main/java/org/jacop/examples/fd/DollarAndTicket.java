/**
 *  DollarAndTicket.java 
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
import org.jacop.constraints.Element;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It solves a simple logic puzzle - Dollar and Ticket problem. 
 * 
 * @author Wojciech Swietek, Maciej Trela, and Radoslaw Szymanek
 * 
 *
 * Every year the Soccer Club has a raffle to support the cost of playing
 * fields, equipment, and camps.  This year the top five sellers were
 * three girls named Diane, Jenny, and Maggie, and two boys named Greg
 * and Kevin; last names are Borecki, Ott, Panos, Ruiz, and Vogel. Each
 * of them is on a different team (the Bobcats, Cheetahs, Kickers,
 * Stars, and Wolves), and each sold a different number of books of
 * tickets (20, 18, 12, 10, and 6).  Can you match each seller's full
 * name with his or her team and number of ticket books sold?
 *
 * 1. Jenny sold exactly twice as many books as Ms. Ruiz.
 * 2. The one who sold 12 books (who isn't Panos) isn't on the Bobcats or Stars.
 * 3. The player from the Wolves sold at least twice as many books as Ott.
 * 4. Borecki isn't on the Kickers.
 * 5. The girl on the Cheetahs sold exactly three times as many books as Diane.
 * 6. Greg isn't Borecki or Ott.
 * 7. Kevin isn't on the Bobcats.
 *  
 */

public class DollarAndTicket extends ExampleFD {

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("Program to solve DollarATicket Solve problem ");

		String[] firstnames = { "Diane", "Jenny", "Maggie", "Greg", "Kevin" };

		// Creating indexes for ease of referring.
		int idiane = 0, ijenny = 1, /* imaggie = 2, */ igreg = 3, ikevin = 4;

		String[] surnames = { "Borecki", "Ott", "Pamos", "Ruiz", "Vogel" };

		// Creating indexes for ease of referring.
		int /* ivogel = 0, */ iborecki = 1, iott = 2, ipamos = 3, iruiz = 4;
		
		String[] teams = { "Bobcats", "Cheetahs", "Kickers", "Stars", "Wolves" };

		// Creating indexes for ease of referring.
		int ibobcats = 0, icheetahs = 1, ikickers = 2, istars = 3, iwolves = 4;

		IntVar firstname[] = new IntVar[5];
		IntVar surname[] = new IntVar[5];
		IntVar team[] = new IntVar[5];

		// Each variable has a domain being created by subsequent calls to
		// addDom function.
		for (int i = 0; i < 5; i++) {
			firstname[i] = new IntVar(store, firstnames[i]);
			firstname[i].addDom(6, 6);
			firstname[i].addDom(10, 10);
			firstname[i].addDom(12, 12);
			firstname[i].addDom(18, 18);
			firstname[i].addDom(20, 20);

			surname[i] = new IntVar(store, surnames[i]);
			surname[i].addDom(6, 6);
			surname[i].addDom(10, 10);
			surname[i].addDom(12, 12);
			surname[i].addDom(18, 18);
			surname[i].addDom(20, 20);

			team[i] = new IntVar(store, teams[i]);
			team[i].addDom(6, 6);
			team[i].addDom(10, 10);
			team[i].addDom(12, 12);
			team[i].addDom(18, 18);
			team[i].addDom(20, 20);
			
			vars.add(firstname[i]); vars.add(surname[i]); vars.add(team[i]);
		}

		// All objects have a unique identifier (# of books sold)
		store.impose(new Alldifferent(firstname));
		store.impose(new Alldifferent(surname));
		store.impose(new Alldifferent(team));

		// 1. Jenny sold exactly twice as many books as Ms. Ruiz.

		store.impose(new XmulCeqZ(surname[iruiz], 2, firstname[ijenny]));

		// 2. The one who sold 12 books (who isn't Panos) isn't
		// on the Bobcats or Stars.

		store.impose(new XneqC(surname[ipamos], 12));
		store.impose(new XneqC(team[ibobcats], 12));
		store.impose(new XneqC(team[istars], 12));

		// 3. The player from the Wolves sold at least twice as
		// many books as Ott.
		// Auxilary variable is created.
		IntVar X = new IntVar(store, "X", 0, 50);

		// Since there is no constraint XmulCgteqY then it must be splitted into
		// two constraints.
		store.impose(new XmulCeqZ(surname[iott], 2, X));
		store.impose(new XgteqY(team[iwolves], X));

		// 4. Borecki isn't on the Kickers.
		store.impose(new XneqY(surname[iborecki], team[ikickers]));

		// 5. The girl on the Cheetahs sold exactly three times as many
		// books as Diane.

		IntVar girlIndex = new IntVar(store, "girlIndex", 1, 3);
		// First three indexes of firstname denote girls name
		// (the ordering of names is important here).
		IntVar girlFirstname[] = { firstname[0], firstname[1], firstname[2] };

		vars.add(girlIndex);
		
		store.impose(new Element(girlIndex, girlFirstname, team[icheetahs]));
		store.impose(new XmulCeqZ(firstname[idiane], 3, team[icheetahs]));

		// 6. Greg isn't Borecki or Ott.
		store.impose(new XneqY(firstname[igreg], surname[iott]));
		store.impose(new XneqY(firstname[igreg], surname[iborecki]));

		// 7. Kevin isn't on the Bobcats.
		store.impose(new XneqY(firstname[ikevin], team[ibobcats]));

	}
		
	/**
	 * It executes the program to solve this simple puzzle.
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		DollarAndTicket example = new DollarAndTicket();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}
	
}
