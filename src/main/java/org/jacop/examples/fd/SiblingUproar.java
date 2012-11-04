/**
 *  SiblingUproar.java 
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
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It is quite complex logic puzzle about siblings. 
 * 
 * @author Krzysztof "Vrbl" Wrobel, Wioletta "Vuka" Kruzolek, and Radoslaw Szymanek 
 *
 * This is quite difficult logic puzzle to be modeled and solved by CP.
 *
 * Mrs. Wheatley returned home from her job to find the household in a
 * turmoil of arguments.  Each of her five teenagers (three boys named
 * Bryan, Russell, and Stuart, and two girls named Nina and Paula) had
 * gotten angry at one of his or her siblings for a different reason
 * (finished cereal, let dog in room, used up hot water, failed to return
 * rollerblades, and hogged television) and had decided to retaliate in a
 * different way (knocked over chess game, let gerbil out of cage, hung
 * up on friend, removed light bulbs, and hid violin).
 *
 * After a few futile minutes of trying to sort out blame, 
 * Mrs. Wheatley called a halt to the arguments by declaring everyone 
 * equally guilty and giving each a different chore around the house 
 * as that evening's punishment (cleaning the attic, basement, or garage, 
 * or washing the Venetian blinds or windows).  Can you discover, for 
 * each child, the sibling he or she was initially angry at, the reason 
 * for the anger, the retaliatory measure he or she took, and the chore 
 * meted out to each child?
 *
 * 1. No one was originally angry at the sibling who was angry at him or
 * her.
 *
 * 2. The boy who was angry at the sibling who used up all the hot water
 * taking a shower retaliated against him or her by removing all the
 * light bulbs from his or her room; the child who was angry at this boy
 * was later punished by being sent to sweep the basement.
 *
 * 3. The five siblings are: Paula, the person who was angry at Paula,
 * the person who was angry because a sibling was hogging the television,
 * the child who was told to straighten the attic, and a child to didn't 
 * remove a sibling's light bulbs or hide a sibling's violin.
 * 
 * 4. The child who was angry at Stuart was punished by being told to wash 
 * the Venetian blinds.
 * 
 * 5. Russell was punished by being sent to clean out a section of the garage. 
 * 
 * 6. The child who let the dog in a sibling's room didn't retaliate against another sibling by knocking over a chess game that he or she was playing.
 * 
 * 7. The child who was hogging the television was angry at a sibling who wasn't punished by being told to straighten up the attic or wash the windows.
 * 
 * 8. In retaliation, one person hid the violin belonging to the person who was angry at Paula.
 * 
 * 9. Bryan and the person who was punished by being told to wash the
 * windows are, in same order, the child who was angry at the sibling
 * who didn't return the rollerblades and the one who retaliated against 
 * a sibling by knocking over a chess game in progress.
 * 
 * 10. Stuart and the person who was angry at Nina are, in some order, the child 
 * who was angry at the person who finished the best cereal in the house and the one who retaliated against a sibling by hanging up on his or her best friend.
 * 
 * Determine: Sibling - Angry at - Reason - Retaliation - Chore
 * 
 */

public class SiblingUproar extends ExampleFD {

	@Override
	public void model() {

		// Array of FDV's which will be used during search.
		vars = new ArrayList<IntVar>();
		store = new Store();

		System.out.println("Problem name: Sibling Uproar ");

		// Specification of children names
		String[] childrenNames = { "Brian", "Russell", "Stuart", "Nina",
				"Paula" };
		
		// Creation of indexes for ease of referring
		int iBrian = 0, iRussell = 1, iStuart = 2, iNina = 3, iPaula = 4;

		// Specification of being angry at someone.
		String[] angryatNames = { "angryAtBrian", "angryAtRussell",
				"angryAtStuart", "angryAtNina", "angryAtPaula" };
		
		// Creation of indexes for ease of referring
		int jBrian = 0, jRussell = 1, jStuart = 2, jNina = 3, jPaula = 4;

		// Specification of the reasons for being angry.
		String[] reasonNames = { "finished_cereal", "let_dog_in_room",
				"used_up_hot_water", "failed_to_return_rollerblades",
				"hogged_television" };
		// Creation of indexes for ease of referring
		int ifinished_cereal = 0, ilet_dog_in_room = 1, iused_up_hot_water = 2, ifailed_to_return_rollerblades = 3, ihogged_television = 4;

		// Specification of different types of revenge.
		String[] wayNames = { "knocked_over_chess_game",
				"let_gerbil_out_of_cage", "hung_up_on_friend",
				"removed_light_bulbs", "hid_violin" };

		// Creation of indexes for ease of referring
		int iknocked_over_chess_game = 0, /* ilet_gerbil_out_of_cage = 1, */ 
			ihung_up_on_friend = 2, iremoved_light_bulbs = 3, ihid_violin = 4;

		// Specification of different punishment.
		String[] choreNames = { "cleaning_the_attic", "cleaning_the_basement",
				"cleaning_the_garage", "washing_the_blinds",
				"washing_the_windows" };
		// Creation of indexes for ease of referring
		int icleaning_the_attic = 0, icleaning_the_basement = 1, icleaning_the_garage = 2, iwashing_the_blinds = 3, iwashing_the_windows = 4;

		// Creation of FDV's array
		IntVar children[] = new IntVar[5];
		IntVar angryat[] = new IntVar[5];
		IntVar reason[] = new IntVar[5];
		IntVar way[] = new IntVar[5];
		IntVar chore[] = new IntVar[5];

		// All variables can have five values, as they are five children, five
		// types of activities, etc.
		for (int i = 0; i < 5; i++) {
			children[i] = new IntVar(store, childrenNames[i], 1, 5);
			angryat[i] = new IntVar(store, angryatNames[i], 1, 5);
			reason[i] = new IntVar(store, reasonNames[i], 1, 5);
			way[i] = new IntVar(store, wayNames[i], 1, 5);
			chore[i] = new IntVar(store, choreNames[i], 1, 5);
			vars.add(children[i]); vars.add(angryat[i]); vars.add(reason[i]); 
			vars.add(way[i]); vars.add(chore[i]);
		}

		// Each child has a different id
		store.impose(new Alldifferent(children));
		// Only one child can be angry at the same person.
		store.impose(new Alldifferent(angryat));
		// Each child is angry for a different reason.
		store.impose(new Alldifferent(reason));
		// Each child has chosen a different type of the revenge.
		store.impose(new Alldifferent(way));
		// Each child is punished ina different way.
		store.impose(new Alldifferent(chore));

		// Auxilary variables.
		IntVar x1 = new IntVar(store, "x1", 1, 5);
		IntVar x2 = new IntVar(store, "x2", 1, 5);
		IntVar x3 = new IntVar(store, "x3", 1, 5);
		IntVar x4 = new IntVar(store, "x4", 1, 5);
		IntVar x5 = new IntVar(store, "x5", 1, 5);
		IntVar y1 = new IntVar(store, "y1", 1, 5);
		IntVar y2 = new IntVar(store, "y2", 1, 5);
		IntVar y3 = new IntVar(store, "y3", 1, 5);
		IntVar y4 = new IntVar(store, "y4", 1, 5);
		IntVar y5 = new IntVar(store, "y5", 1, 5);

		// Constraints to connect variables angryat and children.
		// y1=angryat[x1] denotes child y1 angry at x1.
		store.impose(new Element(x1, angryat, y1));
		store.impose(new Element(y1, children, x1));
		store.impose(new Element(x2, angryat, y2));
		store.impose(new Element(y2, children, x2));
		store.impose(new Element(x3, angryat, y3));
		store.impose(new Element(y3, children, x3));
		store.impose(new Element(x4, angryat, y4));
		store.impose(new Element(y4, children, x4));
		store.impose(new Element(x5, angryat, y5));
		store.impose(new Element(y5, children, x5));

		IntVar xs[] = { x1, x2, x3, x4, x5 };
		// The same relation as for angry at and children.
		store.impose(new Alldifferent(xs));
		
		for (IntVar v : xs)
			vars.add(v);
		IntVar ys[] = { y1, y2, y3, y4, y5 };
		for (IntVar v : ys)
			vars.add(v);
		
		// 1. No one was originally angry at the sibling who was angry at him or
		// her.
		// Bryan is not angry at somebody who is angry at Bryan.
		store.impose(new XneqY(children[iBrian], angryat[jBrian]));
		// Russell ...
		store.impose(new XneqY(children[iRussell], angryat[jRussell]));
		store.impose(new XneqY(children[iStuart], angryat[jStuart]));
		store.impose(new XneqY(children[iNina], angryat[jNina]));
		store.impose(new XneqY(children[iPaula], angryat[jPaula]));

		// 2. The boy who was angry at the sibling who used up all the hot water
		// taking a shower retaliated against him
		// or her by removing all the light bulbs from his or her room;
		// the child who was angry at this boy was later punished by being sent
		// to sweep the basement.

		// auxilary variable, boys are denoted by values from 1 to 3.
		IntVar boy = new IntVar(store, "boy", 1, 3);
		IntVar s = new IntVar(store, "sibling", 1, 5);
		vars.add(boy);
		vars.add(s);

		store.impose(new Element(boy, children, way[iremoved_light_bulbs]));
		store.impose(new Element(s, angryat, reason[iused_up_hot_water]));
		store.impose(new XeqY(way[iremoved_light_bulbs],
				reason[iused_up_hot_water]));

		IntVar ktos = new IntVar(store, "somebody", 1, 5);
		store.impose(new Element(boy, angryat, ktos));
		store.impose(new XeqY(chore[icleaning_the_basement], ktos));
		vars.add(ktos);

		// 3. The five siblings are: Paula, the person who was angry at Paula,
		// the person who was angry because a sibling was hogging the
		// television, the child who was told to straighten the attic,
		// and a child to didn't remove a sibling's light bulbs or hide a
		// sibling's violin.

		IntVar someone = new IntVar(store, "someone", 1, 5);
		store.impose(new Element(someone, angryat, reason[ihogged_television]));
		vars.add(someone);

		IntVar Z = new IntVar(store, "Z", 1, 5);
		store.impose(new XneqY(Z, way[iremoved_light_bulbs]));
		store.impose(new XneqY(Z, way[ihid_violin]));
		vars.add(Z);

		IntVar all[] = { children[iPaula], angryat[jPaula],
				reason[ihogged_television], chore[icleaning_the_attic], Z };// piatka
																			// rodzenstwa
		store.impose(new Alldifferent(all));

		// 4. The child who was angry at Stuart was punished by being told to
		// wash the Venetian blinds.

		store.impose(new XeqY(angryat[jStuart], chore[iwashing_the_blinds]));

		// 5. Russell was punished by being sent to clean out a section of the
		// garage.

		store.impose(new XeqY(chore[icleaning_the_garage], children[iRussell]));

		// 6. The child who let the dog in a sibling's room didn't retaliate
		// against another sibling by knocking over a chess game
		// that he or she was playing.

		store.impose(new XneqY(reason[ilet_dog_in_room],
				way[iknocked_over_chess_game]));

		// 7. The child who was hogging the television was angry at a sibling
		// who wasn't punished by being told to
		// straighten up the attic or wash the windows.

		store.impose(new XneqY(reason[ihogged_television],
				chore[icleaning_the_attic]));
		store.impose(new XneqY(reason[ihogged_television],
				chore[iwashing_the_windows]));

		// 8. In retaliation, one person hid the violin belonging to the person
		// who was angry at Paula.

		IntVar imie = new IntVar(store, "imie", 1, 5);
		store.impose(new Element(imie, angryat, way[ihid_violin]));
		store.impose(new Element(imie, children, angryat[jPaula]));
		vars.add(imie);

		// 9. Bryan and the person who was punished by being told to wash the
		// windows are, in same order,
		// the child who was angry at the sibling who didn't return the
		// rollerblades
		// and the one who retaliated against a sibling by knocking over a chess
		// game in progress.

		store.impose(new XeqY(way[iknocked_over_chess_game], children[iBrian]));
		store.impose(new XeqY(chore[iwashing_the_windows],
				reason[ifailed_to_return_rollerblades]));

		// 10. Stuart and the person who was angry at Nina are, in some order,
		// the child who
		// was angry at the person who finished the best cereal in the house and
		// the one who
		// retaliated against a sibling by hanging up on his or her best friend.

		IntVar kto = new IntVar(store, "kto", 1, 5);
		store.impose(new Element(kto, children, reason[ifinished_cereal]));
		store.impose(new XeqY(angryat[jNina], reason[ifinished_cereal]));
		store.impose(new XeqY(children[iStuart], way[ihung_up_on_friend]));
		vars.add(kto);

	}
	
	/**
	 * It executes the program to solve this logic puzzle.
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		SiblingUproar example = new SiblingUproar();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}	

}
