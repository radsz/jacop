/**
 *  BuildingBlocks.java 
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
import org.jacop.constraints.Cumulative;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It solves a simple logic puzzle about blocks.
 * 
 * @author Krzysztof "Vrbl" Wrobel and Radoslaw Szymanek
 *
 * Each of four alphabet blocks has a single letter of the alphabet on
 * each of its six sides.  In all, the four blocks contain every letter
 * but Q and Z.  By arranging the blocks in various ways, you can spell
 * all of the words listed below.  Can you figure out how the letters are
 * arranged on the four blocks?
 *
 * BAKE ONYX ECHO OVAL 
 *
 * GIRD SMUG JUMP TORN 
 *
 * LUCK VINY LUSH WRAP 
 */

public class BuildingBlocks extends ExampleFD {

	@Override
	public void model() {

		vars = new ArrayList<IntVar>();
		store = new Store();

		System.out.println("Building Blocks");

		IntVar A = new IntVar(store, "A", 1, 4);
		IntVar B = new IntVar(store, "B", 1, 4);
		IntVar C = new IntVar(store, "C", 1, 4);
		IntVar D = new IntVar(store, "D", 1, 4);
		IntVar E = new IntVar(store, "E", 1, 4);
		IntVar F = new IntVar(store, "F", 1, 4);
		IntVar G = new IntVar(store, "G", 1, 4);
		IntVar H = new IntVar(store, "H", 1, 4);
		IntVar I = new IntVar(store, "I", 1, 4);
		IntVar J = new IntVar(store, "J", 1, 4);
		IntVar K = new IntVar(store, "K", 1, 4);
		IntVar L = new IntVar(store, "L", 1, 4);
		IntVar M = new IntVar(store, "M", 1, 4);
		IntVar N = new IntVar(store, "N", 1, 4);
		IntVar O = new IntVar(store, "O", 1, 4);
		IntVar P = new IntVar(store, "P", 1, 4);
		IntVar R = new IntVar(store, "R", 1, 4);
		IntVar S = new IntVar(store, "S", 1, 4);
		IntVar T = new IntVar(store, "T", 1, 4);
		IntVar U = new IntVar(store, "U", 1, 4);
		IntVar W = new IntVar(store, "W", 1, 4);
		IntVar V = new IntVar(store, "V", 1, 4);
		IntVar X = new IntVar(store, "X", 1, 4);
		IntVar Y = new IntVar(store, "Y", 1, 4);

		// array of letters.
		IntVar letters[] = { A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, R, S,
						  T, U, W, V, X, Y };

		for (IntVar v : letters)
			vars.add(v);

		// First word, each letter on a different block.
		IntVar bake[] = { B, A, K, E };
		store.impose(new Alldifferent(bake));

		IntVar onyx[] = { O, N, Y, X };
		store.impose(new Alldifferent(onyx));

		IntVar echo[] = { E, C, H, O };
		store.impose(new Alldifferent(echo));

		IntVar oval[] = { O, V, A, L };
		store.impose(new Alldifferent(oval));

		IntVar grid[] = { G, R, I, D };
		store.impose(new Alldifferent(grid));

		IntVar smug[] = { S, M, U, G };
		store.impose(new Alldifferent(smug));

		IntVar jump[] = { J, U, M, P };
		store.impose(new Alldifferent(jump));

		IntVar torn[] = { T, O, R, N };
		store.impose(new Alldifferent(torn));

		IntVar luck[] = { L, U, C, K };
		store.impose(new Alldifferent(luck));

		IntVar viny[] = { V, I, N, Y };
		store.impose(new Alldifferent(viny));

		IntVar lush[] = { L, U, S, H };
		store.impose(new Alldifferent(lush));

		IntVar wrap[] = { W, R, A, P };
		store.impose(new Alldifferent(wrap));

		// auxilary variables
		IntVar one = new IntVar(store, "one", 1, 1);
		IntVar six = new IntVar(store, "six", 6, 6);

		IntVar ones[] = new IntVar[24];
		for (int i = 0; i < 24; i++)
			ones[i] = one;

		// Each block can not contain more than six letters.
		store.impose(new Cumulative(letters, ones, ones, six));

		// Letters decode the start time (block number).
		// Duration, each letter is only on one block (duration 1).
		// Resource, each letter takes only one space (usage 1).
		// Limit, all blocks can accommodate 6 letters.

	}
		
	/**
	 * It executes the program to solve this logic puzzle.
	 * @param args
	 */
	public static void main(String args[]) {

		BuildingBlocks example = new BuildingBlocks();
		
		example.model();

		if (example.searchSmallestDomain(false))
			System.out.println("Solution(s) found");
	}	
	
}
