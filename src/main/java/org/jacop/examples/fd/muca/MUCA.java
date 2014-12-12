/**
 *  MUCA.java 
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

package org.jacop.examples.fd.muca;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.StringTokenizer;

import org.jacop.constraints.Among;
import org.jacop.constraints.ExtensionalSupportVA;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XplusYgtC;
import org.jacop.constraints.XplusYplusQeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.MaxRegret;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;

/**
 * 
 * It solves the Mixed Multi-Unit Combinatorial Auctions. 
 * 
 * @author Radoslaw Szymanek
 * @version 4.2
 * 
 * 
 * The idea originated from reading the following paper 
 * where the first attempt to use CP was presented.
 * 
 * Comparing Winner Determination Algorithms for Mixed
 * Multi-Unit Combinatorial Auctions by Brammert Ottens
 * Ulle Endriss
 * 
 */

public class MUCA extends ExampleFD {

	/**
	 * ArrayList of bids issued by different bidders. 
	 * Each bidder issues an ArrayList of xor bids. 
	 * Each Xor bid is a list of transformations. 
	 */
	public ArrayList<ArrayList<ArrayList<Transformation> >> bids;


	/**
	 * For each bidder and each xor bid there is an 
	 * integer representing a cost of the xor bid.
	 */
	public ArrayList<ArrayList<Integer>> costs;

	
	/**
	 * It specifies the initial quantities of goods.
	 */
	public ArrayList<Integer> initialQuantity;
	
	
	/**
	 * It specifies the minimal quantities of items seeked to achieve.
	 */
	public ArrayList<Integer> finalQuantity;

	/**
	 * It specifies number of goods which are in the focus of the auction.
	 */
	public int noGoods = 7;

	
	/**
	 * It specifies the minimal possible delta of goods for any transformation.
	 */
	public int minDelta = -10;
	
	/**
	 * It specifies the maximal possible delta of goods for any transformation.
	 */
	
	public int maxDelta = 10;

	/**
	 * It specifies the minimal value for the cost.
	 */
	public int minCost = -100000;

	/**
	 * It specifies the maximal value for the cost.
	 */
	public int maxCost = 100000;

	
	/**
	 * The maximal number of products.
	 */
	public int maxProducts = 100;

	
	/**
	 * For each bidder it specifies variable representing 
	 * the cost of the chosen xor bid.
	 */
	public ArrayList<IntVar> bidCosts;

	
	/**
	 * It specifies the sequence of transitions used by an auctioneer.
	 */
	public IntVar transitions[];

	
	/**
	 * It specifies the maximal number of transformations used by the auctioneer.
	 */
	public int maxNoTransformations;

	
	/**
	 * For each transition and each good it specifies the 
	 * delta change of that good before the transition takes place.
	 */
	public IntVar deltasI [][]; 

	/**
	 * For each transition and each good it specifies the 
	 * delta change of that good after the transition takes place.
	 */	
	public IntVar deltasO [][];

	/**
	 * It specifies the number of goods after the last transition.
	 */
	public IntVar sum[];

	/**
	 * It reads auction problem description from the file.
	 */
	public String filename = "./ExamplesJaCoP/testset3.auct";

	/**
	 * It creates an instance of the auction problem.
	 */
	public void setupProblem1() {

		bids = new ArrayList<ArrayList<ArrayList<Transformation> >>();

		ArrayList<ArrayList<Transformation>> bid_1 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_1_xor1 = new ArrayList<Transformation>();

		Transformation t1 = new Transformation();
		// ((0, 1))
		t1.goodsIds = new ArrayList<Integer>();
		t1.goodsIds.add(new Integer(3));
		t1.goodsIds.add(new Integer(10));
		t1.delta = new ArrayList<Delta>();
		t1.delta.add(new Delta(0, 1));
		t1.delta.add(new Delta(5, 0));

		bid_1_xor1.add(t1);

		// ((2, 3))
		Transformation t2 = new Transformation();
		t2.goodsIds = new ArrayList<Integer>();
		t2.goodsIds.add(new Integer(4));
		t2.goodsIds.add(new Integer(10));
		t2.goodsIds.add(new Integer(11));
		t2.delta = new ArrayList<Delta>();
		t2.delta.add(new Delta(0, 2));
		t2.delta.add(new Delta(2, 0));
		t2.delta.add(new Delta(2, 0));

		bid_1_xor1.add(t2);

		bid_1.add(bid_1_xor1);

		ArrayList<ArrayList<Transformation>> bid_2 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_2_xor1 = new ArrayList<Transformation>();

		Transformation t3 = new Transformation();
		// ((0, 1))
		t3.goodsIds = new ArrayList<Integer>();
		t3.goodsIds.add(new Integer(5));
		t3.goodsIds.add(new Integer(11));
		t3.goodsIds.add(new Integer(12));
		t3.delta = new ArrayList<Delta>();
		t3.delta.add(new Delta(0, 1));
		t3.delta.add(new Delta(1, 0));
		t3.delta.add(new Delta(1, 01));

		bid_2_xor1.add(t3);

		Transformation t4 = new Transformation();
		// ((0, 1))
		t4.goodsIds = new ArrayList<Integer>();
		t4.goodsIds.add(new Integer(6));
		t4.goodsIds.add(new Integer(11));
		t4.goodsIds.add(new Integer(12));
		t4.goodsIds.add(new Integer(13));
		t4.delta = new ArrayList<Delta>();
		t4.delta.add(new Delta(0, 2));
		t4.delta.add(new Delta(2, 0));
		t4.delta.add(new Delta(2, 0));
		t4.delta.add(new Delta(2, 0));

		bid_2_xor1.add(t4);

		Transformation t5 = new Transformation();
		// ((0, 1))
		t5.goodsIds = new ArrayList<Integer>();
		t5.goodsIds.add(new Integer(7));
		t5.goodsIds.add(new Integer(12));
		t5.goodsIds.add(new Integer(13));
		t5.delta = new ArrayList<Delta>();
		t5.delta.add(new Delta(1));
		t5.delta.add(new Delta(-1));
		t5.delta.add(new Delta(-1));

		bid_2_xor1.add(t5);

		bid_2.add(bid_2_xor1);

		ArrayList<ArrayList<Transformation>> bid_3 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_3_xor1 = new ArrayList<Transformation>();

		Transformation t6 = new Transformation();
		// ((0, 1))
		t6.goodsIds = new ArrayList<Integer>();
		t6.goodsIds.add(new Integer(8));
		t6.goodsIds.add(new Integer(13));
		t6.goodsIds.add(new Integer(14));
		t6.delta = new ArrayList<Delta>();
		t6.delta.add(new Delta(2));
		t6.delta.add(new Delta(-2));
		t6.delta.add(new Delta(-2));

		bid_3_xor1.add(t6);

		// ((2, 3))
		Transformation t7 = new Transformation();
		t7.goodsIds = new ArrayList<Integer>();
		t7.goodsIds.add(new Integer(9));
		t7.goodsIds.add(new Integer(13));
		t7.goodsIds.add(new Integer(14));
		t7.delta = new ArrayList<Delta>();
		t7.delta.add(new Delta(2));
		t7.delta.add(new Delta(-3));
		t7.delta.add(new Delta(-10));

		bid_3_xor1.add(t7);

		bid_3.add(bid_3_xor1);

		ArrayList<ArrayList<Transformation>> bid_4 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_4_xor1 = new ArrayList<Transformation>();

		Transformation t8 = new Transformation();
		// ((0, 1))
		t8.goodsIds = new ArrayList<Integer>();
		t8.goodsIds.add(new Integer(0));
		t8.goodsIds.add(new Integer(3));
		t8.goodsIds.add(new Integer(4));
		t8.delta = new ArrayList<Delta>();
		t8.delta.add(new Delta(1));
		t8.delta.add(new Delta(-1));
		t8.delta.add(new Delta(-1));

		bid_4_xor1.add(t8);

		bid_4.add(bid_4_xor1);

		ArrayList<ArrayList<Transformation>> bid_5 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_5_xor1 = new ArrayList<Transformation>();

		Transformation t9 = new Transformation();
		// ((0, 1))
		t9.goodsIds = new ArrayList<Integer>();
		t9.goodsIds.add(new Integer(1));
		t9.goodsIds.add(new Integer(5));
		t9.goodsIds.add(new Integer(6));
		t9.goodsIds.add(new Integer(7));
		t9.delta = new ArrayList<Delta>();
		t9.delta.add(new Delta(4));
		t9.delta.add(new Delta(-1));
		t9.delta.add(new Delta(-2));
		t9.delta.add(new Delta(-1));

		bid_5_xor1.add(t9);

		bid_5.add(bid_5_xor1);

		ArrayList<ArrayList<Transformation>> bid_6 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_6_xor1 = new ArrayList<Transformation>();

		Transformation t10 = new Transformation();
		// ((0, 1))
		t10.goodsIds = new ArrayList<Integer>();
		t10.goodsIds.add(new Integer(2));
		t10.goodsIds.add(new Integer(8));
		t10.goodsIds.add(new Integer(9));
		t10.delta = new ArrayList<Delta>();
		t10.delta.add(new Delta(1));
		t10.delta.add(new Delta(-1));
		t10.delta.add(new Delta(-1));

		bid_6_xor1.add(t10);

		bid_6.add(bid_6_xor1);

		ArrayList<ArrayList<Transformation>> bid_7 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_7_xor1 = new ArrayList<Transformation>();

		Transformation t11 = new Transformation();
		// ((0, 1))
		t11.goodsIds = new ArrayList<Integer>();
		t11.goodsIds.add(new Integer(5));
		t11.goodsIds.add(new Integer(11));
		t11.goodsIds.add(new Integer(12));
		t11.delta = new ArrayList<Delta>();
		t11.delta.add(new Delta(1));
		t11.delta.add(new Delta(-1));
		t11.delta.add(new Delta(-1));

		bid_7_xor1.add(t11);

		Transformation t12 = new Transformation();
		// ((0, 1))
		t12.goodsIds = new ArrayList<Integer>();
		t12.goodsIds.add(new Integer(6));
		t12.goodsIds.add(new Integer(11));
		t12.goodsIds.add(new Integer(12));
		t12.goodsIds.add(new Integer(13));
		t12.delta = new ArrayList<Delta>();
		t12.delta.add(new Delta(2));
		t12.delta.add(new Delta(-2));
		t12.delta.add(new Delta(-2));
		t12.delta.add(new Delta(-2));

		bid_7_xor1.add(t12);

		Transformation t13 = new Transformation();
		// ((0, 1))
		t13.goodsIds = new ArrayList<Integer>();
		t13.goodsIds.add(new Integer(7));
		t13.goodsIds.add(new Integer(12));
		t13.goodsIds.add(new Integer(13));
		t13.delta = new ArrayList<Delta>();
		t13.delta.add(new Delta(1));
		t13.delta.add(new Delta(-1));
		t13.delta.add(new Delta(-1));

		bid_7_xor1.add(t13);

		bid_7.add(bid_7_xor1);

		ArrayList<ArrayList<Transformation>> bid_8 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_8_xor1 = new ArrayList<Transformation>();

		Transformation t14 = new Transformation();
		// ((1, 2))
		t14.goodsIds = new ArrayList<Integer>();
		t14.goodsIds.add(new Integer(1));
		t14.goodsIds.add(new Integer(5));
		t14.goodsIds.add(new Integer(6));
		t14.goodsIds.add(new Integer(7));
		t14.delta = new ArrayList<Delta>();
		t14.delta.add(new Delta(4));
		t14.delta.add(new Delta(-1));
		t14.delta.add(new Delta(-2));
		t14.delta.add(new Delta(-1));

		bid_8_xor1.add(t14);
		bid_8.add(bid_8_xor1);

		bids.add(bid_1);
		bids.add(bid_2);
		bids.add(bid_3);
		bids.add(bid_4);
		bids.add(bid_5);
		bids.add(bid_6);
		bids.add(bid_7);
		bids.add(bid_8);

		initialQuantity = new ArrayList<Integer>();
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(3);
		initialQuantity.add(4);
		initialQuantity.add(3);

		finalQuantity = new ArrayList<Integer>();
		finalQuantity.add(0);
		finalQuantity.add(4);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);

		costs = new ArrayList<ArrayList<Integer>>();
		ArrayList<Integer> cost_bid_1 = new ArrayList<Integer>();
		cost_bid_1.add(new Integer(-10));

		costs.add(cost_bid_1);

		ArrayList<Integer> cost_bid_2 = new ArrayList<Integer>();
		cost_bid_2.add(new Integer(-20));
		costs.add(cost_bid_2);

		ArrayList<Integer> cost_bid_3 = new ArrayList<Integer>();
		cost_bid_3.add(new Integer(-25));
		costs.add(cost_bid_3);

		ArrayList<Integer> cost_bid_4 = new ArrayList<Integer>();
		cost_bid_4.add(new Integer(-30));
		costs.add(cost_bid_4);

		ArrayList<Integer> cost_bid_5 = new ArrayList<Integer>();
		cost_bid_5.add(new Integer(-35));
		costs.add(cost_bid_5);

		ArrayList<Integer> cost_bid_6 = new ArrayList<Integer>();
		cost_bid_6.add(new Integer(-32));
		costs.add(cost_bid_6);

		ArrayList<Integer> cost_bid_7 = new ArrayList<Integer>();
		cost_bid_7.add(new Integer(-15));
		costs.add(cost_bid_7);

		ArrayList<Integer> cost_bid_8 = new ArrayList<Integer>();
		cost_bid_8.add(new Integer(-30));
		costs.add(cost_bid_8);

	}

	/**
	 * It creates an instance of the auction problem.
	 */
	public void setupProblem2() {
		bids = new ArrayList<ArrayList<ArrayList<Transformation> >>();

		ArrayList<ArrayList<Transformation>> bid_1 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_1_xor1 = new ArrayList<Transformation>();

		Transformation t1 = new Transformation();
		// ((0, 1))
		t1.goodsIds = new ArrayList<Integer>();
		t1.goodsIds.add(new Integer(3));
		t1.goodsIds.add(new Integer(0));
		t1.goodsIds.add(new Integer(1));
		t1.delta = new ArrayList<Delta>();
		t1.delta.add(new Delta(1));
		t1.delta.add(new Delta(-1));
		t1.delta.add(new Delta(-1));

		bid_1_xor1.add(t1);

		Transformation t2 = new Transformation();
		// ((0, 1))
		t2.goodsIds = new ArrayList<Integer>();
		t2.goodsIds.add(new Integer(4));
		t2.goodsIds.add(new Integer(0));
		t2.goodsIds.add(new Integer(1));
		t2.goodsIds.add(new Integer(2));
		t2.delta = new ArrayList<Delta>();
		t2.delta.add(new Delta(2));
		t2.delta.add(new Delta(-2));
		t2.delta.add(new Delta(-2));
		t2.delta.add(new Delta(-2));

		bid_1_xor1.add(t2);

		Transformation t3 = new Transformation();
		// ((0, 1))
		t3.goodsIds = new ArrayList<Integer>();
		t3.goodsIds.add(new Integer(5));
		t3.goodsIds.add(new Integer(1));
		t3.goodsIds.add(new Integer(2));
		t3.delta = new ArrayList<Delta>();
		t3.delta.add(new Delta(1));
		t3.delta.add(new Delta(-1));
		t3.delta.add(new Delta(-1));

		bid_1_xor1.add(t3);

		bid_1.add(bid_1_xor1);

		ArrayList<ArrayList<Transformation>> bid_2 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_2_xor1 = new ArrayList<Transformation>();

		Transformation t4 = new Transformation();
		// ((0, 1))
		t4.goodsIds = new ArrayList<Integer>();
		t4.goodsIds.add(new Integer(6));
		t4.goodsIds.add(new Integer(3));
		t4.goodsIds.add(new Integer(4));
		t4.goodsIds.add(new Integer(5));
		t4.delta = new ArrayList<Delta>();
		t4.delta.add(new Delta(4));
		t4.delta.add(new Delta(-1));
		t4.delta.add(new Delta(-2));
		t4.delta.add(new Delta(-1));

		bid_2_xor1.add(t4);

		bid_2.add(bid_2_xor1);

		ArrayList<ArrayList<Transformation>> bid_3 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_3_xor1 = new ArrayList<Transformation>();

		Transformation t5 = new Transformation();
		// ((0, 1))
		t5.goodsIds = new ArrayList<Integer>();
		t5.goodsIds.add(new Integer(3));
		t5.goodsIds.add(new Integer(0));
		t5.goodsIds.add(new Integer(1));
		t5.delta = new ArrayList<Delta>();
		t5.delta.add(new Delta(1));
		t5.delta.add(new Delta(-1));
		t5.delta.add(new Delta(-1));

		bid_3_xor1.add(t5);

		Transformation t6 = new Transformation();
		// ((0, 1))
		t6.goodsIds = new ArrayList<Integer>();
		t6.goodsIds.add(new Integer(4));
		t6.goodsIds.add(new Integer(0));
		t6.goodsIds.add(new Integer(1));
		t6.goodsIds.add(new Integer(2));
		t6.delta = new ArrayList<Delta>();
		t6.delta.add(new Delta(2));
		t6.delta.add(new Delta(-2));
		t6.delta.add(new Delta(-2));
		t6.delta.add(new Delta(-2));

		bid_3_xor1.add(t6);

		Transformation t7 = new Transformation();
		// ((0, 1))
		t7.goodsIds = new ArrayList<Integer>();
		t7.goodsIds.add(new Integer(5));
		t7.goodsIds.add(new Integer(1));
		t7.goodsIds.add(new Integer(2));
		t7.delta = new ArrayList<Delta>();
		t7.delta.add(new Delta(1));
		t7.delta.add(new Delta(-1));
		t7.delta.add(new Delta(-1));

		bid_3_xor1.add(t7);

		bid_3.add(bid_3_xor1);

		ArrayList<ArrayList<Transformation>> bid_4 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_4_xor1 = new ArrayList<Transformation>();

		Transformation t8 = new Transformation();
		// ((1, 2))
		t8.goodsIds = new ArrayList<Integer>();
		t8.goodsIds.add(new Integer(6));
		t8.goodsIds.add(new Integer(3));
		t8.goodsIds.add(new Integer(4));
		t8.goodsIds.add(new Integer(5));
		t8.delta = new ArrayList<Delta>();
		t8.delta.add(new Delta(4));
		t8.delta.add(new Delta(-1));
		t8.delta.add(new Delta(-2));
		t8.delta.add(new Delta(-1));

		bid_4_xor1.add(t8);
		bid_4.add(bid_4_xor1);

		initialQuantity = new ArrayList<Integer>();
		initialQuantity.add(3);
		initialQuantity.add(4);
		initialQuantity.add(3);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);

		finalQuantity = new ArrayList<Integer>();
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(4);

		costs = new ArrayList<ArrayList<Integer>>();

		bids.add(bid_1);
		bids.add(bid_2);
		bids.add(bid_3);
		bids.add(bid_4);

		ArrayList<Integer> cost_bid_1 = new ArrayList<Integer>();
		cost_bid_1.add(new Integer(-20));
		costs.add(cost_bid_1);

		ArrayList<Integer> cost_bid_2 = new ArrayList<Integer>();
		cost_bid_2.add(new Integer(-35));
		costs.add(cost_bid_2);

		ArrayList<Integer> cost_bid_3 = new ArrayList<Integer>();
		cost_bid_3.add(new Integer(-15));
		costs.add(cost_bid_3);

		ArrayList<Integer> cost_bid_4 = new ArrayList<Integer>();
		cost_bid_4.add(new Integer(-30));
		costs.add(cost_bid_4);
	}

	/**
	 * It creates an instance of the auction problem.
	 */
	public void setupProblem3() {

		bids = new ArrayList<ArrayList<ArrayList<Transformation> >>();

		ArrayList<ArrayList<Transformation>> bid_1 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_1_xor1 = new ArrayList<Transformation>();

		Transformation t1 = new Transformation();
		// ((0, 1))
		t1.goodsIds = new ArrayList<Integer>();
		t1.goodsIds.add(new Integer(0));
		t1.goodsIds.add(new Integer(1));
		t1.delta = new ArrayList<Delta>();
		t1.delta.add(new Delta(-1));
		t1.delta.add(new Delta(1));

		bid_1_xor1.add(t1);

		// ((2, 3))
		Transformation t2 = new Transformation();
		t2.goodsIds = new ArrayList<Integer>();
		t2.goodsIds.add(new Integer(2));
		t2.goodsIds.add(new Integer(3));
		t2.delta = new ArrayList<Delta>();
		t2.delta.add(new Delta(-1));
		t2.delta.add(new Delta(1));

		bid_1_xor1.add(t2);

		bid_1.add(bid_1_xor1);

		ArrayList<ArrayList<Transformation>> bid_2 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_2_xor1 = new ArrayList<Transformation>();

		Transformation t4 = new Transformation();
		// ((0, 1))
		t4.goodsIds = new ArrayList<Integer>();
		t4.goodsIds.add(new Integer(0));
		t4.goodsIds.add(new Integer(1));
		t4.delta = new ArrayList<Delta>();
		t4.delta.add(new Delta(-1));
		t4.delta.add(new Delta(1));

		bid_2_xor1.add(t4);

		// ((2, 3))
		Transformation t5 = new Transformation();
		t5.goodsIds = new ArrayList<Integer>();
		t5.goodsIds.add(new Integer(2));
		t5.goodsIds.add(new Integer(3));
		t5.delta = new ArrayList<Delta>();
		t5.delta.add(new Delta(-1));
		t5.delta.add(new Delta(1));

		bid_2_xor1.add(t5);

		bid_2.add(bid_2_xor1);

		ArrayList<ArrayList<Transformation>> bid_3 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_3_xor1 = new ArrayList<Transformation>();

		Transformation t3 = new Transformation();
		// ((1, 2))
		t3.goodsIds = new ArrayList<Integer>();
		t3.goodsIds.add(new Integer(1));
		t3.goodsIds.add(new Integer(2));
		t3.delta = new ArrayList<Delta>();
		t3.delta.add(new Delta(-1));
		t3.delta.add(new Delta(1));

		bid_3_xor1.add(t3);
		bid_3.add(bid_3_xor1);

		bids.add(bid_1);
		bids.add(bid_2);
		bids.add(bid_3);

		initialQuantity = new ArrayList<Integer>();
		initialQuantity.add(1);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);

		finalQuantity = new ArrayList<Integer>();
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(1);

		costs = new ArrayList<ArrayList<Integer>>();
		ArrayList<Integer> cost_bid_1 = new ArrayList<Integer>();
		cost_bid_1.add(new Integer(-5));

		costs.add(cost_bid_1);

		ArrayList<Integer> cost_bid_2 = new ArrayList<Integer>();
		cost_bid_2.add(new Integer(-8));

		costs.add(cost_bid_2);

		ArrayList<Integer> cost_bid_3 = new ArrayList<Integer>();
		cost_bid_3.add(new Integer(-2));
		costs.add(cost_bid_3);

	}

	/**
	 * It creates an instance of the auction problem.
	 */
	public void setupProblem4() {

		noGoods = 4;

		bids = new ArrayList<ArrayList<ArrayList<Transformation> >>();

		ArrayList<ArrayList<Transformation>> bid_1 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_1_xor1 = new ArrayList<Transformation>();

		Transformation t1 = new Transformation();
		// ((0, 1))
		t1.goodsIds = new ArrayList<Integer>();
		t1.goodsIds.add(new Integer(0));
		t1.goodsIds.add(new Integer(1));
		t1.delta = new ArrayList<Delta>();
		t1.delta.add(new Delta(-1));
		t1.delta.add(new Delta(1));

		bid_1_xor1.add(t1);

		// ((2, 3))
		Transformation t2 = new Transformation();
		t2.goodsIds = new ArrayList<Integer>();
		t2.goodsIds.add(new Integer(2));
		t2.goodsIds.add(new Integer(3));
		t2.delta = new ArrayList<Delta>();
		t2.delta.add(new Delta(-1));
		t2.delta.add(new Delta(1));

		bid_1_xor1.add(t2);

		bid_1.add(bid_1_xor1);

		ArrayList<Transformation> bid_1_xor2 = new ArrayList<Transformation>();

		Transformation t4 = new Transformation();
		// ((0, 1))
		t4.goodsIds = new ArrayList<Integer>();
		t4.goodsIds.add(new Integer(0));
		t4.goodsIds.add(new Integer(1));
		t4.delta = new ArrayList<Delta>();
		t4.delta.add(new Delta(-1));
		t4.delta.add(new Delta(1));

		bid_1_xor2.add(t4);

		// ((2, 3))
		Transformation t5 = new Transformation();
		t5.goodsIds = new ArrayList<Integer>();
		t5.goodsIds.add(new Integer(2));
		t5.goodsIds.add(new Integer(3));
		t5.delta = new ArrayList<Delta>();
		t5.delta.add(new Delta(-1));
		t5.delta.add(new Delta(1));

		bid_1_xor2.add(t5);

		bid_1.add(bid_1_xor2);




		ArrayList<ArrayList<Transformation>> bid_2 = new ArrayList<ArrayList<Transformation>>();

		ArrayList<Transformation> bid_2_xor1 = new ArrayList<Transformation>();

		Transformation t3 = new Transformation();
		// ((1, 2))
		t3.goodsIds = new ArrayList<Integer>();
		t3.goodsIds.add(new Integer(1));
		t3.goodsIds.add(new Integer(2));
		t3.delta = new ArrayList<Delta>();
		t3.delta.add(new Delta(-1));
		t3.delta.add(new Delta(1));

		bid_2_xor1.add(t3);
		bid_2.add(bid_2_xor1);

		bids.add(bid_1);
		bids.add(bid_2);

		initialQuantity = new ArrayList<Integer>();
		initialQuantity.add(1);
		initialQuantity.add(0);
		initialQuantity.add(0);
		initialQuantity.add(0);

		finalQuantity = new ArrayList<Integer>();
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(0);
		finalQuantity.add(1);

		costs = new ArrayList<ArrayList<Integer>>();
		ArrayList<Integer> cost_bid_1 = new ArrayList<Integer>();
		cost_bid_1.add(new Integer(-5));
		cost_bid_1.add(new Integer(-8));

		costs.add(cost_bid_1);

		ArrayList<Integer> cost_bid_2 = new ArrayList<Integer>();
		cost_bid_2.add(new Integer(-2));
		costs.add(cost_bid_2);

	}

	/**
	 * It executes the program which solve the supplied auction problem or
	 * solves three problems available within the files. 
	 * 
	 * @param args the first argument specifies the name of the file containing the problem description.
	 */
	public static void main(String[] args) {

		MUCA problem = new MUCA();

		if (args.length > 0) {
			problem.filename = args[0];
		
			problem.model();

			problem.searchSpecial();
		
			return;
		}
		
		problem.model();
		problem.searchSpecial();
		
		problem = new MUCA();
		problem.filename = "./ExamplesJaCoP/testset1.auct";
		problem.model();
		problem.searchSpecial();
		
		problem = new MUCA();
		problem.filename = "./ExamplesJaCoP/testset2.auct";
		problem.model();
		problem.searchSpecial();
		
	}

	@Override
	public void model() {

		readAuction(filename);

		store = new Store();

		// maximal number of transformations in a sequence.
		maxNoTransformations = 0;
		// number of transformations
		int noAvailableTransformations = 0;

		for (ArrayList<ArrayList<Transformation>> bid : bids) {

			int max = 0;

			for(ArrayList<Transformation> bid_xor : bid) {
				noAvailableTransformations += bid_xor.size();
				if (bid_xor.size() > max)
					max = bid_xor.size();
			}

			maxNoTransformations += max;
		}

		// Variables, transition ordering

		transitions = new IntVar[maxNoTransformations];

		for(int i = 0; i < maxNoTransformations; i++)
			transitions[i] = new IntVar(store, "t" + (i+1), 0, noAvailableTransformations);
		for(int i = 0; i < maxNoTransformations - 1; i++)
			store.impose(new IfThen(new XeqC(transitions[i], 0), new XeqC(transitions[i+1], 0)));
		// for each set of transformations create an among

		IntVar usedTransformation[] = new IntVar[noAvailableTransformations];

		for(int i = 0; i < noAvailableTransformations; i++) {

			usedTransformation[i] = new IntVar(store, "isUsed_"+(i+1), 0, 1);
			IntervalDomain kSet = new IntervalDomain(i+1, i+1);
			store.impose(new Among(transitions, kSet, usedTransformation[i]));

		}

		int noTransformations = 0;
		int no = 0;

		ArrayList<IntVar> usedXorBids = new ArrayList<IntVar>();

		bidCosts = new ArrayList<IntVar>();

		for (ArrayList<ArrayList<Transformation>> bid : bids) {

			IntVar [] nVars = new IntVar[bid.size()+1];
			int [][] tuples = new int[bid.size()+1][];
			// tuples[0] denotes [0, 0, ....] so bid is not used.
			tuples[0] = new int[bid.size()+1];

			int i = 0;
			for(ArrayList<Transformation> bid_xor : bid) {

				IntervalDomain kSet = new IntervalDomain();

				ArrayList<IntVar> xorUsedTransformation = new ArrayList<IntVar>();
				for (Transformation t : bid_xor) {
					noTransformations++;
					t.id = noTransformations;
					kSet.unionAdapt(noTransformations, noTransformations);
					xorUsedTransformation.add(usedTransformation[t.id - 1]);
				}

				IntVar n = new IntVar(store, "ind_" + no + "_" + i);
				n.addDom(0, 0);
				n.addDom(bid_xor.size(), bid_xor.size());

				store.impose(new Sum(xorUsedTransformation, n));

				usedXorBids.add(n);

				nVars[++i] = n;
				tuples[i] = new int[bid.size()+1];
				tuples[i][0] = costs.get(no).get(i-1);
				tuples[i][i] = n.max();

				store.impose(new Among(transitions, kSet, n));

			}

			IntVar bidCost = new IntVar(store, "bidCost" + (bidCosts.size()+1), minCost,
					maxCost);
			nVars[0] = bidCost;

			store.impose(new ExtensionalSupportVA(nVars, tuples));
			bidCosts.add(bidCost);

			no++;
		}

		deltasI  = new IntVar[maxNoTransformations][noGoods];
		deltasO  = new IntVar[maxNoTransformations][noGoods];

		sum = new IntVar[noGoods];

		for (int g = 0; g < noGoods; g++) {

			ArrayList<int []> tuples4transitions = new ArrayList<int[]>();

			int[] dummyTransition = {0, 0, 0};
			tuples4transitions.add(dummyTransition);

			for (ArrayList<ArrayList<Transformation>> bid : bids) {

				for(ArrayList<Transformation> bid_xor : bid) {

					for (Transformation t : bid_xor) {

						int [] tuple = { t.id, -t.getDeltaInput(g), t.getDeltaOutput(g) };
						tuples4transitions.add(tuple);

					}
				}
			}

			int tuples [][] = new int[tuples4transitions.size()][];
			for (int i = 0; i < tuples4transitions.size(); i++) {
				tuples[i] = tuples4transitions.get(i);
			}

			IntVar previousPartialSum = new IntVar(store, "initialQuantity_" + g,
					initialQuantity.get(g),
					initialQuantity.get(g));

			for (int i = 0; i < maxNoTransformations; i++) {

				ArrayList<IntVar> vars = new ArrayList<IntVar>();
				vars.add(transitions[i]);
				deltasI[i][g] = new IntVar(store, "deltaI_g" + g + "t" + i, minDelta, maxDelta);
				vars.add(deltasI[i][g]);
				deltasO[i][g] = new IntVar(store, "deltaO_g" + g + "t" + i, minDelta, maxDelta);
				vars.add(deltasO[i][g]);

				store.impose(new ExtensionalSupportVA(vars, tuples));

				store.impose(new XplusYgtC(previousPartialSum, deltasI[i][g], -1));

				IntVar partialSum = new IntVar(store, "partialSum_" + g + "_" + i, 0, maxProducts );
				store.impose(new XplusYplusQeqZ(previousPartialSum, deltasI[i][g], deltasO[i][g], partialSum));

				// store.impose(new XgteqC(partialSum, 0));
				previousPartialSum = partialSum;
			}

			store.impose(new XgteqC(previousPartialSum, finalQuantity.get(g)));
			sum[g] = previousPartialSum;
		}


		for (int g = 0; g < noGoods; g++) {

			IntVar weights [] = new IntVar[usedTransformation.length + 1];
			weights[0] = new IntVar(store, String.valueOf(initialQuantity.get(g)) + "of-g" + g, 
					initialQuantity.get(g), initialQuantity.get(g));

			for (ArrayList<ArrayList<Transformation>> bid : bids) {

				for(ArrayList<Transformation> bid_xor : bid) {

					for (Transformation t : bid_xor) {

						int[][] tuples = new int[2][2];

						if (t.getDelta(g) >= 0)
							weights[t.id] = new IntVar(store, "delta_tid_" + t.id + "_g" + g, 
									0, t.getDelta(g));
						else
							weights[t.id] = new IntVar(store, "delta_t" + t.id + "_g" + g, 
									t.getDelta(g), 0);

						tuples[0][0] = 0;
						tuples[0][1] = 0;
						tuples[1][0] = 1;
						tuples[1][1] = t.getDelta(g);

						IntVar[] vars = {usedTransformation[t.id - 1], weights[t.id]};
						store.impose(new ExtensionalSupportVA(vars, tuples));                                  	  

					}
				}

			}

			store.impose(new Sum(weights, sum[g]));

		}              

		cost = new IntVar(store, "cost", minCost, maxCost);

		store.impose(new Sum(bidCosts, cost));

	}

	/**
	 * It executes special master-slave search. The master search
	 * uses costs variables and maxregret criteria to choose an 
	 * interesting bids. The second search (slave) looks for the 
	 * sequence of chosen transactions such as that all constraints
	 * concerning goods quantity (deltas of transitions) are respected.
	 * 
	 * @return true if there is a solution, false otherwise.
	 */
	public boolean searchSpecial() {

		Search<IntVar> search1 = new DepthFirstSearch<IntVar>();
		SelectChoicePoint<IntVar> select1 = new SimpleSelect<IntVar>(bidCosts.toArray(new IntVar[1]), new MaxRegret<IntVar>(),
				new IndomainMin<IntVar>());

		Search<IntVar> search2 = new DepthFirstSearch<IntVar>();
		SelectChoicePoint<IntVar> select2 = new SimpleSelect<IntVar>(transitions, null,
				new IndomainMin<IntVar>());       

		search1.addChildSearch(search2);
		search2.setSelectChoicePoint(select2);

		boolean result = search1.labeling(store, select1, cost);             

		System.out.print("\t");

		for (int i = 0; i < maxNoTransformations && transitions[i].value() != 0; i++)
			System.out.print(transitions[i] + "\t");
		System.out.println();

		for (int g = 0; g < noGoods; g++) {

			System.out.print(initialQuantity.get(g) + "\t");
			for (int i = 0; i < maxNoTransformations && transitions[i].value() != 0; i++)
				System.out.print( deltasI[i][g].value() + "," + deltasO[i][g].value() + "\t");

			System.out.println(sum[g].value() + ">=" + finalQuantity.get(g));

		}

		return result;
	}

	class Delta {

		// Both must be positive, even if input means consuming.

		public int input;
		public int output;

		public Delta(int input, int output) {

			this.input = input;
			this.output = output;

		}

		// negative means consumption, positive means production.
		public Delta(int delta) {

			if (delta > 0) {

				input = 0;
				output = delta;
			}
			else {
				input = -delta;
				output = 0;
			}
		}
	}

	class Transformation {

		public ArrayList<Integer> goodsIds;
		public ArrayList<Delta> delta;
		public int id;

		public int getDelta(int goodId) {

			for (int i = 0; i < goodsIds.size(); i++)
				if (goodsIds.get(i) == goodId)
					return delta.get(i).output - delta.get(i).input;

			return 0;
		}


		public int getDeltaInput(int goodId) {

			for (int i = 0; i < goodsIds.size(); i++)
				if (goodsIds.get(i) == goodId)
					return delta.get(i).input;

			return 0;
		}

		public int getDeltaOutput(int goodId) {

			for (int i = 0; i < goodsIds.size(); i++)
				if (goodsIds.get(i) == goodId)
					return delta.get(i).output;

			return 0;
		}
	}

	/**
	 * It reads the auction problem from the file.
	 * @param filename file describing the auction problem.
	 */
	public void readAuction(String filename) {

		noGoods = 0;

		try {
			BufferedReader br = new BufferedReader(new FileReader(filename));

			// the first line represents the input goods
			String line = br.readLine();
			StringTokenizer tk = new StringTokenizer(line, "(),: ");

			initialQuantity = new ArrayList<Integer>();

			while(tk.hasMoreTokens()) {
				noGoods++;
				tk.nextToken();
				initialQuantity.add(Integer.valueOf(tk.nextToken()));
			}

			// the second line represents the output goods
			line = br.readLine();
			tk = new StringTokenizer(line, "(),: ");

			finalQuantity = new ArrayList<Integer>();

			while(tk.hasMoreTokens()) {
				tk.nextToken();
				finalQuantity.add(Integer.valueOf(tk.nextToken()));
			}

			// until the word price is read, one is reading transformations.
			// Assume that the transformations are properly grouped

			line = br.readLine();

			int bidCounter     = 1;
			int bid_xorCounter = 1;
			int transformationCounter = 0;
			int goodsCounter   = 0;
			int Id, in, out;

			int[] input;
			int[] output;

			bids = new ArrayList<ArrayList<ArrayList<Transformation> >>();

			bids.add(new ArrayList<ArrayList<Transformation>>());

			(bids.get(0)).add(new ArrayList<Transformation>());

			while(! line.equals("price")) {
				tk = new StringTokenizer(line, "():, ");
				transformationCounter++;

				if(Integer.valueOf(tk.nextToken()) > bidCounter) {
					bidCounter++;
					bid_xorCounter = 1;
					transformationCounter = 1;

					bids.add(new ArrayList<ArrayList<Transformation>>());
					bids.get(bidCounter - 1).add(new ArrayList<Transformation>());
				}
				//System.out.println(bidCounter + " " + bid_xorCounter);
				if(Integer.valueOf(tk.nextToken()) > bid_xorCounter) {
					bid_xorCounter++;
					transformationCounter = 1;

					bids.get(bidCounter - 1).add(new ArrayList<Transformation>());
				}
				// this token contains the number of the transformation
				tk.nextToken();
				bids.get(bidCounter - 1).get(bid_xorCounter - 1).add(new Transformation());

				bids.get(bidCounter - 1).get(bid_xorCounter - 1).get(transformationCounter - 1).goodsIds = new ArrayList<Integer>();
				bids.get(bidCounter - 1).get(bid_xorCounter - 1).get(transformationCounter - 1).delta = new ArrayList<Delta>();

				input = new int[noGoods];
				output = new int[noGoods];

				goodsCounter = 0;
				while(tk.hasMoreTokens()) {
					goodsCounter++;
					//System.out.println(goodsCounter);
					if(goodsCounter <= noGoods) {
						Id = Integer.valueOf(tk.nextToken()) - 1;
						in = Integer.valueOf(tk.nextToken());
						input[Id] = in;
					}
					else {
						Id = Integer.valueOf(tk.nextToken()) - 1;
						out = Integer.valueOf(tk.nextToken());
						output[Id] = out;
					}
				}

				for(int i = 0; i < noGoods; i++) {
					//delta = output[i] - input[i];
					if(output[i] > maxDelta) {
						maxDelta = output[i];
					}
					else if(-input[i] < minDelta) {
						minDelta = -input[i];
					}

					if(output[i] != 0 || input[i] != 0) {
						//System.out.print(i + " " + input[i] + ":" + output[i] + " ");
						//System.out.println(bidCounter + " " + bid_xorCounter + " " + transformationCounter + " " + i + " " + delta);
						bids.get(bidCounter - 1).get(bid_xorCounter - 1).get(transformationCounter - 1).goodsIds.add(i);                                         
						bids.get(bidCounter - 1).get(bid_xorCounter - 1).get(transformationCounter - 1).delta.add(new Delta(input[i], output[i]));
					}
				}
				System.out.print("\n");

				line = br.readLine();
			}

			// now read in the price for each xor bid

			costs = new ArrayList<ArrayList<Integer>>();

			costs.add(new ArrayList<Integer>());

			bidCounter = 1;

			line = br.readLine();

			while(! (line == null)) {
				tk = new StringTokenizer(line, "(): ");

				if(Integer.valueOf(tk.nextToken()) > bidCounter) {
					bidCounter++;
					costs.add(new ArrayList<Integer>());
				}

				// this token contains the xor_bid id.
				tk.nextToken();

				costs.get(bidCounter - 1).add(new Integer(tk.nextToken()));

				line = br.readLine();

			}

		}
		catch(FileNotFoundException ex) {
			System.err.println("You need to run this program in a directory that contains the required file.");
			System.err.println(ex);
			System.exit(-1);
		}
		catch(IOException ex) {
			System.err.println(ex);
		}

		System.out.println(this.maxCost);
		System.out.println(this.maxDelta);
		System.out.println(this.minDelta);
	}

}










