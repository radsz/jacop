/**
 *  Parcel.java 
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

import org.jacop.constraints.Circuit;
import org.jacop.constraints.Element;
import org.jacop.constraints.Sum;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * It solves a simple parcel shipment problem. 
 * 
 * @author Radoslaw Szymanek
 *
 */
public class Parcel extends ExampleFD {

	@Override
	public void model() {

		final int noCities = 10;
		
		// Specifies distance between any two cities
		// 1000 - large value to remove possibility of self loop
		int[][] distance = { { 1000, 85, 110, 94, 71, 76, 25, 56, 94, 67 },
				{ 85, 1000, 26, 70, 62, 60, 63, 62, 70, 49 },
				{ 110, 26, 1000, 71, 87, 89, 88, 87, 93, 73 },
				{ 94, 70, 71, 1000, 121, 19, 82, 106, 124, 105 },
				{ 71, 62, 87, 121, 1000, 104, 53, 24, 8, 13 },
				{ 76, 60, 89, 19, 104, 1000, 65, 89, 108, 93 },
				{ 25, 63, 88, 82, 53, 65, 1000, 30, 57, 46 },
				{ 56, 62, 87, 106, 24, 89, 30, 1000, 23, 20 },
				{ 94, 70, 93, 124, 8, 108, 57, 23, 1000, 20 },
				{ 67, 49, 73, 105, 13, 93, 46, 20, 20, 1000 } };

		int maxLoad = 5;
		int minLoad = -6;
		int[] load_parcels = { 0, 1, 5, -6, 4, 3, -5, 2, 1, -3 };

		// Creating constraint store
		store = new Store();
		vars = new ArrayList<IntVar>();

		// Denotes a city to go to from
		// index city
		IntVar[] cities = new IntVar[noCities];
		// Denotes a cost of traveling between
		// index city and next city
		IntVar[] costs = new IntVar[noCities];
		// Denotes load of person at each city
		IntVar loads[] = new IntVar[noCities];

		for (int i = 0; i < cities.length; i++) {
			cities[i] = new IntVar(store, "cities[" + i + "]", 1, cities.length);
			loads[i] = new IntVar(store, "nextLoad[" + i + "]", minLoad, maxLoad);
			costs[i] = new IntVar(store, "costs[" + i + "]", 0, 1000);
			vars.add(costs[i]);
		}

		// Impose cuircuit constraint which makes sure
		// that array cities is a hamiltonian circuit
		store.impose(new Circuit(cities));

		// We start our journey at first city
		IntVar startTown = cities[0];

		// We have to check all steps of the trip to make
		// sure we satisfy load constraints.
		for (int i = 0; i < cities.length; i++) {
			// Variable nextTown denotes city which is visited in next move
			IntVar nextTown = new IntVar(store, "nextTown[" + i + "]", 1,
					cities.length);
			// This constraint defines nextTown value
			store.impose(new Element(startTown, cities, nextTown));
			// This constraint defines change in the load
			// i denotes here i-th city on the road
			store.impose(new Element(startTown, load_parcels, loads[i]));
			// This constraint computes cost.
			// i denotes here the number of the city person travels from.
			store.impose(new Element(cities[i], distance[i], costs[i]));

			// person has moved to the next town, so there is a new
			// startTown
			startTown = nextTown;
		}

		// Constraints below make sure that at no city the load
		// constraint is violated. Load is always between [0..15].
		for (int i = 0; i < cities.length; i++) {
			IntVar tripLoads[] = new IntVar[i + 1];
			for (int j = 0; j <= i; j++)
				tripLoads[j] = loads[j];
			IntVar partialLoad = new IntVar(store, "partialLoad[0-" + i + "]", 0, 15);
			store.impose(new Sum(tripLoads, partialLoad));
		}

		cost = new IntVar(store, "Cost", 0, 100000);

		// Computes the travel cost.
		store.impose(new Sum(costs, cost));

		vars.add(cost);

	}

	/**
	 * It executes the program to solve the parcel shipment problem.
	 * @param args
	 */
	public static void main(String args[]) {

		Parcel example = new Parcel();
		
		example.model();

		if (example.searchMaxRegretOptimal())
			System.out.println("Solution(s) found");
		
	}	
	
	
}
