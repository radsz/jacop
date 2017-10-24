/*
 * TSP.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.examples.scala

import org.jacop.scala._

/**
  * A problem defined as in Java based examples.
  *
  * rewriting to Scala by Krzysztof Kuchcinski.
  * @author Krzysztof Kuchcinski and Radoslaw Szymanek
  * @version 4.5
  */
object TSP extends App with jacop {

  val noCities = 10
		
  // Specifies distance between any two cities
  // 1000 - large value to remove possibility of self loop
  val distance = Array(Array( 1000, 85, 110, 94, 71, 76, 25, 56, 94, 67 ),
		       Array( 85, 1000, 26, 70, 62, 60, 63, 62, 70, 49 ),
		       Array( 110, 26, 1000, 71, 87, 89, 88, 87, 93, 73 ),
		       Array( 94, 70, 71, 1000, 121, 19, 82, 106, 124, 105 ),
		       Array( 71, 62, 87, 121, 1000, 104, 53, 24, 8, 13 ),
		       Array( 76, 60, 89, 19, 104, 1000, 65, 89, 108, 93 ),
		       Array( 25, 63, 88, 82, 53, 65, 1000, 30, 57, 46 ),
		       Array( 56, 62, 87, 106, 24, 89, 30, 1000, 23, 20 ),
		       Array( 94, 70, 93, 124, 8, 108, 57, 23, 1000, 20 ),
		       Array( 67, 49, 73, 105, 13, 93, 46, 20, 20, 1000 ) )
		
		
  // Denotes a city to go to from index city
  val cities = Array.tabulate(noCities)( i => new IntVar("cities[" + (i + 1) + "]", 1, noCities))

  // Denotes a cost of traveling between index city and next city
  val costs = Array.tabulate(noCities)(i => new IntVar("costs[" + (i + 1) + "]", 0, 1000))

  // Impose cuircuit constraint which makes sure
  // that array cities is a hamiltonian circuit
  circuit(cities)

  // Computes a cost of traveling between ith city
  // and city[i]-th city
  for (i <- 0 until noCities) 
    distance(i)(cities(i)) #= costs(i)

  // Computes overall cost of traveling
  // simply sum of all costs
  val cost = sum(costs.toList)

  val result = minimize( search(cities.toList, first_fail, indomain_min), cost )

}	

