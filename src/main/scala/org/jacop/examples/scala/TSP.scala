package org.jacop.examples.scala

import org.jacop.scala._

/**
 * 
 * It models Travelling Salesman Problem (TSP). 
 * 
 * @author Krzysztof Kuchcinski
 *
 */

object TSP extends App with jacop {

// 	IntVar[][] varsMatrix;
	

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

