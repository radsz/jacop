/*
 * Golomb.java
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
object Golomb extends App with jacop {

  val start = System.currentTimeMillis() 

  // Golomb
  val m = 8
  val n = m*m

  val mark = //: Array[IntVar] =
//     for (i <- Array.range(0, m)) yield new IntVar("mark"+i, 0, n)
    Array.tabulate(m)(i => new IntVar("mark"+i, 0, n))

  val differences = // : Array[IntVar] =
    for (i <- Array.range(0, m); j <- Array.range(i+1, m) ) yield mark(j) - mark(i)
//          (for (i <- 0 until m; j <- i+1 until m) yield mark(j) - mark(i)).toArray
    
//   for ( i <- 0 to differences.length - 1) differences(i) #>= 0
   differences.foreach(diff => diff #>= 0)
//   Array.tabulate(differences.length) (i => differences(i) #>= 0)

  mark(0) #= 0  

//   for (i <- 0 until m-1) mark(i) < mark(i+1)  
  Array.tabulate(m-1)(i => mark(i) #< mark(i+1)) //.foreach(println) 

  differences(0) #< differences(differences.length - 1) 

  alldifferent(differences)

  val result = minimize( search(mark.toList, input_order, indomain_min), mark(m-1))

  val end = System.currentTimeMillis() 

  if (result) {
    print("Golomb ruler : ")

    for (i <- 0 until m) print(mark(i).dom + " ")

    println("\n\n*** Execution time = " + (end - start) + " ms")
  }
    else println("No solution")
}

