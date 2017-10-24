/*
 * Jobshop.java
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
object Jobshop extends App with jacop {

  val m = Array(Array(2,0,1,3,5,4),
                Array(1,2,4,5,0,3),
                Array(2,3,5,0,1,4),
                Array(1,0,2,3,4,5),
                Array(2,1,4,5,0,3),
                Array(1,3,5,0,4,2)
         )
  val d = Array(Array(1,3,6,7,3,6),
                Array(8,5,10,10,10,4),
                Array(5,4,8,9,1,7),
                Array(5,5,5,3,8,9),
                Array(9,3,5,4,3,1),
                Array(3,3,9,10,4,1)
          )

  val n = m.length
  val k = m(0).length

  // task start times
  val t = Array.tabulate(n,k)( (i,j) => new IntVar("t_"+i+"_"+j, 0, 100))

  // jobs complition time
  val compl = Array.tabulate(n) (i => t(i)(k-1) + d(i)(k-1))
  val end = max(compl)

  // precedence constraints
  for (i <- 0 until n; j <- 0 until k-1)
      t(i)(j) + d(i)(j) #<= t(i)(j+1)

  // resource constraints
  val max_res = n
  val one = new IntVar("1", 1, 1)
  val ones = Array.tabulate(n) ( i => one)

  for ( l <- 0 until max_res) {
    val Ts = for (i <- Array.range(0, n); j <- Array.range (0, k) if m(i)(j) == l) yield  t(i)(j)
    val Ds = for (i <- Array.range (0, n); j <- Array.range (0, k) if m(i)(j) == l) yield   new IntVar("", d(i)(j), d(i)(j))

    cumulative(Ts, Ds, ones, 1)
  }

  val t_list : List[IntVar] = List.tabulate(n,k)( (i,j) => t(i)(j)).flatten
  val result = minimize( search(t_list, smallest, indomain_min), end, () => printSol)

//printSol)

  statistics()

  def printSol() : Unit = {
    println("\nSolution with cost: " + end.value + "\n=======================")
    for (i <- 0 until n)
      println(t(i).toList)
  }

}
