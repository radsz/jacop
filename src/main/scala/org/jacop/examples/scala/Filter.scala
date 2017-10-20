/*
 * Filter.java
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
object Filter extends App with jacop {

  val addId = 1
  val mulId = 2
  val dependencies = Array ( Array(0, 2 ), Array( 0, 15 ), Array( 0, 17 ), Array( 1, 4 ),
			     Array( 1, 8 ), Array( 1, 11 ), Array( 2, 3 ), Array( 2, 7 ), Array( 2, 9 ), Array( 3, 4 ),
			     Array( 4, 5 ), Array( 4, 6 ), Array( 4, 10 ), Array( 5, 7 ), Array( 6, 8 ), Array( 7, 9 ),
			     Array( 7, 10 ), Array( 8, 11 ), Array( 8, 13 ), Array( 8, 19 ), Array( 9, 12 ), Array( 10, 13 ),
			     Array( 11, 14 ), Array( 12, 15 ), Array( 14, 16 ), Array( 15, 17 ), Array( 15, 18 ),
			     Array( 15, 29 ), Array( 16, 20 ), Array( 16, 28 ), Array( 16, 19 ), Array( 17, 21 ),
			     Array( 18, 22 ), Array( 19, 23 ), Array( 20, 24 ), Array( 21, 27 ), Array( 22, 25 ),
			     Array( 22, 32 ), Array( 23, 26 ), Array( 23, 33 ), Array( 16, 28 ), Array( 24, 28 ),
			     Array( 25, 30 ), Array( 26, 31 ), Array( 27, 29 ), Array( 30, 32 ), Array( 31, 33 ) )

  val ids = Array( addId, addId, addId, addId, addId, mulId, mulId, addId,
		  addId, addId, addId, addId, mulId, addId, mulId, addId, addId,
		  addId, addId, addId, addId, mulId, addId, addId, mulId, mulId,
		  mulId, addId, addId, addId, addId, addId, addId, addId )

  val last = Array( 13, 24, 28, 29, 30, 31, 32, 33 )

  val delAdd = new IntVar("delAdd", 1,1)
  val delMul = new IntVar("delMul", 2,2)

  val t = Array.tabulate(ids.length)( i => new IntVar("t"+i, 0, 100))  
  val r = Array.tabulate(ids.length)( i => if (ids(i) == addId) new IntVar("r"+i, 1, 2) else new IntVar("r"+i, 3, 4) )  
  val del = Array.tabulate(ids.length)( i => if (ids(i) == addId) delAdd else delMul )  

  for (i <- 0 until dependencies.length) 
    t(dependencies(i)(0)) + del(dependencies(i)(0)) #<= t(dependencies(i)(1))

  val endOps = List.tabulate(last.length)( i => t(last(i)) + del(last(i)) )
  val end = max(endOps)

//   val one = new IntVar("1", 1,1)
  val rectangles: Array[Array[IntVar]] = Array.tabulate(ids.length) ( i => Array(t(i), r(i), del(i), 1))
  diff2(rectangles)

//   val tAdd = for (i <- Array.range(0, t.length); if (ids(i) == addId) ) yield t(i)
//   val dAdd = for (i <- Array.range(0, del.length); if (ids(i) == addId) ) yield del(i)
//   val rAdd = for (i <- Array.range(0, r.length); if (ids(i) == addId) ) yield one
//   val limitAdd = new IntVar("limitAdd", 0, 2)
//   cumulative(tAdd, dAdd, rAdd, limitAdd)

//   val tMul = for (i <- Array.range(0, t.length); if (ids(i) == mulId) ) yield t(i)
//   val dMul = for (i <- Array.range(0, del.length); if (ids(i) == mulId) ) yield del(i)
//   val rMul = for (i <- Array.range(0, r.length); if (ids(i) == mulId) ) yield one
//   val limitMul = new IntVar("limitMul", 0, 2)
//   cumulative(tMul, dMul, rMul, limitMul)

  // Search
  val tr = List.tabulate(t.length) ( i => List(t(i), r(i)))

  // numberSolutions(2)
  val result = minimize( search_vector(tr, smallest_min, indomain_min), end, () => printSol )
  // numberSolutions(2)
  // val result = minimize_seq( List(search(t, smallest_min, indomain_min), search(r, input_order, indomain_min)), 
			    // end, printSol )

  statistics()

  def printSol() : Unit = {
    println("\nSolution with cost: " + end.value + "\n=======================")
    println(tr)
  }
}
