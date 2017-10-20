/*
 * BIBD.java
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
  * @version 4.4
  */
object BIBD extends jacop {

  /**
   * It specifies number of rows in the incidence matrix. 
   */
  var v = 7
  /**
   * It specifies number of columns in the incidence matrix. 
   */
  var b = 7
  /**
   * It specifies number of ones in each row.
   */
  var r = 3
  /**
   * It specifies number of ones in each column. 
   */
  var k = 3
  /**
   * It specifies the value of the scalar product of any two distinct rows.
   */
  var lambda = 1

  def main(args: Array[String]) {

    if (args.length > 1) {
      try {
 	v = args(0).toInt
 	b = args(1).toInt
 	r = args(2).toInt
 	k = args(3).toInt
 	lambda = args(4).toInt
      }
      catch {
 	case ex: Exception => println("Program parameters if provided must specify v, b, r, k, and lambda")
      }
    }	
    model()
  }

  def model() = {

    val x = List.tabulate(v,b)( (i,j) => new BoolVar("x" + i + "_" + j))

    // sum on rows
    for (i <- 0 until v)
      sum(x(i).toList) #= r // (new IntVar(0,0)/:x(i)) (_ + _)  #= r

    // sum on columns
    for (j <- 0 until b) 
      sum( List.tabulate(v)( i => x(i)(j)) ) #= k

    for ( i <- 0 to v)
      for ( j <- i+1 until v) 
 	sum( List.tabulate(b)( m => x(i)(m) /\ x(j)(m)) ) #= lambda

     val result = satisfy( search(x.flatMap(_.toList), first_fail, indomain_min) )

    if (result) 
      for (i <- 0 until v) {
	for (j <- 0 until b)
	  print(""+x(i)(j).value+" ")
	println()
      }
    else println("No solution")	

  }	
}
