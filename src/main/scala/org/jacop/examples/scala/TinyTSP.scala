/*
 * TinyTSP.java
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
object TinyTSP extends App with jacop {

  setPrecision(1e-12)

  val N = 4  // number of cities

  val x = Array(0.0, 1.0, 2.0, 2.0)
  val y = Array(3.0, 1.0, 2.0, 0.0)
  val d = Array.tabulate(N,N)( (i,j) => scala.math.sqrt((x(i) - x(j))*(x(i) - x(j)) + (y(i) - y(j)) * (y(i) - y(j))))

  val visit = Array.tabulate(N)( i => new IntVar("visit[" + i + "]", 1, N))

  val dist = List.tabulate(N)(i => d(i)(visit(i)))

  val distance = new FloatVar("distance", 0, 1000);
  distance #= sum(dist.toList)

  circuit(visit)

  val result = minimize(search(visit, input_order, indomain_min), distance, () => printValue) 
  statistics

  def printValue() {
    print(1 + " -> ")
    var index = 1
    for (i <- 1 to N) {
      if (i < N)
	print(visit(index-1).value + " -> ")
      else
	print(visit(index-1).value)
      index = visit(index-1).value
    }
    println("\n" + distance) 

  }
}
