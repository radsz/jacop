/*
 * GraphColoringS.java
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
  * Graph coloring problem.
  *
  * @author Krzysztof Kuchcinski and Radoslaw Szymanek
  * @version 4.5
  */
object GraphColoringS extends App with jacop{
  val size = 4
  val v = Array.tabulate(size)(i => new IntVar("v"+i, 1, size))

  v.foreach(x => println(x))

  v(0) #\= v(1)
  v(0) #\= v(2)
  v(1) #\= v(2)
  v(1) #\= v(3)
  v(2) #\= v(3)

  val result = satisfy(search(v, input_order, indomain_min), printSol())
  statistics()

  if ( result )
    println("*** After Search: " + v(0)+", "+v(1) +", "+ v(2) +", "+v(3))
  else
    println("*** No")

  def printSol () = () => {
        println("Solution: " + v.toList)
  }

}
