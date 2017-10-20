/*
 * Queen.java
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
object Queen extends App with jacop {

  val n = 50

  val q: List[IntVar] = for (i <- List.range(0, n)) yield new IntVar("q"+i, 0, n)

  def noattack(i: Int, j: Int, qi: IntVar, qj: IntVar) = {
	qi     #\= qj 
	qi + i #\= qj + j 
	qi - i #\= qj - j 
  }

  for (i <- 0 until n; j <- i+1 until n) noattack(i, j, q(i), q(j))

  val result = satisfy( search(q, first_fail, indomain_middle) )

  if (result) 
    q.foreach(qi => {
      for( i <- 0 until n) 
 	if (qi.value() == i) print(" # ") else print(" . ")
      println()

    })
  else println("No solution")
}
