/*
 * Adder.java
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
object Adder extends App with jacop {

  val a = new BoolVar("a")
  val b = new BoolVar("b")
  val c = new BoolVar("c")
  val summa = new BoolVar("summa")
  val carry = new BoolVar("carry")

  // summa part
  summa #= (a xor b xor c)

  // carry part
  carry #= ((c /\ (a xor b)) \/ (a /\ b))

  recordSolutions = true

  val result = satisfyAll(search(List(a, b, c, summa, carry), input_order, indomain_min), printTableRow()) 

  println("" + a + " " + b + " " + " " + c + " " + " " + summa + " " + " " + carry)

  def printTableRow() = () => {
    println(a.value + " | " + b.value + " | " + c.value + " || " + summa.value + " | " + carry.value )
  }
}
