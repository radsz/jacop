/*
 * Transistors.java
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
object Transistors extends App with jacop {

  def ntran(b: BoolVar, x: BoolVar, y: BoolVar) = b -> (x #= y)
  def ptran(b: BoolVar, x: BoolVar, y: BoolVar) = (~ b) -> (x #= y)

  val a = new BoolVar("a")
  val b = new BoolVar("b")
  val c = new BoolVar("c")
  val sum = new BoolVar("sum")
  val carry = new BoolVar("carry")
  val nca = new BoolVar("nca")
  val t = Array.tabulate(6)(i => new BoolVar("t"+i))
  val q = Array.tabulate(4)(i => new BoolVar("q"+i))
  val one = true //new BoolVar("1", 1, 1)
  val zero = false //new BoolVar("0", 0, 0)

  // sum part
  ptran(nca, t(0), one)
  ptran(c, one, t(4))
  ptran(b, t(0), t(4))
  ptran(a, t(0), t(1))
  ptran(nca, t(4), t(1))
  ptran(t(1), one, sum)
  ntran(a, t(1), t(2))
  ntran(nca, t(1), t(5))
  ntran(t(1), sum, zero)
  ntran(b, t(2), t(5))
  ntran(nca, t(2), zero)
  ntran(c, t(5), zero)

  // carry part
  ptran(a, q(0), one)
  ptran(b, q(0), one)
  ptran(a, q(1), one)
  ptran(c, q(0), nca)
  ptran(b, q(1), nca)
  ptran(nca, one, carry)
  ntran(c, nca, q(2))
  ntran(b, nca, q(3))
  ntran(nca, carry, zero)
  ntran(a, q(2), zero)
  ntran(b, q(2), zero)
  ntran(a, q(3), zero)

  val result = satisfyAll( search(List(a, b, c, sum, carry), input_order, indomain_min) )

  println(a + " " + b + " " + " " + c + " " + " " + sum + " " + " " + carry)

}
