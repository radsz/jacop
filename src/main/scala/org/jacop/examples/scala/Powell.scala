/*
 * Powell.java
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

// Problem 1 from paper "Some tests of Generalized Bisection" by R. Baker Kearfott.

/**
  * A problem defined as in Java based examples.
  *
  * rewriting to Scala by Krzysztof Kuchcinski.
  * @author Krzysztof Kuchcinski and Radoslaw Szymanek
  * @version 4.5
  */
object Powell extends App with jacop {

  setPrecision(1e-20)

  val x = Array.tabulate(4)( i => new FloatVar("x[" + i + "]", -2, 2))

  // constraint
  x(0) + 10.0*x(1) #= 0.0
  //sum(x, Array[Double](1, 10, 0, 0)) #= 0

  scala.math.sqrt(5.0)*(x(2) - x(3)) #= 0.0

  (x(1) - 2.0*x(2))*(x(1) - 2.0*x(2)) #= 0.0

  scala.math.sqrt(10.0)*(x(0) - x(3))*(x(0) - x(3)) #= 0.0

  val result = satisfyAll(search_float(x.toList, input_order), () => println(x.toList)) 
  statistics

}
