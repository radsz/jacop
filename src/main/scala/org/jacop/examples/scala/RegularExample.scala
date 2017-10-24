/*
 * RegularExample.java
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
object RegularExample extends App with jacop {


  val v = Array.tabulate(3)( i => new IntVar("v"+0, 0, 2))

  var dfa = new fsm(8) // create FSM with eight states

//   var dfa = new fsm() 
//   for (i <- 0 until 8) dfa += new state()

  dfa.init( dfa(0) )
  dfa.addFinalStates( Array(dfa(7)) )

  dfa(0) -> (0, dfa(1))
  dfa(0) -> (1, dfa(2))
  dfa(0) -> (2, dfa(3))
  dfa(1) -> (1, dfa(4))
  dfa(1) -> (2, dfa(5))
  dfa(2) -> (0, dfa(4))
  dfa(2) -> (2, dfa(6)) 
  dfa(3) -> (0, dfa(5))
  dfa(3) -> (1, dfa(6))
  dfa(4) -> (2, dfa(7))
  dfa(5) -> (1, dfa(7))
  dfa(6) -> (new IntSet(0, 0), dfa(7))

  println(dfa)

  regular(dfa, v.toList)

  val result = satisfyAll( search(v.toList, input_order, indomain_min) )
}
