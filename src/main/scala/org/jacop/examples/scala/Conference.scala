/*
 * Conference.java
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
 * 
 * It solves a simple conference session placement problem.
 * rewriting to Scala by Krzysztof Kuchcinski.
 * @author Krzysztof Kuchcinski & Radoslaw Szymanek
 * @version 4.4
 *
 * It solves a simple conference example problem, where different sessions 
 * must be scheduled according to the specified constraints.
 *
 */

object Conference extends App with jacop {

  // session letter
  // A, B, C, D, E, F, G, H, I, J, K
  // session index number
  // 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10
  val iA = 0; val iB = 1; val iC = 2; val iD = 3; val iE = 4; val iF = 5
  val iG = 6; val iH = 7; val iI = 8; val iJ = 9; val iK = 10

  val sessions = Array.tabulate(11)( i => new IntVar("session[" + i + "]", 1, 4))

  // Imposing inequalities constraints between sessions
  // A != J
  sessions(iA) #\= sessions(iJ)
  // I != J
  sessions(iI) #\= sessions(iJ)
  // E != I
  sessions(iE) #\= sessions(iI)
  // C != F
  sessions(iC) #\= sessions(iF)
  // F != G
  sessions(iF) #\= sessions(iG)
  // D != H
  sessions(iD) #\= sessions(iH)
  // B != D
  sessions(iB) #\= sessions(iD)
  // E != K
  sessions(iE) #\= sessions(iK)

  // different times - B, G, H, I
  alldifferent( for (i <- Array(iB, iG, iH, iI)) yield sessions(i) )

  // different times - A, B, C, H
  alldifferent( for (i <- Array(iA, iB, iC, iH)) yield sessions(i) )

  // different times - A, E, G
  alldifferent( for (i <- Array(iA, iE, iG)) yield sessions(i) )

  // different times - B, H, K
  alldifferent( for (i <- Array(iB, iH, iK)) yield sessions(i) )

  // different times - D, F, J
  alldifferent( for (i <- Array(iD, iF, iJ)) yield sessions(i) )

  // sessions precedence

  // E < J, D < K, F < K
  sessions(iE) #< sessions(iJ)
  sessions(iD) #< sessions(iK)
  sessions(iF) #< sessions(iK)

  // session assignment
  sessions(iA) #= 1
  sessions(iJ) #= 4

  // There are 3 sessions per half a day, last hald a day only 2
  // Every half a day is a resource of capacity 3, and session J which
  // is assigned the last half a day has a resource requirement 2, others 1.

  val one = new IntVar("one", 1, 1)
  val two = new IntVar("two", 2, 2)
  val three = new IntVar("three", 3, 3)

  val durations = Array.tabulate(11)( i => one)

  val resources = Array.tabulate(11)( i => if (i == iJ) two else one)

  cumulative(sessions, durations, resources, three)

//   println(Model)

  val result = satisfyAll( search_split(sessions.toList, most_constrained) )

}
