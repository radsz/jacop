package org.jacop.examples.scala

import org.jacop.scala._

/**
 * 
 * It solves a simple conference session placement problem.
 * 
 * @author Krzysztof Kuchcinski & Radoslaw Szymanek
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
