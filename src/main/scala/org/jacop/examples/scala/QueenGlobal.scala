package org.jacop.examples.scala

import org.jacop.scala._

object QueenGlobal extends App with jacop {

  val n = 100

  val q = Array.tabulate(n)( i => new IntVar("q"+i, 0, n) )
  alldifferent(q)

  val q1 = Array.tabulate(n)( i => q(i) + i )
  alldifferent(q1)

  val q2 = Array.tabulate(n)( i => q(i) - i )
  alldifferent(q2)
  
  val result = satisfy( search(q, first_fail, indomain_middle) )

  if (result) println("Yes")
  else println("No solution")
}
