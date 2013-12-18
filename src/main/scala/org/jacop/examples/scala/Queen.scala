package org.jacop.examples.scala

import org.jacop.scala._

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
