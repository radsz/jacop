package org.jacop.examples.scala

import org.jacop.scala._

/*
 * Created by IntelliJ IDEA.
 * User: kris
 * Date: 2012-06-13
 * Time: 12:15
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

  val result = satisfy(search(v, input_order, indomain_min), printSol)
  statistics()

  if ( result )
    println("*** After Search: " + v(0)+", "+v(1) +", "+ v(2) +", "+v(3))
  else
    println("*** No")

  def printSol () : Unit = {
        println("Solution: " + v.toList)
  }

}