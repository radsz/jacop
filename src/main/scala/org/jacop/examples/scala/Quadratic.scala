package org.jacop.examples.scala

import org.jacop.scala._

object Quadratic extends App with jacop {

  setPrecision(1e-12)

  val x = new FloatVar("x", -10, 10)
  val y = new FloatVar("y", -10, 10)

  // constraints
  2.0*x*y + y #= 1.0
  x*y #= 0.2

  val result = satisfyAll(search_float(List(x,y), input_order), () => println(x+"\n"+y)) 
  statistics
}
