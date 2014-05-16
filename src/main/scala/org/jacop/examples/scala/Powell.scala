package org.jacop.examples.scala

import org.jacop.scala._

// Problem 1 from paper "Some tests of Generalized Bisection" by R. Baker Kearfott.

object Powell extends App with jacop {

  setPrecision(1e-20)

  val x = Array.tabulate(4)( i => new FloatVar("x[" + i + "]", -2, 2))

  // constraint
  x(0) + 10.0*x(1) #= 0.0

  scala.math.sqrt(5.0)*(x(2) - x(3)) #= 0.0

  (x(1) - 2.0*x(2))*(x(1) - 2.0*x(2)) #= 0.0

  scala.math.sqrt(10.0)*(x(0) - x(3))*(x(0) - x(3)) #= 0.0

  val result = satisfyAll(search_float(x.toList, input_order), () => println(x.toList)) 
  statistics

}
