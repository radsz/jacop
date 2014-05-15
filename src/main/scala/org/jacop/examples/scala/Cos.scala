package org.jacop.examples.scala

import org.jacop.scala._

object Cos extends App with jacop {

  setPrecision(1e-12)

  val x = new FloatVar("x", -10, 10)

  x #= cos(x)

  val result = satisfyAll(search_float(List(x), input_order), printValue) 
  statistics

  def printValue() {
    println("Value when cos(x)=x is " + x.value + ", precision = " + precision)
  }
}
