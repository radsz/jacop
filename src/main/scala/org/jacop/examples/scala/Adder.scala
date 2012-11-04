package org.jacop.examples.scala

import org.jacop.scala._

object Adder extends App with jacop {

  val a = new BoolVar("a")
  val b = new BoolVar("b")
  val c = new BoolVar("c")
  val summa = new BoolVar("summa")
  val carry = new BoolVar("carry")

  // summa part
  summa #= (a xor b xor c)

  // carry part
  carry #= ((c /\ (a xor b)) \/ (a /\ b))

  recordSolutions = true

  val result = satisfyAll(search(List(a, b, c, summa, carry), input_order, indomain_min), printTableRow) 

  println("" + a + " " + b + " " + " " + c + " " + " " + summa + " " + " " + carry)

  def printTableRow() {
    println(a.value + " | " + b.value + " | " + c.value + " || " + summa.value + " | " + carry.value )
  }
}
