package org.jacop.examples.scala

import org.jacop.scala._

/**
 * The class Run is used to run test programs for JaCoP package.
 * It is used for test purpose only.
 *
 * @author Krzysztof Kuchcinski
 * @version 3.0
 */
object NetExample extends App with jacop {

  var vars: Array[IntVar] = null
  var COST: IntVar = null

  simpleNet()

  transportationProblem()

  assignment()


  def simpleNet() {
    var T1: Long = 0
    var T2: Long = 0 
    var T: Long = 0
    T1 = System.currentTimeMillis()


      val x = new Array[IntVar](8)

      var net = new network

      val source: node = node("source", 5)
      val sink = node("sink", -5)

      val A = node("A", 0)
      val B = node("B", 0)
      val C = node("C", 0)
      val D = node("D", 0)

      net = net + source + sink + A + B + C + D

      x(0) = new IntVar("x_0", 0, 5)
      x(1) = new IntVar("x_1", 0, 5)

      net.arc(source, A, 0, x(0))
      net.arc(source, C, 0, x(1))


      x(2) = new IntVar("a->b", 0, 5)
      x(3) = new IntVar("a->d", 0, 5)
      x(4) = new IntVar("c->b", 0, 5)
      x(5) = new IntVar("c->d", 0, 5)
      net.arc(A, B, 3, x(2))
      net.arc(A, D, 2, x(3))
      net.arc(C, B, 5, x(4))
      net.arc(C, D, 6, x(5))


      x(6) = new IntVar("x_6", 0, 5)
      x(7) = new IntVar("x_7", 0, 5)
      net.arc(B, sink, 0, x(6))
      net.arc(D, sink, 0, x(7))

      val cost = new IntVar("cost", 0, 1000)
      net.cost(cost)
      COST = cost

      network_flow(net)

      vars = x

      numberSolutions(3)
      val Result = minimize_seq(List(search(x.toList, input_order, indomain_min), 
				 search(List(cost), input_order, indomain_min)), 
			    cost,
			    printCost, printSol )
      statistics()

      if (Result) {
	  System.out.println("*** Yes")
	  System.out.println (cost)
      }
      else
	  System.out.println("*** No")

      T2 = System.currentTimeMillis()
      T = T2 - T1
      println("\n\t*** Execution time = "+ T + " ms")


    }

    def transportationProblem() {
      var T1: Long = 0
      var T2: Long = 0 
      var T: Long = 0
      T1 = System.currentTimeMillis()


      var net = new network

      val A = node("A", 0)
      val B = node("B", 0)
      val C = node("C", 0)
      val D = node("D", 0)
      val E = node("E", 0)
      val F = node("F", 0)
      

      val source = node("source", 9)  // should ne 5+3+3=11 but it does not work...

      val sinkD = node("sinkD", -3)
      val sinkE = node("sinkE", -3)
      val sinkF = node("sinkF", -3)

      net = net + source + sinkD + sinkE + sinkF + A + B + C + D + E + F

      val x = new Array[IntVar](13)

      x(0) = new IntVar("x_0", 0, 5)
      x(1) = new IntVar("x_1", 0, 3)
      x(2) = new IntVar("x_2", 0, 3)
      net.arc(source, A, 0, x(0))
      net.arc(source, B, 0, x(1))
      net.arc(source, C, 0, x(2))

      x(3) = new IntVar("a->d", 0, 5)
      x(4) = new IntVar("a->e", 0, 5)
      net.arc(A, D, 3, x(3))
      net.arc(A, E, 1, x(4))

      x(5) = new IntVar("b->d", 0, 3)
      x(6) = new IntVar("b->e", 0, 3)
      x(7) = new IntVar("b->f", 0, 3)
      net.arc(B, D, 4, x(5))
      net.arc(B, E, 2, x(6))
      net.arc(B, F, 4, x(7))

      x(8) = new IntVar("c->e", 0, 3)
      x(9) = new IntVar("c->f", 0, 3)
      net.arc(C, E, 3, x(8))
      net.arc(C, F, 3, x(9))

      x(10) = new IntVar("x_10", 3, 3)
      x(11) = new IntVar("x_11", 3, 3)
      x(12) = new IntVar("x_12", 3, 3)
      net.arc(D, sinkD, 0, x(10))
      net.arc(E, sinkE, 0, x(11))
      net.arc(F, sinkF, 0, x(12))

      val cost = new IntVar("cost", 0, 1000)
      net.cost(cost)
      COST = cost


      network_flow(net)

    vars = x

      val Result = minimize_seq(List(search(x.toList, input_order, indomain_min), 
				 search(List(cost), input_order, indomain_min)), 
			    cost,
			    printCost, printSol )

      statistics()

      if (Result) {
	  System.out.println("*** Yes")
	  System.out.println (cost)
      }
      else
	  System.out.println("*** No")

      T2 = System.currentTimeMillis()
      T = T2 - T1
      System.out.println("\n\t*** Execution time = "+ T + " ms")
    }

    def assignment() {

      var T1: Long = 0
      var T2: Long = 0 
      var T: Long = 0
      T1 = System.currentTimeMillis()


      var net = new network

      val A = node("A", 1)
      val B = node("B", 1)
      val C = node("C", 1)
      val D = node("D", 1)
      val n1 = node("n1", -1)
      val n2 = node("n2", -1)
      val n3 = node("n3", -1)
      val n4 = node("n4", -1)

      net = net + A + B + C + D + n1 + n2 + n3 + n4

      val x = new Array[IntVar](12)

      x(0) = new IntVar("a->2", 0, 1)
      x(1) = new IntVar("a->3", 0, 1)
      x(2) = new IntVar("a->4", 0, 1)
      net.arc(A, n2,  9, x(0))
      net.arc(A, n3,  7, x(1))
      net.arc(A, n4, 13, x(2))

      x(3) = new IntVar("b->1", 0, 1)
      x(4) = new IntVar("b->2", 0, 1)
      x(5) = new IntVar("b->3", 0, 1)
      net.arc(B, n1, 16, x(3))
      net.arc(B, n2, 13, x(4))
      net.arc(B, n3,  8, x(5))

      x(6) = new IntVar("c->1", 0, 1)
      x(7) = new IntVar("c->2", 0, 1)
      x(8) = new IntVar("c->4", 0, 1)
      net.arc(C, n1, 10, x(6))
      net.arc(C, n3,  6, x(7))
      net.arc(C, n4, 15, x(8))

      x(9) = new IntVar("d->1", 0, 1)
      x(10) = new IntVar("d->2", 0, 1)
      x(11) = new IntVar("d->3", 0, 1)
      net.arc(D, n1, 11, x(9))
      net.arc(D, n3, 13, x(10))
      net.arc(D, n4, 17, x(11))

      val cost = new IntVar("cost", 0, 1000)
      net.cost(cost)
      COST = cost

      network_flow(net)

      vars = x

      // numberSolutions(2)
      val Result = minimize_seq(List(search(x.toList, input_order, indomain_min), 
				 search(List(cost), input_order, indomain_min)), 
			    cost, 
			    printCost, printSol )

      statistics()

      if (Result) {
	  System.out.println("*** Yes")
	  System.out.println (cost)
      }
      else
	  System.out.println("*** No")

      T2 = System.currentTimeMillis()
      T = T2 - T1
      System.out.println("\n\t*** Execution time = "+ T + " ms")

    }

  def printCost() : Unit = {
    println(COST)
  }

  def printSol() : Unit = {
    println(vars.toList)
  }
}
