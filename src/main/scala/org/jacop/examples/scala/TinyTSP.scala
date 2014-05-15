package org.jacop.examples.scala

import org.jacop.scala._

object TinyTSP extends App with jacop {

  setPrecision(1e-12)

  val N = 4  // number of cities

  val x = Array(0.0, 1.0, 2.0, 2.0)
  val y = Array(3.0, 1.0, 2.0, 0.0)
  val d = Array.tabulate(N,N)( (i,j) => scala.math.sqrt((x(i) - x(j))*(x(i) - x(j)) + (y(i) - y(j)) * (y(i) - y(j))))

  val visit = Array.tabulate(N)( i => new IntVar("visit[" + i + "]", 1, N))

  val dist = List.tabulate(N)(i => d(i)(visit(i)))

  val distance = new FloatVar("distance", 0, 1000);
  distance #= sum(dist.toList)

  circuit(visit)

  val result = minimize(search(visit, input_order, indomain_min), distance, () => printValue) 
  statistics

  def printValue() {
    print(1 + " -> ")
    var index = 1
    for (i <- 1 to N) {
      if (i < N)
	print(visit(index-1).value + " -> ")
      else
	print(visit(index-1).value)
      index = visit(index-1).value
    }
    println("\n" + distance) 

  }
}
