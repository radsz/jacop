package org.jacop.examples.scala

import org.jacop.scala._

object Golomb extends App with jacop {

  val start = System.currentTimeMillis() 

  // Golomb
  val m = 8
  val n = m*m

  val mark = //: Array[IntVar] =
//     for (i <- Array.range(0, m)) yield new IntVar("mark"+i, 0, n)
    Array.tabulate(m)(i => new IntVar("mark"+i, 0, n))

  val differences = // : Array[IntVar] =
    for (i <- Array.range(0, m); j <- Array.range(i+1, m) ) yield mark(j) - mark(i)
//          (for (i <- 0 until m; j <- i+1 until m) yield mark(j) - mark(i)).toArray
    
//   for ( i <- 0 to differences.length - 1) differences(i) #>= 0
   differences.foreach(diff => diff #>= 0)
//   Array.tabulate(differences.length) (i => differences(i) #>= 0)

  mark(0) #= 0  

//   for (i <- 0 until m-1) mark(i) < mark(i+1)  
  Array.tabulate(m-1)(i => mark(i) #< mark(i+1)) //.foreach(println) 

  differences(0) #< differences(differences.length - 1) 

  alldifferent(differences)

  val result = minimize( search(mark.toList, input_order, indomain_min), mark(m-1))

  val end = System.currentTimeMillis() 

  if (result) {
    print("Golomb ruler : ")

    for (i <- 0 until m) print(mark(i).dom + " ")

    println("\n\n*** Execution time = " + (end - start) + " ms")
  }
    else println("No solution")
}

