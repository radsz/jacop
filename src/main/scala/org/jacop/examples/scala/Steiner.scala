package org.jacop.examples.scala

import org.jacop.scala._

object Steiner extends App { //with jacop {

  val n = 7
  val nb = n * (n-1) / 6

  val sets = List.tabulate(nb)( i => new SetVar("set_"+i, 1, n))

  // all sets must have three elements
  sets.foreach(s => card(s) #= 3)

  // there are at most one element common to two sets
  for (i <- 0 until n; j <- i+1 until n) 
    card( sets(i) * sets(j) ) #<= 1 

// Symmetry breaking:
  for (i <- 0 until n-1) 
    sets(i) #<= sets(i+1)

  val result = satisfy( search(sets, input_order, indomain_min_set) )

  if (result) {
    sets.foreach(si => print(si.dom + " "))
    println() 
  }
  else println("No solution")

}
