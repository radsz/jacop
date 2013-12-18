package org.jacop.examples.scala

import org.jacop.scala._

object RegularExample extends App with jacop {


  val v = Array.tabulate(3)( i => new IntVar("v"+0, 0, 2))

  var dfa = new fsm(8) // create FSM with eight states

//   var dfa = new fsm() 
//   for (i <- 0 until 8) dfa += new state()

  dfa.init( dfa(0) )
  dfa.addFinalStates( Array(dfa(7)) )

  dfa(0) -> (0, dfa(1))
  dfa(0) -> (1, dfa(2))
  dfa(0) -> (2, dfa(3))
  dfa(1) -> (1, dfa(4))
  dfa(1) -> (2, dfa(5))
  dfa(2) -> (0, dfa(4))
  dfa(2) -> (2, dfa(6)) 
  dfa(3) -> (0, dfa(5))
  dfa(3) -> (1, dfa(6))
  dfa(4) -> (2, dfa(7))
  dfa(5) -> (1, dfa(7))
  dfa(6) -> (new IntSet(0, 0), dfa(7))

  println(dfa)

  regular(dfa, v.toList)

  val result = satisfyAll( search(v.toList, input_order, indomain_min) )
}
