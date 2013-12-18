package org.jacop.examples.scala

import org.jacop.scala._

object BIBD extends jacop {

  /**
   * It specifies number of rows in the incidence matrix. 
   */
  var v = 7
  /**
   * It specifies number of columns in the incidence matrix. 
   */
  var b = 7
  /**
   * It specifies number of ones in each row.
   */
  var r = 3
  /**
   * It specifies number of ones in each column. 
   */
  var k = 3
  /**
   * It specifies the value of the scalar product of any two distinct rows.
   */
  var lambda = 1

  def main(args: Array[String]) {

    if (args.length > 1) {
      try {
 	v = args(0).toInt
 	b = args(1).toInt
 	r = args(2).toInt
 	k = args(3).toInt
 	lambda = args(4).toInt
      }
      catch {
 	case ex: Exception => println("Program parameters if provided must specify v, b, r, k, and lambda")
      }
    }	
    model()
  }

  def model() = {

    val x = List.tabulate(v,b)( (i,j) => new BoolVar("x" + i + "_" + j))

    // sum on rows
    for (i <- 0 until v)
      sum(x(i).toList) #= r // (new IntVar(0,0)/:x(i)) (_ + _)  #= r

    // sum on columns
    for (j <- 0 until b) 
      sum( List.tabulate(v)( i => x(i)(j)) ) #= k

    for ( i <- 0 to v)
      for ( j <- i+1 until v) 
 	sum( List.tabulate(b)( m => x(i)(m) /\ x(j)(m)) ) #= lambda

     val result = satisfy( search(x.flatMap(_.toList), first_fail, indomain_min) )

    if (result) 
      for (i <- 0 until v) {
	for (j <- 0 until b)
	  print(""+x(i)(j).value+" ")
	println()
      }
    else println("No solution")	

  }	
}
