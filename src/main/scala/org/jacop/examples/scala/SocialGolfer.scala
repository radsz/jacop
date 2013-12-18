package org.jacop.examples.scala

import org.jacop.scala._

/**
 * It is a Social Golfer example based on set variables.
 *
 * @author Krzysztof Kuchcinski
 * @version 3.0
 */

object SocialGolfer extends jacop {

  // 2, 7, 4
	
  var weeks = 3

  var groups = 2

  var players = 2

  var golferGroup: Array[Array[SetVar]] = null

  var vars: List[SetVar] = null

  /**
   * 
   * It runs a number of social golfer problems.
   * 
   * @param args- command's arguments
   */
  def main (args: Array[String]) {

    setup(3, 2, 2)
    model()
    solve()
		
    // Solved
    setup(2,5,4) // weeks - groups - players in each group
    model()
    solve()
		
    setup(2,6,4) // weeks - groups - players in each group
    model()
    solve()
		
    setup(2,7,4) // weeks - groups - players in each group
    model()
    solve()
		
    setup(3,5,4) // weeks - groups - players in each group
    model()
    solve()
		
    setup(3,6,4) // weeks - groups - players in each group
    model()
    solve()
		
    setup(3,7,4) // weeks - groups - players in each group
    model()
    solve()
		
    setup(4,5,4) // weeks - groups - players in each group
    model()
    solve()
		
    setup(4,6,5) // weeks - groups - players in each group
    model()
    solve()
		
    setup(4,7,4) // weeks - groups - players in each group
    model()
    solve()
		
    setup(4,9,4) // weeks - groups - players in each group
    model()
    solve()
		
    setup(5,5,3) // weeks - groups - players in each group
    model()
    solve()
		
    setup(5,7,4) // weeks - groups - players in each group
    model()
    solve()
    
    setup(5,8,3) // weeks - groups - players in each group
    model()
    solve()
		
    setup(6,6,3) // weeks - groups - players in each group
    model()
    solve()
		
    setup(5,3,2) // weeks - groups - players in each group
    model()
    solve()
		
    setup(4,3,3) // weeks - groups - players in each group
    model()
    solve()
		
  }

  /**
   * It sets the parameters for the model creation function. 
   * 
   * @param w- weeks
   * @param g- groups
   * @param p- players
   */
  def setup(w: Int, g: Int, p: Int) {

    weeks = w
    groups = g
    players = p

  }

  def model() {

    val N = groups * players
		
    val weights = new Array[Int](players)
		
    val base = scala.math.max(10, players + 1) //at least players + 1
		
    weights(players - 1) = 1

    var i = players - 2
    while (i >= 0) { 
      weights(i) = weights(i+1)*base
      i -= 1
    }
 
    println("\nSocial golfer problem " + weeks + "-" + groups + "-" + players)

    golferGroup = Array.tabulate(weeks, groups)( (i, j) => new SetVar("g_"+i+"_"+j, 1, N))

    Array.tabulate(weeks, groups)( (i, j) => card(golferGroup(i)(j)) #= players )

     for (i <- 0 until weeks; j <- 0 until groups) 
 	for (k <- j+1 until groups) 
 	  golferGroup(i)(j) <> golferGroup(i)(k)


    for (i <- 0 until weeks) {
			
      var t = golferGroup(i)(0)

      for (j  <-  1 until groups) 
	t = t + golferGroup(i)(j)
			
      t #= new IntSet(1, N)
    }

    for (i <- 0 until weeks)
      for (j <- i+1 until weeks) 
	if (i != j) 
	  for (k <- 0 until groups)
	    for (l <- 0 until groups) 
	      card( golferGroup(i)(k) * golferGroup(j)(l) ) #<= 1

    val v: Array[IntVar] = new Array[IntVar](weeks)
    val var1 = List.tabulate(weeks, players)( (i,j) => new IntVar("var"+i+"-"+j, 1, N))

    for (i <- 0 until weeks) {
      matching( golferGroup(i)(0), var1(i) )
      v(i) = sum( var1(i), weights)
    }
		
    for (i <- 0 until weeks-1)
      v(i) #<= v(i+1)

    vars = golferGroup.flatten.toList

  }

    def solve() {

      val tread = java.lang.Thread.currentThread()
      val b = java.lang.management.ManagementFactory.getThreadMXBean()

      val startCPU = b.getThreadCpuTime(tread.getId())
      val startUser = b.getThreadUserTime(tread.getId())

      val result = satisfy( search(vars, min_lub_card, indomain_min_set),  printSolution)

	if (result) {
	  println("*** Yes")
	  // for (i <- 0 until weeks) {
	  //   for (j <- 0 until groups) {
	  //     print(golferGroup(i)(j).dom()+" ")
	  //   }
	  //   println
	  // }
	}
	else
	  println("*** No")

      statistics()

      println( "ThreadCpuTime = " + (b.getThreadCpuTime(tread.getId()) - startCPU)/1e+6 + "ms")
      println( "ThreadUserTime = " + (b.getThreadUserTime(tread.getId()) - startUser)/1e+6 + "ms" )

    }

  def printSolution() = {
    for (i <- 0 until weeks) {
      for (j <- 0 until groups) {
	print(golferGroup(i)(j).dom()+" ")
      }
      println()
    }
  }

}
