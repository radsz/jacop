package org.jacop.examples.scala

import java.io.BufferedReader
import java.io.FileNotFoundException
import java.io.FileReader
import java.io.IOException
import java.util.StringTokenizer


/**
 * 
 * It solves the Mixed Multi-Unit Combinatorial Auctions. 
 * 
 * @author Radoslaw Szymanek (for Scala Krzysztof Kuchcinski)
 * @version 3.0
 * 
 * 
 * The idea originated from reading the following paper 
 * where the first attempt to use CP was presented.
 * 
 * Comparing Winner Determination Algorithms for Mixed
 * Multi-Unit Combinatorial Auctions by Brammert Ottens
 * Ulle Endriss
 * 
 */

import scala.collection.mutable.ArrayBuffer
import org.jacop.scala._

object MUCA  extends jacop {

  /**
   * ArrayBuffer of bids issued by different bidders. 
   * Each bidder issues an ArrayBuffer of xor bids. 
   * Each Xor bid is a list of transformations. 
   */
  var bids : ArrayBuffer[ArrayBuffer[ArrayBuffer[ Transformation] ]] = null

  /**
   * For each bidder and each xor bid there is an 
   * integer representing a cost of the xor bid.
   */
  var costs : ArrayBuffer[ArrayBuffer[Int]] = null

  /**
   * It specifies the initial quantities of goods.
   */
  var initialQuantity : List[Int] = List()

  /**
   * It specifies the minimal quantities of items seeked to achieve.
   */
  var finalQuantity : List[Int] = List()

  /**
   * It specifies number of goods which are in the focus of the auction.
   */
  var noGoods = 7

  /**
   * It specifies the minimal possible delta of goods for any transformation.
   */
  var minDelta = -10
	
  /**
   * It specifies the maximal possible delta of goods for any transformation.
   */
  
  var maxDelta = 10

  /**
   * It specifies the minimal value for the cost.
   */
  val minCost = -100000

  /**
   * It specifies the maximal value for the cost.
   */
  val maxCost = 100000

  var cost : IntVar = null
	
  /**
   * The maximal number of products.
   */
  val maxProducts = 100

  /**
   * For each bidder it specifies variable representing 
   * the cost of the chosen xor bid.
   */
  var bidCosts : List[IntVar] = null
	
  /**
   * It specifies the sequence of transitions used by an auctioneer.
   */
  var transitions : Array[IntVar] = null

  /**
   * It specifies the maximal number of transformations used by the auctioneer.
   */
  var maxNoTransformations : Int = 0
	
  /**
   * For each transition and each good it specifies the 
   * delta change of that good before the transition takes place.
   */
  var deltasI : Array[Array[IntVar]] = null

  /**
   * For each transition and each good it specifies the 
   * delta change of that good after the transition takes place.
   */	
  var deltasO : Array[Array[IntVar]] = null

  /**
   * It specifies the number of goods after the last transition.
   */
  var summa : Array[IntVar] = null

  /**
   * It reads auction problem description from the file.
   */
  var filename : String = "./ExamplesJaCoP/testset3.auct"

  /**
   * It executes the program which solve the supplied auction problem or
   * solves three problems available within the files. 
   * 
   * @param args the first argument specifies the name of the file containing the problem description.
   */
  def main(args: Array[String]) {

    if (args.length > 0)
      filename = args(0)
    else 
      filename = "/Users/kris/research/JaCoP-3.1/ExamplesJaCoP/testset3.auct"

    model()
  }


  def model() {

    readAuction(filename)

    // maximal number of transformations in a sequence.
    maxNoTransformations = 0
    // number of transformations
    var noAvailableTransformations = 0

    for ( bid <- bids) {
      var max = 0

      for (bid_xor <- bid) {

	noAvailableTransformations += bid_xor.length
	if (bid_xor.length > max)
	  max = bid_xor.length
      }

      maxNoTransformations += max
    }

    // Variables, transition ordering
    transitions = Array.tabulate(maxNoTransformations)( i => new IntVar("t" + (i+1), 0, noAvailableTransformations))

    for(i <- 0 until maxNoTransformations - 1) {
      val b = new BoolVar("b"+i)
      b <=> (transitions(i) #= 0)
      b -> (transitions(i+1) #= 0)
    }

    // for each set of transformations create an among

    val usedTransformation = Array.tabulate(noAvailableTransformations)(i => new IntVar("isUsed_"+(i+1), 0, 1))

    for(i <- 0 until noAvailableTransformations) 
      among(transitions, new IntSet(i+1, i+1), usedTransformation(i))

    var noTransformations = 0
    var no = 0

    var usedXorBids = new ArrayBuffer[IntVar]()

    bidCosts = List[IntVar]()

    for (bid <- bids) {
      val nVars = new Array[IntVar](bid.length + 1)
      val tuples = new Array[Array[Int]](bid.length + 1)
      // tuples[0] denotes [0, 0, ....] so bid is not used.
      tuples(0) = new Array[Int](bid.length + 1)

      var i = 0
      for (bid_xor <- bid) {
	var kSet = new IntSet()

	var xorUsedTransformation = new ArrayBuffer[IntVar]()
	for( t <- bid_xor) {
	  noTransformations += 1
	  t.id = noTransformations
	  // + is set union ;)
 	  kSet += noTransformations
	  xorUsedTransformation :+= usedTransformation(t.id - 1)
	}

	val n = new IntVar("ind_" + no + "_" + i, 0, 0)
	n.addDom(bid_xor.length, bid_xor.length)

 	sum(xorUsedTransformation.toList) #= n

	usedXorBids :+= n

	i += 1
	nVars(i) = n
	tuples(i) = new Array[Int](bid.length + 1)
	tuples(i)(0) = costs(no)(i-1)
	tuples(i)(i) = n.max()

	among(transitions, kSet, n)

      }

      val bidCost = new IntVar("bidCost" + (bidCosts.length+1), minCost, maxCost)
      nVars(0) = bidCost
      
      table(nVars.toList, tuples)

      bidCosts :+= bidCost

      no += 1
  }

    deltasI = Array.ofDim(maxNoTransformations, noGoods) 
    deltasO = Array.ofDim(maxNoTransformations, noGoods)

    summa = new Array[IntVar](noGoods)

    for (g <- 0 until noGoods) {

      var tuples4transitions = new ArrayBuffer[Array[Int]]()
      val dummyTransition = Array[Int](0, 0, 0)
      tuples4transitions :+= dummyTransition

      bids.foreach( bid => 
	bid.foreach( bid_xor => 
	  bid_xor.foreach( t => 
	    tuples4transitions :+= Array[Int]( t.id, -t.getDeltaInput(g), t.getDeltaOutput(g)))))
 
      val tuples  = tuples4transitions.toArray 

      var previousPartialSum = new IntVar("initialQuantity_" + g, initialQuantity(g), initialQuantity(g))

      for (i <- 0 until maxNoTransformations) {

	var vars = List[IntVar]()
	vars :+= transitions(i)
	deltasI(i)(g) = new IntVar("deltaI_g" + g + "t" + i, minDelta, maxDelta)
	vars :+= deltasI(i)(g)
	deltasO(i)(g) = new IntVar("deltaO_g" + g + "t" + i, minDelta, maxDelta)
	vars :+= deltasO(i)(g)
	
	table(vars.toList, tuples)

	(previousPartialSum + deltasI(i)(g)) #> -1

	val partialSum = new IntVar("partialSum_" + g + "_" + i, 0, maxProducts )
	previousPartialSum + deltasI(i)(g) + deltasO(i)(g) #= partialSum

	previousPartialSum = partialSum
      }

      previousPartialSum #>= finalQuantity(g)
      summa(g) = previousPartialSum
    }


    for (g <- 0 until noGoods) {

      val weights = new Array[IntVar](usedTransformation.length + 1)
      weights(0) = new IntVar(String.valueOf(initialQuantity(g)) + "of-g" + g, 
					initialQuantity(g), initialQuantity(g))

      for (bid <- bids) {
	for (bid_xor <- bid ) {
	  for (t <- bid_xor) {
	    if (t.getDelta(g) >= 0)
	      weights(t.id) = new IntVar("delta_tid_" + t.id + "_g" + g, 0, t.getDelta(g))
	    else
	      weights(t.id) = new IntVar("delta_t" + t.id + "_g",  t.getDelta(g), 0)

	    val tuples = Array(Array(0, 0), Array(1, t.getDelta(g)))
	    val vars = Array(usedTransformation(t.id - 1), weights(t.id))

 	    table(vars.toList, tuples)
	  }
	}
      }
      sum(weights.toList) #= summa(g)
    }              

    cost = sum(bidCosts.toList)

    searchSpecial 

  }


  /**
   * It executes special master-slave search. The master search
   * uses costs variables and maxregret criteria to choose an 
   * interesting bids. The second search (slave) looks for the 
   * sequence of chosen transactions such as that all constraints
   * concerning goods quantity (deltas of transitions) are respected.
   * 
   * @return true if there is a solution, false otherwise.
   */
  def searchSpecial : Boolean = {

    val search1 = search(bidCosts, max_regret, indomain_min)
    val search2 = search(transitions.toList, input_order, indomain_min)

    val result = minimize_seq(List(search1, search2), cost)

    print("\t")

    for (i <- 0 until maxNoTransformations if transitions(i).value() != 0 )
      print(transitions(i) + "\t")
    println()

    for (g <- 0 until noGoods) {

      print(initialQuantity(g) + "\t")
      for (i <- 0 until maxNoTransformations if transitions(i).value() != 0 )
  	print( deltasI(i)(g).value() + "," + deltasO(i)(g).value() + "\t")
      
      println(summa(g).value() + ">=" + finalQuantity(g))

    }

    result
  }

  class Delta(var input : Int, var output : Int) {

    // Both must be positive, even if input means consuming.

    // negative means consumption, positive means production.
    def this(delta : Int) = {
      this( if (delta > 0) 0 else - delta, if (delta > 0) delta else 0)
     }
  }


  class Transformation {

    var goodsIds : ArrayBuffer[Int] = new ArrayBuffer[Int]()
    var delta : ArrayBuffer[Delta] = new ArrayBuffer[Delta]()
    var id : Int = 0

    def getDelta(goodId : Int) : Int = {

      for (i <- 0 until goodsIds.size)
	if (goodsIds(i) == goodId)
	  return delta(i).output - delta(i).input

       0
    }

    def getDeltaInput(goodId : Int) : Int = {

      for (i <- 0 until goodsIds.size)
	if (goodsIds(i) == goodId)
	  return delta(i).input

       0
    }

    def getDeltaOutput(goodId : Int) : Int = {

      for (i <- 0 until goodsIds.size)
	if (goodsIds(i) == goodId)
	  return delta(i).output

       0
    }

    override def toString : String = {

      var st = "*** "
      for (i <- 0 until goodsIds.size) 
	st += "id ="+goodsIds(i) + "(" +getDeltaInput(goodsIds(i))+", "+getDeltaOutput(goodsIds(i))+") "
       st
    }
	    
  }


  /**
   * It reads the auction problem from the file.
   * @param filename file describing the auction problem.
   */
  def readAuction(filename : String) {

    noGoods = 0

    try {
      val br = new BufferedReader(new FileReader(filename))

      // the first line represents the input goods
      var line = br.readLine()
      var tk = new StringTokenizer(line, "(),: ")

      while(tk.hasMoreTokens) {
	noGoods += 1
	tk.nextToken()
	initialQuantity :+= tk.nextToken.toInt
      }

      // the second line represents the output goods
      line = br.readLine()
      tk = new StringTokenizer(line, "(),: ")

      while(tk.hasMoreTokens) {
	tk.nextToken()
	finalQuantity :+= tk.nextToken().toInt
      }

      // until the word price is read, one is reading transformations.
      // Assume that the transformations are properly grouped

      line = br.readLine()

      var bidCounter     = 1
      var bid_xorCounter = 1
      var transformationCounter = 0
      var goodsCounter   = 0
      var Id=0; var in=0; var  out=0

      var input : Array[Int] = null
      var output : Array[Int] = null

      bids = new ArrayBuffer[ArrayBuffer[ArrayBuffer[Transformation] ]]()

      bids :+= new ArrayBuffer[ArrayBuffer[Transformation]]()

      bids(0) :+= new ArrayBuffer[Transformation]()


      while(! line.equals("price")) {
	tk = new StringTokenizer(line, "():, ")
	transformationCounter += 1

	if(tk.nextToken().toInt > bidCounter) {
	  bidCounter += 1
	  bid_xorCounter = 1
	  transformationCounter = 1

	  bids :+= new ArrayBuffer[ArrayBuffer[Transformation]]()
	  bids(bidCounter - 1) :+= new ArrayBuffer[Transformation]()
	}
// 				System.out.println(bidCounter + " " + bid_xorCounter);
	if(tk.nextToken().toInt > bid_xorCounter) {
	  bid_xorCounter += 1
	  transformationCounter = 1
	  
	  bids(bidCounter - 1) :+= new ArrayBuffer[Transformation]()
	}
				// this token contains the number of the transformation
	tk.nextToken()
	bids(bidCounter - 1)(bid_xorCounter - 1) :+= new Transformation()

	bids(bidCounter - 1)(bid_xorCounter - 1)(transformationCounter - 1).goodsIds = new ArrayBuffer[Int]()
	bids(bidCounter - 1)(bid_xorCounter - 1)(transformationCounter - 1).delta = new ArrayBuffer[Delta]()

	input = new Array[Int](noGoods)
	output = new Array[Int](noGoods)

	goodsCounter = 0
	while(tk.hasMoreTokens) {
	  goodsCounter += 1
// 	  System.out.println(goodsCounter);
	  if(goodsCounter <= noGoods) {
	    Id = tk.nextToken().toInt - 1
	    in = tk.nextToken().toInt
	    input(Id) = in
	  }
	  else {
	    Id = tk.nextToken().toInt - 1
	    out = tk.nextToken().toInt
	    output(Id) = out
	  }
	}

	for(i <- 0 until noGoods) {
	  //delta = output[i] - input[i];
	  if(output(i) > maxDelta) {
	    maxDelta = output(i)
	  }
	  else if(-input(i) < minDelta) {
	    minDelta = -input(i)
	  }
	  
	  if(output(i) != 0 || input(i) != 0) {
// 						System.out.print(i + " " + input[i] + ":" + output[i] + " ");
// 						System.out.println(bidCounter + " " + bid_xorCounter + " " + transformationCounter + " " + i + " " + delta);
	    bids(bidCounter - 1)(bid_xorCounter - 1)(transformationCounter - 1).goodsIds :+= i                                         
	    bids(bidCounter - 1)(bid_xorCounter - 1)(transformationCounter - 1).delta :+= new Delta(input(i), output(i))
	  }
	}
// 				System.out.print("\n");

	line = br.readLine()
      }

      // now read in the price for each xor bid

      costs = new ArrayBuffer[ArrayBuffer[Int]]()

      costs :+= new ArrayBuffer[Int]()

      bidCounter = 1

      line = br.readLine()

      while(! (line == null)) {
	tk = new StringTokenizer(line, "(): ")

	if(tk.nextToken().toInt > bidCounter) {
	  bidCounter += 1
	  costs :+= new ArrayBuffer[Int]()
	}

	// this token contains the xor_bid id.
	tk.nextToken()

	costs(bidCounter - 1) :+= tk.nextToken().toInt

	line = br.readLine()

      }

    }
    catch {
      case ex : FileNotFoundException =>
        System.err.println("You need to run this program in a directory that contains the required file.")
        System.err.println(ex)
        System.exit(-1)
      case ex : IOException  =>
        System.err.println(ex)
    }

//     println(this.maxCost);
//     println(this.maxDelta);
//     println(this.minDelta);

//     println ("bids = "+bids);
//     println ("costs = "+costs);

  }

}
