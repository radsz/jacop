package org.jacop.examples.scala

import java.io.BufferedReader
import java.io.FileNotFoundException
import java.io.FileReader
import java.io.IOException
import java.util.regex.Pattern

import scala.collection.mutable.ArrayBuffer
import org.jacop.scala._

/**
 * 
 * It solves a nonogram example problem, sometimes also called Paint by Numbers.
 * 
 * 
 * @author Radoslaw Szymanek; rewriting to Scala Krzysztof Kuchcinski
 * 
 */

object Nonogram extends jacop {

  /**
   * The value that represents a black dot.
   */
  val black = 1
	
  /**
   * The value that represents a white dot.
   */
  val white = 0

  /**
   * A board to be painted in white/black dots.
   */
  var board : Array[Array[IntVar]] = null

  /**
   * It specifies if the slide based decomposition of the regular constraint
   * should be applied. This decomposition uses ternary extensional support 
   * constraints. It achieves GAC if FSM is deterministic. 
   */
  val slideDecomposition = false

  /**
   * It specifies if the regular constraint should be used.
   */
  val regularConstr = true

  /**
   * It specifies if one extensional constraint based on MDD created from FSM
   * should be used. The translation process works if FSM is deterministic.
   */
  val extensionalMDD = false

  def readFromFile(filename: String) {
		
    var lines = new Array[String](100)

    val dimensions = new Array[Int](2)

    /* read from file args[0] or qcp.txt */
    try {
      
      val in = new BufferedReader(new FileReader(filename))

      var str = in.readLine()

      val pat = Pattern.compile(" ")
      val result = pat.split(str)
			
      var current = 0

      for (j <- 0 until result.length)
	try {
	  val currentNo = result(j).toInt
	  dimensions(current) = currentNo
	  current += 1
	} catch {
	  case ex : Exception =>
	}

      lines = new Array[String](dimensions(0) + dimensions(1))
			
      var n = 0

      str = in.readLine()	
      while (str != null && n < lines.length) {
	lines(n) = str
	n += 1
	str = in.readLine()
      }
      in.close()
    } catch {
      case e : FileNotFoundException => System.err.println("I can not find file " + filename)
      case e : IOException => {
	System.err.println("Something is wrong with file" + filename)
      }
 
      row_rules = new Array[Array[Int]](dimensions(1)) 
      col_rules = new Array[Array[Int]](dimensions(0))

      // Transforms strings into ints
      for (i <- 0 until lines.length) {
			
	val pat = Pattern.compile(" ")
	val result = pat.split(lines(i))

	val sequence = new Array[Int](result.length)
			
	var current = 0
	for (j <- 0 until result.length)
	  try {
	    sequence(current) = result(j).toInt
	    current += 1
	  } catch {
	    case ex : Exception =>
	  }
	if (i < row_rules.length) row_rules(i) = sequence
	else
	  col_rules(i - row_rules.length) = sequence
      }
      
    }
  }
	

  /**
   * It produces and FSM given a sequence representing a rule. e.g. [2, 3]
   * specifies that there are two black dots followed by three black dots.
   * 
   * @param sequence - input parameter
   * @return Finite State Machine used by Regular automaton to enforce proper sequence.
   */
  def createAutomaton(sequence: Array[Int]) : fsm = {

    var result = new fsm

    var currentState = new state
    result.init(currentState)

    currentState -> (white, currentState)
		
    for (i <- 0 until sequence.length) {
      if (sequence(i) != 0) {
	for (j <- 0 until sequence(i)) {
	  // Black transition
 	  val nextState = new state
 	  result += nextState
 	  currentState -> (black, nextState)
 	  currentState = nextState
	}
	// White transitions
	if (i + 1 != sequence.length) {
	  val nextState = new state
	  result += nextState
	  currentState -> (white, nextState)
	  currentState = nextState
	}  
	currentState -> (white, currentState)
      }
    }

    result.addFinalStates( Array(currentState) )

     result

  }

  def model() {

    import org.jacop.constraints.ExtensionalSupportMDD
    import org.jacop.constraints.regular.Regular

    var vars = new ArrayBuffer[IntVar]()

    var values : IntSet = new IntSet
    values = values + white + black
 
    // Specifying the board with allowed values.
    board = Array.tabulate(row_rules.length, col_rules.length)( (i, j) => 
                       new IntVar("board[" + i + "][" + j + "]", values))

    // Zigzag based variable ordering. 
    for (m <- 0 until row_rules.length + col_rules.length - 1) {
      for (j <- 0 until m if j < col_rules.length) {
	val i = m - j
   	if (i < row_rules.length)
   	  vars :+= board(i)(j)
      }
    }		
		
    println("Size " + vars.length)
		
    // Making sure that rows respect the rules.
    for (i <- 0 until row_rules.length) {
			
      val result = createAutomaton(row_rules(i))
			
      if (slideDecomposition)
  	getModel.imposeDecomposition(new Regular(result, board(i).asInstanceOf[Array[org.jacop.core.IntVar]]))
      
      if (regularConstr)
	regular(result, board(i).toList)
			
      if (extensionalMDD)
 	getModel.impose(new ExtensionalSupportMDD(result.transformDirectlyIntoMDD(board(i).asInstanceOf[Array[org.jacop.core.IntVar]])))

    }

    // Making sure that columns respect the rules.
    for (i <- 0 until col_rules.length) {
					
      val result = createAutomaton(col_rules(i))
      val column = Array.tabulate(row_rules.length)( j => board(j)(i))
							
      if (slideDecomposition)
 	getModel.imposeDecomposition(new Regular(result, column.asInstanceOf[Array[org.jacop.core.IntVar]]))

      if (regularConstr)
	regular(result, column.toList)

      if (extensionalMDD)
 	getModel.impose(new ExtensionalSupportMDD(result.transformDirectlyIntoMDD(column.asInstanceOf[Array[org.jacop.core.IntVar]])))
	
    }

    satisfy( search(vars.toList, input_order, indomain_min) )

  }
			
  /**
   * It prints a matrix of variables. All variables must be grounded.
   * @param matrix matrix containing the grounded variables.
   */
  def printMatrix(matrix: Array[Array[IntVar]]) {

        for(i <- 0 until matrix.length) {
            for(j <- 0 until matrix(i).length) {
            	if ( matrix(i)(j).value() == black )
            		print("0")
            	else
            		print(" ")
            }
            println()
        }
    }

  /**
   * It executes the program which solves this simple problem.
   * @param args no arguments are read.
   */
  def main(args : Array[String]) {

    model()
    printMatrix(board)

/*
    for (i <- 0 until 150) {
			
      var no = ""+i
      while (no.length() < 3)
      no = "0" + no;
      
      System.out.println("Problem file data" + no + ".nin");
      readFromFile("/Users/kris/research/JaCoP-3.1/ExamplesJaCoP/nonogramRepository/data" + no + ".nin");
      model();				
    }
*/
  } 

  /**
   * It specifies a rule for each row.
   */

  var row_rules = Array( 
		  Array(0,0,0,0,2,2,3),
		  Array(0,0,4,1,1,1,4),
		  Array(0,0,4,1,2,1,1),
		  Array(4,1,1,1,1,1,1),
		  Array(0,2,1,1,2,3,5),
		  Array(0,1,1,1,1,2,1),
		  Array(0,0,3,1,5,1,2),
		  Array(0,3,2,2,1,2,2),
		  Array(2,1,4,1,1,1,1),
		  Array(0,2,2,1,2,1,2),
		  Array(0,1,1,1,3,2,3),
		  Array(0,0,1,1,2,7,3),
		  Array(0,0,1,2,2,1,5),
		  Array(0,0,3,2,2,1,2),
		  Array(0,0,0,3,2,1,2),
		  Array(0,0,0,0,5,1,2),
		  Array(0,0,0,2,2,1,2),
		  Array(0,0,0,4,2,1,2),
		  Array(0,0,0,6,2,3,2),
		  Array(0,0,0,7,4,3,2),
		  Array(0,0,0,0,7,4,4),
		  Array(0,0,0,0,7,1,4),
		  Array(0,0,0,0,6,1,4),
		  Array(0,0,0,0,4,2,2),
		  Array(0,0,0,0,0,2,1)
	)
	
  /**
   * It specifies a rule for each column.
   */
	 
  var col_rules = Array( 
		   Array(0,0,1,1,2,2),
		   Array(0,0,0,5,5,7),
		   Array(0,0,5,2,2,9),
		   Array(0,0,3,2,3,9),
		   Array(0,1,1,3,2,7),
		   Array(0,0,0,3,1,5),
		   Array(0,7,1,1,1,3),
		   Array(1,2,1,1,2,1),
		   Array(0,0,0,4,2,4),
		   Array(0,0,1,2,2,2),
		   Array(0,0,0,4,6,2),
		   Array(0,0,1,2,2,1),
		   Array(0,0,3,3,2,1),
		   Array(0,0,0,4,1,15),
		   Array(1,1,1,3,1,1),
		   Array(2,1,1,2,2,3),
		   Array(0,0,1,4,4,1),
		   Array(0,0,1,4,3,2),
		   Array(0,0,1,1,2,2),
		   Array(0,7,2,3,1,1),
		   Array(0,2,1,1,1,5),
		   Array(0,0,0,1,2,5),
		   Array(0,0,1,1,1,3),
		   Array(0,0,0,4,2,1),
		   Array(0,0,0,0,0,3)
	)


	
/*  
  var row_rules = Array(
	Array(2),
	Array(2),
	Array(2),
	Array(2),
	Array(12),
	Array(2),
	Array(2),
	Array(2),
	Array(2),
	Array(2),
	Array(2),
	Array(2),
	Array(2),
	Array(2),
	Array(2),
	Array(2),
	Array(14),
	Array(14),
	Array(1,2),
	Array(1,2),
	Array(1,2),
	Array(1,2),
	Array(11,2),
	Array(1,2),
	Array(1,2),
	Array(1,2),
	Array(1,2),
	Array(1,5),
	Array(1,5),
	Array(1,5),
	Array(1,5),
	Array(1,5),
	Array(1,5),
	Array(1,24),
	Array(32),
	Array(26),
	Array(26),
	Array(26),
	Array(3,8,7,2),
	Array(3,7,6,2),
	Array(3,7,6,2),
	Array(3,7,6,2),
	Array(3,8,7,2),
	Array(26),
	Array(34),
	Array(34),
	Array(34),
	Array(34),
	Array(34),
	Array(24),
	Array(5,3,5),
	Array(3,5,3,5),
	Array(2,2,24),
	Array(1,1,24),
	Array(2,29),
	Array(5,24,2),
	Array(3,26,2),
	Array(41,3),
	Array(43,2),
	Array(42,3),
	Array(41,2),
	Array(41,2),
	Array(4,2,2,2,2,5),
	Array(42),
	Array(42),
	Array(42),
	Array(64),
	Array(86),
	Array(83),
	Array(65),
	Array(75),
	Array(71),
	Array(60,10),
	Array(6,53,10),
	Array(6,25,24,10),
	Array(19,17,3,44),
	Array(30,12,40),
	Array(12,19,22),
	Array(9,24,16),
	Array(4,20,8,11),
	Array(5,24,6,2,3),
	Array(38,6,2,6),
	Array(45,8,8),
	Array(52,3),
	Array(51,1),
	Array(51,2),
	Array(50,1),
	Array(50,1),
	Array(50,1),
	Array(34,9,2),
	Array(31,6,7,7,1),
	Array(29,10,6,3,5,1),
	Array(27,8,5,5,3,1),
	Array(25,5,5,4,10,5,2),
	Array(23,3,11,2,3,3,5,1),
	Array(20,3,16,2,8,11,1),
	Array(18,2,8,4,1,9,3,7,2),
	Array(15,4,8,5,4,12,5,9,1),
	Array(11,5,7,8,2,14,5,11,1),
	Array(7,7,6,13,9,15,15));
	
  var col_rules = Array(
	Array(2),
	Array(4),
	Array(8),
	Array(2,13),
	Array(2,17),
	Array(2,18),
	Array(2,19),
	Array(2,19),
	Array(2,19),
	Array(1,2,19),
	Array(2,2,19),
	Array(2,2,19),
	Array(2,2,19),
	Array(2,2,19),
	Array(2,2,19),
	Array(2,2,18),
	Array(2,26,1),
	Array(2,9,17,1),
	Array(2,10,17,1),
	Array(2,10,16,2),
	Array(2,9,17,2),
	Array(2,9,17,2),
	Array(2,3,3,16,3),
	Array(13,16,2),
	Array(13,15,1),
	Array(12,16,2,1),
	Array(12,15,2,1),
	Array(12,15,1,2),
	Array(11,15,2,3),
	Array(11,15,1,3),
	Array(11,14,2,4),
	Array(1,3,20,14,1,3),
	Array(1,1,2,23,13,1,4),
	Array(1,1,1,21,14,2,4),
	Array(1,1,5,2,22,13,3,3,1),
	Array(1,1,5,4,5,13,13,2,3,1),
	Array(1,1,5,2,5,13,12,2,3,1),
	Array(31,1,6,13,12,3,3,2),
	Array(1,15,1,6,13,12,3,2,2),
	Array(1,29,13,12,3,2,3),
	Array(1,5,32,13,3,2,3),
	Array(1,42,13,2,3,3),
	Array(1,29,12,13,2,3,3),
	Array(29,12,14,1,3,3),
	Array(2,17,10,12,4,8,3,2),
	Array(1,2,17,10,12,3,8,4,1),
	Array(1,2,17,10,12,3,2,9,4,1),
	Array(1,2,17,23,3,2,10,3),
	Array(1,2,6,8,22,3,2,11,3),
	Array(1,2,11,19,11,4,2,11,3),
	Array(38,19,11,4,2,13,1),
	Array(38,19,11,25),
	Array(1,2,11,7,10,12,1,1,3),
	Array(1,2,12,8,10,12,1,1,5),
	Array(1,2,17,23,1,1,7),
	Array(1,2,17,24,1,1,7),
	Array(1,2,17,10,13,1,1,8),
	Array(2,17,10,13,1,1,3,5),
	Array(29,13,4,3,4),
	Array(29,14,2,4,4),
	Array(5,19,14,1,2,4),
	Array(29,14,1,1,3),
	Array(44,2,2,2),
	Array(5,20,2,3,1),
	Array(5,5,14,2,2,2),
	Array(5,5,15,3,2,1),
	Array(5,5,15,3,3,1),
	Array(5,5,15,6,1),
	Array(5,15,3,3),
	Array(21,3,3),
	Array(21,3,3),
	Array(22,2,2),
	Array(2,17,2,2),
	Array(2,2,13,3,1),
	Array(1,2,13,2,1),
	Array(2,2,13,2,1),
	Array(2,1,6,5,4),
	Array(1,2,14,4),
	Array(1,14,4),
	Array(14,2),
	Array(14,2),
	Array(14,3),
	Array(14,2),
	Array(14,2),
	Array(15,2),
	Array(15,2),
	Array(15,2),
	Array(5,2,1,1),
	Array(2,1,2,1,1),
	Array(2,1,2,1,1),
	Array(2,1,2,1,1),
	Array(2,1,2,2,1),
	Array(2,1,2,2,1),
	Array(1,2,1,1),
	Array(1,2,1,1),
	Array(2,1,4),
	Array(2,1,4),
	Array(2,2,5),
	Array(2,2,5),
	Array(3));
*/
/*
  var row_rules = Array(
			  Array(3),
			  Array(5),
			  Array(3,1),
			  Array(2,1),
			  Array(3,3,4),
			  Array(2,2,7),
			  Array(6,1,1),
			  Array(4,2,2),
			  Array(1,1),
			  Array(3,1),
			  Array(6),
			  Array(2,7),
			  Array(6,3,1),
			  Array(1,2,2,1,1),
			  Array(4,1,1,3),
			  Array(4,2,2),
			  Array(3,3,1),
			  Array(3,3),
			  Array(3),
			  Array(2,1)
			);

  var col_rules = 
	 Array(
	  Array(2),
	  Array(1,2),
	  Array(2,3),
	  Array(2,3),
	  Array(3,1,1),
	  Array(2,1,1),
	  Array(1,1,1,2,2),
	  Array(1,1,3,1,3),
	  Array(2,6,4),
	  Array(3,3,9,1),
	  Array(5,3,2),
	  Array(3,1,2,2),
	  Array(2,1,7),
	  Array(3,3,2),
	  Array(2,4),
	  Array(2,1,2),
	  Array(2,2,1),
	  Array(2,2),
	  Array(1),
	  Array(1)
	 );
*/

	/*
	public int[][] col_rules = Array( Array(3), Array(1 ,1), Array(1,1), Array(2));
	public int[][] row_rules = Array( Array(4), Array(1,1), Array(2), Array(1));
    */	
	
}
