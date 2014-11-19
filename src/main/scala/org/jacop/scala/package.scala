/**
* Package for defining variables, constraints, global constraints and search methods for [[org.jacop]] constraint solver in Scala.
*/
package org.jacop

//import org.jacop.core._
import org.jacop.constraints._
import org.jacop.constraints.knapsack._
import org.jacop.constraints.regular._
import org.jacop.constraints.binpacking._
import org.jacop.constraints.netflow._
import org.jacop.search._
//import org.jacop.set.core._
import org.jacop.set.constraints._
import org.jacop.set.search._
import org.jacop.floats.core.FloatDomain
import org.jacop.floats.constraints._
import org.jacop.floats.search._

import _root_.scala.reflect._

package object scala {

  val trace = false

  var allSolutions = false

  var printFunctions: Array[() => Unit] = null

  type DFS = DepthFirstSearch[_ <: org.jacop.core.Var]  // DepthFirstSearch[T] forSome { type T <: org.jacop.core.Var }
  var labels: Array[DFS] = null

  var limitOnSolutions: Int = -1

  var timeOutValue: Int = -1

  var recordSolutions = false

  /*
   * private var impModel corresponds to the currently used store/model. 
   * getModel is used in jacop.scala to get the current object Model.
   */
  private var impModel : Model = new Model()	// the current impModel-store
  def getModel = impModel	// returns the current impModel
  def setModel(that : Model) = impModel = that	// sets the current impModel

  implicit class IntVarSeq(val peer: Array[IntVar]) extends AnyVal {
    def apply(index: IntVar) : IntVar = intVarAt(index, peer)
  }

  implicit class IntSeq(val peer: Array[Int]) extends AnyVal {
    def apply(index: IntVar) : IntVar = intAt(index, peer)
  }

  implicit class FloatSeq(val peer: Array[Double]) extends AnyVal {
    def apply(index: IntVar) : FloatVar = floatAt(index, peer)
  }

/**
* Sets precision for floating point solver
*
* @param p precision
*/
  // =============== Precision for floating point solver ===============

  def setPrecision(p: Double) = FloatDomain.setPrecision(p)

  def precision() = FloatDomain.precision()

  // =============== Global constraints ===============

/**
* Wrapper for [[org.jacop.constraints.Alldiff]].
*
* @param x array of variables to be different. 
*/
  def alldifferent(x: Array[IntVar])  {
    val c = new Alldiff( x.asInstanceOf[Array[org.jacop.core.IntVar]] )
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.Alldistinct]].
*
* @param x array of variables to be different. 
*/
  def alldistinct(x: Array[IntVar]) {
    val c = new Alldistinct( x.asInstanceOf[Array[org.jacop.core.IntVar]] )
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.GCC]].
*
* @param x array of variables. 
* @param y array of counters of differnet values from array x. 
*/
  def gcc(x: Array[IntVar], y: Array[IntVar]) {
    val c = new GCC( x.asInstanceOf[Array[org.jacop.core.IntVar]], y.asInstanceOf[Array[org.jacop.core.IntVar]] )
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.Sum]].
*
* @param res array of variables to be summed up. 
* @param result summation result. 
*/
  def sum[T <: org.jacop.core.IntVar](res: List[T], result: IntVar)(implicit m: ClassTag[T])  {
     val c = new Sum(res.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], result)
     if (trace) println(c)
     impModel.impose( c )
   }

/**
* Wrapper for [[org.jacop.constraints.Sum]].
*
* @param res array of variables to be summed up. 
* @return summation result. 
*/
  def sum[T <: org.jacop.core.IntVar](res: List[T])(implicit m: ClassTag[T]) : IntVar = {
    val result = new IntVar()
    val c = new Sum(res.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], result)
    impModel.constr += c
    result
  }

/**
* Wrapper for [[org.jacop.constraints.SumWeight]].
*
* @param res array of variables to be summed up. 
* @param w array of weights. 
* @param result summation result. 
*/
  def weightedSum[T <: org.jacop.core.IntVar](res: List[T], w: Array[Int], result: IntVar)(implicit m: ClassTag[T]) {
    val c = new SumWeight(res.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], w, result)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.SumWeight]].
*
* @param res array of variables to be summed up. 
* @param w array of weights. 
* @return summation result. 
*/
  def sum[T <: org.jacop.core.IntVar](res: List[T], w: Array[Int])(implicit m: ClassTag[T]) : IntVar = {
    val result = new IntVar()
    val c = new SumWeight(res.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], w, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.constraints.SumWeightDom]].
*
* @param res array of variables to be summed up (domain consistency used). 
* @param w array of weights. 
* @param result summation result. 
*/
  def weightedSumDom[T <: org.jacop.core.IntVar](res: List[T], w: Array[Int], result: IntVar)(implicit m: ClassTag[T]) {
    val c = new SumWeightDom(res.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], w, result)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.SumWeightDom]].
*
* @param res array of variables to be summed up. 
* @param w array of weights. 
* @return summation result. 
*/
  def sumDom[T <: org.jacop.core.IntVar](res: List[T], w: Array[Int])(implicit m: ClassTag[T]) : IntVar = {
    val result = new IntVar()
    val c = new SumWeightDom(res.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], w, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.constraints.AbsXeqY]].
*
* @param x variable for abs operation. 
* @return absolute value result. 
*/
  def abs(x: org.jacop.core.IntVar) : IntVar = {
    val result = new IntVar()
    val c = new AbsXeqY(x, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.constraints.Max]].
*
* @param x array of variables where maximum values is to be found. 
* @param mx maxumum value. 
*/
  def max[T <: org.jacop.core.IntVar](x: List[T], mx: org.jacop.core.IntVar)(implicit m: ClassTag[T])  {
    val c = new org.jacop.constraints.Max(x.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], mx)
    if (trace) println(c)
    impModel.impose(c)
  }

/**
* Wrapper for [[org.jacop.constraints.Min]].
*
* @param x array of variables where mnimimum values is to be found. 
* @param mn minimum value.
*/
  def min[T <: org.jacop.core.IntVar](x: List[T], mn: org.jacop.core.IntVar )(implicit m: ClassTag[T]) {
    val c = new org.jacop.constraints.Min(x.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], mn)
    if (trace) println(c)
    impModel.impose(c)
  }

/**
* Wrapper for [[org.jacop.constraints.Max]].
*
* @param x array of variables where maximum values is to be found.
* @return max value. 
*/
  def max[T <: org.jacop.core.IntVar](x: List[T])(implicit m: ClassTag[T]) : IntVar = {
    val result = new IntVar()
    val c = new org.jacop.constraints.Max(x.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], result)
    impModel.constr += c
    result
  }

/**
* Wrapper for [[org.jacop.constraints.Min]].
*
* @param x array of variables where minimum values is to be found.
* @return minimum value. 
*/
  def min[T <: org.jacop.core.IntVar](x: List[T])(implicit m: ClassTag[T]) : IntVar = {
    val result = new IntVar()
    val c = new org.jacop.constraints.Min(x.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], result)
    impModel.constr += c
    result
  }

/**
* Wrapper for [[org.jacop.constraints.Count]].
*
* @param list list of variables to count number of values value. 
* @param count of values value. 
*/
  def count[T <: org.jacop.core.IntVar](list: List[T], count: T, value: Int)(implicit m: ClassTag[T])  {
    val c = new Count(list.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], count, value)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.Count]].
*
* @param list list of variables to count number of values value. 
* @return number of values value. 
*/
  def count[T <: org.jacop.core.IntVar](list: List[T], value: Int)(implicit m: ClassTag[T]) : IntVar = {
    val result = new IntVar()
    val c = new Count(list.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], result, value)
    impModel.constr += c
    println(result) 
    result
  }

/**
* Wrapper for [[org.jacop.constraints.Values]].
*
* @param list list of variables to count number of different values. 
* @param count of different values. 
*/
  def values[T <: org.jacop.core.IntVar](list: List[T], count: IntVar)(implicit m: ClassTag[T])  {
    val c = new Values(list.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], count)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.Values]].
*
* @param list list of variables to count number of different values. 
* @return number of different values. 
*/
  def values[T <: org.jacop.core.IntVar](list: List[T])(implicit m: ClassTag[T]) : IntVar = {
    val result = new IntVar()
    val c = new Values(list.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], result)
    impModel.constr += c
    result
  }

/**
* Wrapper for [[org.jacop.constraints.Element]].
*
* @param index index to select element from list of elements. 
* @param elements array of integers that can be assigned to values. 
* @param value value selected from list of elements. 
*/
  def element(index: org.jacop.core.IntVar, elements: Array[Int], value: org.jacop.core.IntVar)  {
    val c = new Element(index, elements, value)
    if (trace) println(c)
    impModel.impose( c )
  }


/**
* Wrapper for [[org.jacop.constraints.Element]].
*
* @param index index to select element from list of elements. 
* @param elements array of integers that can be assigned to values. 
* @param value value selected from list of elements. 
* @param offset value of index offset (shift). 
*/
  def element(index: org.jacop.core.IntVar, elements: Array[Int], value: org.jacop.core.IntVar, offset: Int)  {
    val c = new Element(index, elements, value, offset)
    if (trace) println(c)
    impModel.impose( c )
  }
 
/**
* Wrapper for [[org.jacop.constraints.Element]].
*
* @param index index to select element from list of elements. 
* @param elements array of varibales that can be assigned to values. 
* @param value value selected from list of elements. 
*/
  def element[T <: org.jacop.core.IntVar](index: org.jacop.core.IntVar, elements: List[T], value: org.jacop.core.IntVar)(implicit m: ClassTag[T])  {
    val c = new Element(index, elements.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], value)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.Element]].
*
* @param index index to select element from list of elements. 
* @param elements array of varibales that can be assigned to values. 
* @param value value selected from list of elements. 
* @param offset value of index offset (shift). 
*/
  def element[T <: org.jacop.core.IntVar](index: org.jacop.core.IntVar, elements: List[T], value: org.jacop.core.IntVar, offset: Int)(implicit m: ClassTag[T])  {
    val c = new Element(index, elements.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], value, offset)
    if (trace) println(c)
    impModel.impose( c )
  }

  /** Wrapper for [[org.jacop.constraints.Element]].
    *
    * @param index    index to select element from list of elements.
    * @param xs       array of integers that can be assigned to values.
    * @param offset   value of index offset (shift).
    * @return         the variable yielding the element at the given index
    */
  def intAt(index: IntVar, xs: Array[Int], offset: Int = 0) : IntVar = {
    val result  = new IntVar()
    val c       = new Element(index, xs, result, offset)
    if (trace) println(c)
    impModel.impose(c)
    result
  }

  def intVarAt(index: IntVar, xs: Array[IntVar], offset: Int = 0) : IntVar = {
    val result  = new IntVar()
    val c       = new Element(index, xs.asInstanceOf[Array[org.jacop.core.IntVar]], result, offset)
    if (trace) println(c)
    impModel.impose(c)
    result
  }

  /** Wrapper for [[org.jacop.floats.constraints.ElementFloat]].
    *
    * @param index    index to select element from list of elements.
    * @param xs       array of integers that can be assigned to values.
    * @param offset   value of index offset (shift).
    * @return         the variable yielding the element at the given index
    */
  def floatAt(index: IntVar, xs: Array[Double], offset: Int = 0) : FloatVar = {
    val result  = new FloatVar()
    val c       = new ElementFloat(index, xs, result, offset)
    if (trace) println(c)
    impModel.impose(c)
    result
  }

/**
* Wrapper for [[org.jacop.constraints.Diff2]].
*
* @param x coordinate X of rectangle. 
* @param y coordinate Y of rectangle. 
* @param lx length in derection X of rectangle. 
* @param ly length in derection Y of rectangle. 
*/
  def diff2(x: Array[IntVar], y: Array[IntVar], lx: Array[IntVar], ly: Array[IntVar])  {
    val c = new Diff(x.asInstanceOf[Array[org.jacop.core.IntVar]], y.asInstanceOf[Array[org.jacop.core.IntVar]],
		     lx.asInstanceOf[Array[org.jacop.core.IntVar]], ly.asInstanceOf[Array[org.jacop.core.IntVar]])
    if (trace) println(c)
    impModel.impose(c)
  }

/**
* Wrapper for [[org.jacop.constraints.Diff2]].
*
* @param rectangles array of four element vectors representing rectnagles [x, y, lx, ly]
*/
  def diff2(rectangles: Array[Array[IntVar]])  {
    val c = new Diff(rectangles.asInstanceOf[Array[Array[org.jacop.core.IntVar]]])
    if (trace) println(c)
    impModel.impose( new Diff(rectangles.asInstanceOf[Array[Array[org.jacop.core.IntVar]]]) )
  }

/**
* Wrapper for [[org.jacop.constraints.Cumulative]].
*
* @param t array of start times of tasks.
* @param d array of duration of tasks.
* @param r array of number of resources of tasks.
* @param limit limit on number of resources used in a schedule.
*/
  def cumulative(t: Array[IntVar], d: Array[IntVar], r: Array[IntVar], limit: IntVar)  {
    val c = new Cumulative(t.asInstanceOf[Array[org.jacop.core.IntVar]],
			   d.asInstanceOf[Array[org.jacop.core.IntVar]],
			   r.asInstanceOf[Array[org.jacop.core.IntVar]], limit)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.Circuit]].
*
* @param n array of varibales, which domains define next nodes in the graph.
*/
  def circuit(n: Array[IntVar])  {
    val c = new Circuit(n.asInstanceOf[Array[org.jacop.core.IntVar]])
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.Assignment]].
*
* @param x array of varibales. 
* @param y array variables that values are permutation of x.
*/
  def assignment(x: Array[IntVar], y: Array[IntVar])  {
    val c = new Assignment(x.asInstanceOf[Array[org.jacop.core.IntVar]], y.asInstanceOf[Array[org.jacop.core.IntVar]])
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.Among]].
*
* @param list array of varibales. 
* @param kSet values to be checked.
* @param n number of values found.
*/
  def among(list: Array[IntVar], kSet: IntSet, n: IntVar) {
    val c = new Among(list.asInstanceOf[Array[org.jacop.core.IntVar]], kSet, n)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.AmongVar]].
*
* @param listX array of varibales. 
* @param listY array of varibales to be checked if their values .
* @param n number of values found.
*/
  def among(listX: Array[IntVar], listY: Array[IntVar], n: IntVar) {
    val c = new AmongVar(listX.asInstanceOf[Array[org.jacop.core.IntVar]], listY.asInstanceOf[Array[org.jacop.core.IntVar]], n)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.ExtensionalSupportVA]].
*
* @param list array of variables. 
* @param tuples array of tuples allowed to be assigned to variables.
*/
  def table[T <: org.jacop.core.IntVar](list: List[T], tuples: Array[Array[Int]])(implicit m: ClassTag[T]) {
    val c = new ExtensionalSupportVA(list.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], tuples)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.constraints.knapsack.Knapsack]].
*
* @param profits array of profite for items. 
* @param weights array of weights for items.
* @param quantity array of quantities of items.
* @param knapsackCapacity knapsack capacity.
* @param knapsackProfit profite when selling items.
*/
  def knapsack(profits: Array[Int], weights: Array[Int], quantity: List[IntVar], 
	       knapsackCapacity: IntVar, knapsackProfit: IntVar ) {
    val c = new Knapsack(profits, weights, quantity.toArray, knapsackCapacity, knapsackProfit)
    if (trace) println(c)
    impModel.impose( c )    
  }

/**
* Wrapper for [[org.jacop.constraints.binpacking.Binpacking]].
*
* @param bin list containing which bin is assigned to an item. 
* @param load list of loads for bins.
* @param w array of weights for items.
*/
  def binpacking(bin: List[IntVar], load: List[IntVar], w: Array[Int]) {
    val c = new Binpacking(bin.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], load.toArray.asInstanceOf[Array[org.jacop.core.IntVar]], w)
    if (trace) println(c)
    impModel.impose( c )    
  }

/**
* Wrapper for [[org.jacop.constraints.regular.Regular]].
*
* @param dfa specification of finite state machine using class fsm. 
* @param vars list of variables assigned to fsm nodes.
*/
  def regular(dfa: fsm, vars: List[IntVar]) {
    val c = new Regular(dfa, vars.toArray)
    if (trace) println(c)
    impModel.impose( c )
  }

  // ================== Decompose constraints

/**
* Wrapper for [[org.jacop.constraints.Sequence]].
*
* @param list list of variables to be constrained. 
* @param set set of values to be checked.
* @param q length of the sub-sequence.
* @param min minimal number of occurrences of values in the sub-sequence.
* @param max maximal number of occurrences of values in the sub-sequence.
*/
  def sequence(list: Array[IntVar], set: IntSet, q: Int, min: Int, max: Int) {
    val c = new Sequence(list.asInstanceOf[Array[org.jacop.core.IntVar]], set, q, min, max)
    if (trace) println(c)
    impModel.imposeDecomposition( c )
}

/**
* Wrapper for [[org.jacop.constraints.Stretch]].
*
* @param values a list of values to be assigned to sub-sequences. 
* @param min minimal length of the sub-sequence for each value on position i.
* @param max maximal length of the sub-sequence for each value on position i.
* @param x list of variables to be constrained.
*/
  def stretch(values: Array[Int], min: Array[Int], max: Array[Int], x: Array[IntVar]) {
    val c = new Stretch(values, min, max, x.asInstanceOf[Array[org.jacop.core.IntVar]])
    if (trace) println(c)
    impModel.imposeDecomposition( c )
}

/**
* Wrapper for [[org.jacop.constraints.Lex]].
*
* @param x array of vectors of varibales to be lexicographically ordered.
*/
  def lex(x: Array[Array[IntVar]]) {
    val c = new org.jacop.constraints.Lex(x.asInstanceOf[Array[Array[org.jacop.core.IntVar]]])
    if (trace) println(c)
    impModel.imposeDecomposition(c)
  }

/**
* Wrapper for [[org.jacop.constraints.SoftAlldifferent]].
*
* @param xVars array of variables to be constrained to be different.
* @param costVar measures degree of violation (uses value based violation).
*/
  def softAlldifferent(xVars: Array[IntVar], costVar: IntVar) {
    val violationMeasure = ViolationMeasure.VALUE_BASED
    val c = new SoftAlldifferent(xVars.asInstanceOf[Array[org.jacop.core.IntVar]], costVar, violationMeasure)
    if (trace) println(c)
    impModel.imposeDecomposition( c )
  }

/**
* Wrapper for [[org.jacop.constraints.SoftGCC]].
*
* @param xVars array of variables to be constrained to be different.
* @param hardLowerBound  lower bound on limits that can not be violated.
* @param hardUpperBound  upper bound on limits that can not be violated
* @param countedValue values that are counted.
* @param softCounters specifies preferred values for counters and can be violated.
*/
  def softGCC(xVars: Array[IntVar], hardLowerBound: Array[Int], hardUpperBound: Array[Int], countedValue: Array[Int], softCounters: Array[IntVar], 
	      costVar: IntVar) {
    val violationMeasure = ViolationMeasure.VALUE_BASED
    val c = new SoftGCC(xVars.asInstanceOf[Array[org.jacop.core.IntVar]], 
			hardLowerBound, 
			hardUpperBound, 
			countedValue, 
			softCounters.asInstanceOf[Array[org.jacop.core.IntVar]],  
			costVar, violationMeasure)
    if (trace) println(c)
    impModel.imposeDecomposition( c )
}

  def network_flow(net: org.jacop.constraints.netflow.NetworkBuilder) {
    val c = new NetworkFlow(net)
    if (trace) println(c)
    impModel.impose( c )
  }

  // ================== Logical operations on constraints


/**
* Wrapper for [[org.jacop.constraints.Or]].
*
* @param list constraints to be disjunction.
* @return the constraint that is a a disjunction of constraints.
*/
  def OR(list: PrimitiveConstraint*)  : PrimitiveConstraint = {
    val c = new Or(list.toArray)
    list.foreach( e => impModel.constr.remove(impModel.constr.indexOf(e)) )
    impModel.constr += c
    c
  }

/**
* Wrapper for [[org.jacop.constraints.Or]].
*
* @param list constraints to be disjunction.
* @return the constraint that is a a disjunction of constraints.
*/
  def OR(list: List[PrimitiveConstraint])  : PrimitiveConstraint = {
    val c = new Or(list.toArray)
    list.foreach( e => impModel.constr.remove(impModel.constr.indexOf(e)) )
    impModel.constr += c
    c
  }

/**
* Wrapper for [[org.jacop.constraints.And]].
*
* @param list constraints to be conjunction.
* @return the constraint that is a a conjunction of constraints.
*/
  def AND(list: PrimitiveConstraint*) : PrimitiveConstraint = {
    val c = new And(list.toArray)
    list.foreach( e => impModel.constr.remove(impModel.constr.indexOf(e)) )
    impModel.constr += c
    c
  }

/**
* Wrapper for [[org.jacop.constraints.And]].
*
* @param list constraints to be conjunction.
* @return the constraint that is a a conjunction of constraints.
*/
  def AND(list: List[PrimitiveConstraint]) : PrimitiveConstraint = {
    val c = new And(list.toArray)
    list.foreach( e => impModel.constr.remove(impModel.constr.indexOf(e)) )
    impModel.constr += c
    c
  }

/**
* Wrapper for [[org.jacop.constraints.Not]].
*
* @param constr constraints to be negated.
* @return the negated constraint.
*/
  def NOT(constr: PrimitiveConstraint) : PrimitiveConstraint = {
    val c = new Not(constr)
    impModel.constr.remove(impModel.constr.indexOf(constr))
    impModel.constr += c
    c
  }

  // =============== Set constraints ===============


/**
* Wrapper for [[org.jacop.set.constraints.CardAeqX]].
*
* @param s constrained set variable.
* @return variable defining cardinality of s.
*/
  def card(s: SetVar) : IntVar = {
    val result = new IntVar()
    val c = new CardAeqX(s, result)
    impModel.constr += c
    result
  }

/**
* Wrapper for [[org.jacop.set.constraints.CardA]].
*
* @param s constrained set variable.
* @param n cardinality.
*/
  def card(s: SetVar, n: Int)  {
    val c = new CardA(s, n)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.set.constraints.CardAeqX]].
*
* @param s constrained set variable.
* @param n cardinality (IntVar variable).
*/
  def card(s: SetVar, n: org.jacop.core.IntVar)  {
    val c = new CardAeqX(s, n)
    if (trace) println(c)
    impModel.impose( c )
  }

/**
* Wrapper for [[org.jacop.set.constraints.Match]].
*
* @param a  a set variable to be matched against list of IntVar.
* @param list varibales that get values from the set.
*/
  def matching[T <: org.jacop.core.IntVar](a: SetVar, list: List[T])(implicit m: ClassTag[T]) {
    val c = new Match(a, list.toArray)
    if (trace) println(c)
    impModel.impose( c )
  }

  // =============== Floating point constraints ===================

/**
* Wrapper for [[org.jacop.floats.constraints.AbsPeqR]].
*
* @param a FloatVar variable.
* @return absolute value of the variable.
*/
  def abs(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new AbsPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.ExpPeqR]].
*
* @param a FloatVar variable.
* @return value of exponential function the variable.
*/
  def exp(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new ExpPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.LnPeqR]].
*
* @param a FloatVar variable.
* @return value of natural logarithm function the variable.
*/
  def ln(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new LnPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.SqrtPeqR]].
*
* @param a FloatVar variable.
* @return value of square root function the variable.
*/
  def sqrt(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new SqrtPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.SinPeqR]].
*
* @param a FloatVar variable.
* @return value of sinus function the variable.
*/
  def sin(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new SinPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.AsinPeqR]].
*
* @param a FloatVar variable.
* @return value of asinus function the variable.
*/
  def asin(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new AsinPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.CosPeqR]].
*
* @param a FloatVar variable.
* @return value of cosinus function the variable.
*/
  def cos(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new CosPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.AcosPeqR]].
*
* @param a FloatVar variable.
* @return value of acosinus function the variable.
*/
  def acos(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new AcosPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.TanPeqR]].
*
* @param a FloatVar variable.
* @return value of tangent function the variable.
*/
  def tan(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new TanPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.AtanPeqR]].
*
* @param a FloatVar variable.
* @return value of atangent function the variable.
*/
  def atan(a: org.jacop.floats.core.FloatVar) : FloatVar = {
    val result = new FloatVar()
    val c = new AtanPeqR(a, result)
    if (trace) println(c)
    impModel.impose( c )
    result
  }

/**
* Wrapper for [[org.jacop.floats.constraints.LinearFloat]].
*
* @param res array of variables to be summed up. 
* @return summation result. 
*/
 def sum[T <: org.jacop.floats.core.FloatVar](res: List[T])(implicit m: Manifest[T]) : FloatVar = {
   val result = new FloatVar()
   val vect = new Array[org.jacop.floats.core.FloatVar](res.length + 1)
   val w = new Array[Double](res.length + 1)

   for ( i <- 0 to (res.length - 1)) {
     vect(i) = res(i).asInstanceOf[org.jacop.floats.core.FloatVar]
     w(i) = 1.0
   }
   vect(res.length) = result.asInstanceOf[org.jacop.floats.core.FloatVar]
   w(res.length) = -1.0
   val c = new LinearFloat(impModel, vect, w, "==", 0.0)
    if (trace) println(c)
   impModel.constr += c
   result
 }

/**
* Wrapper for [[org.jacop.floats.constraints.LinearFloat]].
*
* @param res array of variables to be summed up. 
* @return summation result. 
*/
 def linear[T <: org.jacop.floats.core.FloatVar](res: List[T], weight: Array[Double])(implicit m: Manifest[T]) : FloatVar = {
   val result = new FloatVar()
   val vect = new Array[org.jacop.floats.core.FloatVar](res.length + 1)
   val w = new Array[Double](res.length + 1)

   for ( i <- 0 to (res.length - 1)) {
     vect(i) = res(i).asInstanceOf[org.jacop.floats.core.FloatVar]
     w(i) = weight(i)
   }
   vect(res.length) = result.asInstanceOf[org.jacop.floats.core.FloatVar]
   w(res.length) = -1.0
   val c = new LinearFloat(impModel, vect, w, "==", 0.0)
    if (trace) println(c)
   impModel.constr += c
   result
 }

/**
* Wrapper for [[org.jacop.floats.constraints.LinearFloat]].
*
* @param res array of variables to be summed up. 
* @return summation result. 
*/
 def linear[T <: org.jacop.floats.core.FloatVar](res: List[T], weight: Array[Double], result: Double)(implicit m: Manifest[T]) {

   val c = new LinearFloat(impModel, res.asInstanceOf[Array[org.jacop.floats.core.FloatVar]], weight, "==", result)
    if (trace) println(c)
   impModel.constr += c
 }

  // =============== Search methods ===================

/**
* Minimization search method.
*
* @param select select method defining variable selection and value assignment methods.
* @param cost Cost variable
* @return true if solution found and false otherwise.
*/
   def minimize[T <: org.jacop.core.Var](select: SelectChoicePoint[T], cost: IntVar, printSolutions: (() => Unit)*)(implicit m: ClassTag[T]): Boolean = {

     impModel.imposeAllConstraints()

     val label = dfs
     labels = Array(label)

     printFunctions = new Array(printSolutions.size)
     if (printSolutions.size > 0) {
       var i=0
       for (p <- printSolutions) {
	 printFunctions(i) = p
	 i += 1
       }
    
       //label.setSolutionListener(new EmptyListener[T]);
       label.setPrintInfo(false)
       label.setSolutionListener(new ScalaSolutionListener[T])
     }

    if (timeOutValue > 0)
      label.setTimeOut(timeOutValue)

     if (limitOnSolutions > 0) {
       label.getSolutionListener().setSolutionLimit(limitOnSolutions)
       label.respectSolutionListenerAdvice=true
     }

     label.labeling(impModel, select, cost)
   }

/**
* Minimization search method.
*
* @param select select method defining variable selection and value assignment methods.
* @param cost Cost variable
* @return true if solution found and false otherwise.
*/
   def minimize[T <: org.jacop.core.Var](select: SelectChoicePoint[T], cost: FloatVar, printSolutions: (() => Unit)*)(implicit m: ClassTag[T]): Boolean = {

     impModel.imposeAllConstraints()

     val label = dfs
     labels = Array(label)

     printFunctions = new Array(printSolutions.size)
     if (printSolutions.size > 0) {
       var i=0
       for (p <- printSolutions) {
	 printFunctions(i) = p
	 i += 1
       }
    
       //label.setSolutionListener(new EmptyListener[T]);
       label.setPrintInfo(false)
       label.setSolutionListener(new ScalaSolutionListener[T])
     }

    if (timeOutValue > 0)
      label.setTimeOut(timeOutValue)

     if (limitOnSolutions > 0) {
       label.getSolutionListener().setSolutionLimit(limitOnSolutions)
       label.respectSolutionListenerAdvice=true
     }

     label.labeling(impModel, select, cost)
   }

/**
* Maximization search method.
*
* @param select select method defining variable selection and value assignment methods.
* @param cost Cost variable
* @return true if solution found and false otherwise.
*/
  def maximize[T <: org.jacop.core.Var](select: SelectChoicePoint[T], cost: IntVar, printSolutions: (() => Unit)*)(implicit m: ClassTag[T]): Boolean = {

    val costN = new IntVar("newCost", org.jacop.core.IntDomain.MinInt, org.jacop.core.IntDomain.MaxInt)
    costN #= -cost

    minimize(select, costN, printSolutions: _*)
  }


/**
* Maximization search method.
*
* @param select select method defining variable selection and value assignment methods.
* @param cost Cost variable
* @return true if solution found and false otherwise.
*/
  def maximize[T <: org.jacop.core.Var](select: SelectChoicePoint[T], cost: FloatVar, printSolutions: (() => Unit)*)(implicit m: ClassTag[T]): Boolean = {

    val costN = new FloatVar("newCost", org.jacop.core.IntDomain.MinInt, org.jacop.core.IntDomain.MaxInt)
    costN #= -cost

    minimize(select, costN, printSolutions: _*)
  }

/**
* Search method that finds a solution.
*
* @param select select method defining variable selection and value assignment methods.
* @return true if solution found and false otherwise.
*/

  def satisfy[T <: org.jacop.core.Var](select: SelectChoicePoint[T], printSolutions: (() => Unit)*)(implicit m: ClassTag[T]): Boolean = {

    impModel.imposeAllConstraints()

    val label = dfs
    labels = Array(label)

    printFunctions = new Array(printSolutions.size)
    if (printSolutions.size > 0) {
      var i=0
      for (p <- printSolutions) {
	printFunctions(i) = p
	i += 1
      }
    
      // label.setSolutionListener(new EmptyListener[T]);
      label.setPrintInfo(false)
      label.setSolutionListener(new ScalaSolutionListener[T])
    }

    if (timeOutValue > 0)
      label.setTimeOut(timeOutValue)

    if (allSolutions)
      label.getSolutionListener().searchAll(true)

     if (limitOnSolutions > 0) 
       label.getSolutionListener().setSolutionLimit(limitOnSolutions)
    
    label.getSolutionListener().recordSolutions(recordSolutions)

    label.labeling(impModel, select)

  }

/**
* Search method that finds all solutions.
*
* @param select select method defining variable selection and value assignment methods.
* @return true if solution found and false otherwise.
*/
  def satisfyAll[T <: org.jacop.core.Var](select: SelectChoicePoint[T], printSolutions: (() => Unit)*)(implicit m: ClassTag[T]): Boolean = {

    allSolutions = true

    satisfy( select, printSolutions: _*)

  }


/**
* Minimization method for sequence of search methods (specified by list of select methods).
*
* @param select list of select methods defining variable selection and value assignment methods for sequence of searchs.
* @param cost Cost variable
* @return true if solution found and false otherwise.
*/
  def minimize_seq[T <: org.jacop.core.Var](select: List[SelectChoicePoint[T]], cost: IntVar, printSolutions: (() => Unit)*) (implicit m: ClassTag[T]): Boolean = {

    impModel.imposeAllConstraints()

    val masterLabel = dfs
    labels = new Array(select.size)
    labels(0) = masterLabel

    if (printSolutions.size > 0) {
      //masterLabel.setSolutionListener(new EmptyListener[T]);
      masterLabel.setPrintInfo(false)
    }

    if (limitOnSolutions > 0) 
      masterLabel.respectSolutionListenerAdvice=true

    if (timeOutValue > 0)
      masterLabel.setTimeOut(timeOutValue)

    var previousSearch = masterLabel
    var lastLabel = masterLabel
    if (select.length > 1)
      for (i <- 1 until select.length) {
       	val label = dfs
	previousSearch.addChildSearch(label)
	label.setSelectChoicePoint(select(i))
	previousSearch = label
	lastLabel = label
	labels(i) = label

	if (printSolutions.size > 0) {
	  //label.setSolutionListener(new EmptyListener[T]);
    label.setPrintInfo(false)
	}

	if (limitOnSolutions > 0) 
	  label.respectSolutionListenerAdvice=true

	if (timeOutValue > 0)
	  label.setTimeOut(timeOutValue)
      }

    printFunctions = new Array(printSolutions.size)
    if (printSolutions.size > 0) {
      var i=0
      for (p <- printSolutions) {
	printFunctions(i) = p
	i += 1
      }

      lastLabel.setPrintInfo(false)
      lastLabel.setSolutionListener(new ScalaSolutionListener[T])

      if (limitOnSolutions > 0) {
	lastLabel.getSolutionListener().setSolutionLimit(limitOnSolutions)
	lastLabel.respectSolutionListenerAdvice=true
      }
    }

    masterLabel.labeling(impModel, select(0), cost)
  }
  
/**
* Maximization method for sequence of search methods (specified by list of select methods).
*
* @param select list of select methods defining variable selection and value assignment methods for sequence of searchs.
* @param cost Cost variable
* @return true if solution found and false otherwise.
*/
  def maximize_seq[T <: org.jacop.core.Var](select: List[SelectChoicePoint[T]], cost: IntVar, printSolutions: (() => Unit)*)(implicit m: ClassTag[T]): Boolean = {

    val costN = new IntVar("newCost", org.jacop.core.IntDomain.MinInt, org.jacop.core.IntDomain.MaxInt)
    costN #= -cost

    minimize_seq(select, costN, printSolutions: _*)
  }


/**
* Search method for finding a solution using a sequence of search methods (specified by list of select methods).
*
* @param select list of select methods defining variable selection and value assignment methods for sequence of searchs.
* @return true if solution found and false otherwise.
*/
  def satisfy_seq[T <: org.jacop.core.Var](select: List[SelectChoicePoint[T]], printSolutions: (() => Unit)*)(implicit m: ClassTag[T]): Boolean = {

    impModel.imposeAllConstraints()

    val masterLabel = dfs
    labels = new Array(select.size)
    labels(0) = masterLabel

    if (printSolutions.size > 0) {
      //masterLabel.setSolutionListener(new EmptyListener[T]);
      masterLabel.setPrintInfo(false)
    }    

    if (timeOutValue > 0)
      masterLabel.setTimeOut(timeOutValue)

    if (allSolutions)
      masterLabel.getSolutionListener().searchAll(true)

    masterLabel.getSolutionListener().recordSolutions(recordSolutions)

    var previousSearch = masterLabel
    var lastLabel = masterLabel
    if (select.length > 1)
      for (i <- 1 until select.length) {
       	val label = dfs
	previousSearch.addChildSearch(label)
	label.setSelectChoicePoint(select(i))
	previousSearch = label
	lastLabel = label
	labels(i) = label

	if (printSolutions.size > 0) {
	  //label.setSolutionListener(new EmptyListener[T]);
    label.setPrintInfo(false)
	}

	if (timeOutValue > 0)
	  label.setTimeOut(timeOutValue)

	if (allSolutions)
	  label.getSolutionListener().searchAll(true)

	label.getSolutionListener().recordSolutions(recordSolutions)
      }

    printFunctions = new Array(printSolutions.size)
    if (printSolutions.size > 0) {
      var i=0
      for (p <- printSolutions) {
      	printFunctions(i) = p
      	i += 1
      }
    
      lastLabel.setPrintInfo(false)
      lastLabel.setSolutionListener(new ScalaSolutionListener[T]);

      if (limitOnSolutions > 0) 
	lastLabel.getSolutionListener().setSolutionLimit(limitOnSolutions)
    }

    lastLabel.getSolutionListener().recordSolutions(recordSolutions)

    masterLabel.labeling(impModel, select(0))
  }

/**
* Search method for finding all solutions using a sequence of search methods (specified by list of select methods).
*
* @param select list of select methods defining variable selection and value assignment methods for sequence of searchs.
* @return true if solution found and false otherwise.
*/
  def satisfyAll_seq[T <: org.jacop.core.Var](select: List[SelectChoicePoint[T]], printSolutions: (() => Unit)*)(implicit m: ClassTag[T]): Boolean = {

    allSolutions = true

    satisfy_seq( select, printSolutions: _* )

  }

/**
* Depth first search method.
*
* @return standard depth first search.
*/
  def dfs[T <: org.jacop.core.Var](implicit m: ClassTag[T]) : DepthFirstSearch[T] = {
    val label = new DepthFirstSearch[T]

    label.setAssignSolution(true)
    label.setSolutionListener(new PrintOutListener[T]())
    if (allSolutions)
      label.getSolutionListener().searchAll(true)

    label

  }

/**
* Defines list of variables, their selection method for search and value selection
*
* @return select method for search.
*/
  def search[T <: org.jacop.core.Var](vars: List[T], heuristic: ComparatorVariable[T], indom: Indomain[T])(implicit m: ClassTag[T]) : SelectChoicePoint[T] = {
    new SimpleSelect[T](vars.toArray, heuristic, indom)    
  }

/**
* Defines list of variables, their selection method for sequential search and value selection
*
* @return select method for search.
*/
  def search_vector[T <: org.jacop.core.Var](vars: List[List[T]], heuristic: ComparatorVariable[T], indom: Indomain[T])(implicit m: ClassTag[T]) : SelectChoicePoint[T] = {

    val varsArray = new Array[Array[T]](vars.length)
    for (i <- 0 until vars.length)
      varsArray(i) = vars(i).toArray

    new SimpleMatrixSelect[T](varsArray, heuristic, indom)    
  }

/**
* Defines list of variables, their selection method for split search and value selection
*
* @return select method for search.
*/
  def search_split[T <: org.jacop.core.IntVar](vars: List[T], heuristic: ComparatorVariable[T])(implicit m: ClassTag[T]) : SelectChoicePoint[T] = {
    new SplitSelect[T](vars.toArray, heuristic, new IndomainMiddle[T]())
  }

/**
* Defines list of variables, their selection method for split search and value selection
*
* @return select method for search.
*/
  def search_float[T <: org.jacop.floats.core.FloatVar](vars: List[T], heuristic: ComparatorVariable[T])(implicit m: ClassTag[T]) : SelectChoicePoint[T] = {
    new SplitSelectFloat[T](impModel, vars.toArray, heuristic)
  }


/**
* Defines functions that prints search statistics
* 
*/
  def statistics() {
    var nodes=0
    var decisions=0
    var wrong=0
    var backtracks=0
    var depth=0
    var solutions=0

    if (labels != null)
      for ( label <- labels) {
        nodes += label.getNodes()
        decisions += label.getDecisions()
        wrong += label.getWrongDecisions()
        backtracks += label.getBacktracks()
        depth += label.getMaximumDepth()
        solutions = label.getSolutionListener().solutionsNo()
      }
    println("\nSearch statistics:\n=================="+
	    "\nSearch nodes : "+nodes+
	    "\nSearch decisions : "+decisions+
	    "\nWrong search decisions : "+wrong+
	    "\nSearch backtracks : "+backtracks+
	    "\nMax search depth : "+depth+
	    "\nNumber solutions : "+ solutions 
	  )
  }


/**
* Defines functions that prints search statistics
*
* @param n number of solutions to be explored.
*/
  def numberSolutions(n: Int) = limitOnSolutions = n

/**
* Defines functions that prints search statistics
*
* @param t value of time-out in seconds.
*/
  def timeOut(t: Int) = timeOutValue = t


/**
* Defines null variable selection method that is interpreted by org.jacop as input order.
*
* @return related variable selection method.
*/
  def input_order[T <: org.jacop.core.Var] : ComparatorVariable[T] = null

  // ===============  IntVar & BoolVar specific

/**
* Wrapper for [[org.jacop.search.SmallestDomain]].
*
* @return related variable selection method.
*/
  def first_fail[T <: org.jacop.core.IntVar] : ComparatorVariable[T] = new SmallestDomain[T]

/**
* Wrapper for [[org.jacop.search.MostConstrainedStatic]].
*
* @return related variable selection method.
*/
  def most_constrained[T <: org.jacop.core.IntVar] : ComparatorVariable[T] = new MostConstrainedStatic[T]

/**
* Wrapper for [[org.jacop.search.SmallestMin]].
*
* @return related variable selection method.
*/
  def smallest_min[T <: org.jacop.core.IntVar] : ComparatorVariable[T] = new SmallestMin[T]

/**
* Wrapper for [[org.jacop.search.LargestDomain]].
*
* @return related variable selection method.
*/
  def anti_first_fail[T <: org.jacop.core.IntVar] : ComparatorVariable[T] = new LargestDomain[T]

/**
* Wrapper for [[org.jacop.search.SmallestMin]].
*
* @return related variable selection method.
*/
  def smallest[T <: org.jacop.core.IntVar] : ComparatorVariable[T] = new SmallestMin[T]

/**
* Wrapper for [[org.jacop.search.LargestMax]].
*
* @return related variable selection method.
*/
  def largest[T <: org.jacop.core.IntVar] : ComparatorVariable[T] = new LargestMax[T]

/**
* Wrapper for [[org.jacop.search.MaxRegret]].
*
* @return related variable selection method.
*/
  def max_regret[T <: org.jacop.core.IntVar] : ComparatorVariable[T] = new MaxRegret[T]


/**
* Wrapper for [[org.jacop.search.IndomainMin]].
*
* @return related variable selection method.
*/
  def indomain_min[T <: org.jacop.core.IntVar] : Indomain[T] = new IndomainMin[T]

/**
* Wrapper for [[org.jacop.search.IndomainMax]].
*
* @return related variable selection method.
*/
  def indomain_max[T <: org.jacop.core.IntVar] : Indomain[T] = new IndomainMax[T]

/**
* Wrapper for [[org.jacop.search.IndomainMiddle]].
*
* @return related variable selection method.
*/
  def indomain_middle[T <: org.jacop.core.IntVar] : Indomain[T] = new IndomainMiddle[T]

/**
* Wrapper for [[org.jacop.search.IndomainMedian]].
*
* @return related variable selection method.
*/
  def indomain_median[T <: org.jacop.core.IntVar] : Indomain[T] = new IndomainMedian[T]

/**
* Wrapper for [[org.jacop.search.IndomainRandom]].
*
* @return related variable selection method.
*/
  def indomain_random[T <: org.jacop.core.IntVar] : Indomain[T] = new IndomainRandom[T]

  // ============= Set specific

/**
* Wrapper for [[org.jacop.set.search.MinCardDiff]].
*
* @return related variable selection method.
*/
  def first_fail_set[T <: org.jacop.set.core.SetVar] : ComparatorVariable[T] = new MinCardDiff[T]

/**
* Wrapper for [[org.jacop.search.MostConstrainedStatic]].
*
* @return related variable selection method.
*/
  def most_constrained_set[T <: org.jacop.set.core.SetVar] : ComparatorVariable[T] = new MostConstrainedStatic[T]

/**
* Currently equivalent to min_glb_card.
*
* @return related variable selection method.
*/
  def smallest_set[T <: org.jacop.set.core.SetVar] : ComparatorVariable[T] = min_glb_card

/**
* Wrapper for [[org.jacop.set.search.MinGlbCard]].
*
* @return related variable selection method.
*/
  def min_glb_card[T <: org.jacop.set.core.SetVar] : ComparatorVariable[T] = new MinGlbCard[T]

/**
* Wrapper for [[org.jacop.set.search.MinLubCard]].
*
* @return related variable selection method.
*/
  def min_lub_card[T <: org.jacop.set.core.SetVar] : ComparatorVariable[T] = new MinLubCard[T]

/**
* Wrapper for [[org.jacop.set.search.MaxCardDiff]].
*
* @return related variable selection method.
*/
  def anti_first_fail_set[T <: org.jacop.set.core.SetVar] : ComparatorVariable[T] = new MaxCardDiff[T]


/**
* Wrapper for [[org.jacop.set.search.IndomainSetMin]].
*
* @return related indomain method.
*/
  def indomain_min_set[T <: org.jacop.set.core.SetVar] : Indomain[T] = new IndomainSetMin[T]

/**
* Wrapper for [[org.jacop.set.search.IndomainSetMax]].
*
* @return related indomain method.
*/
  def indomain_max_set[T <: org.jacop.set.core.SetVar] : Indomain[T] = new IndomainSetMax[T]

/**
* Wrapper for [[org.jacop.set.search.IndomainSetRandom]].
*
* @return related indomain method.
*/
  def indomain_random_set[T <: org.jacop.set.core.SetVar] : Indomain[T] = new IndomainSetRandom[T]
}
