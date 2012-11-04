/**
* Package for defining variables, constraints, global constraints and search methods for [[JaCoP]] constraint solver in Scala.
*/
package org.jacop.scala

import org.jacop.constraints._
import org.jacop.set.constraints._

/**
* Manages all variables, constraints and global constraints for [[JaCoP]] constraint solver.
* Keeps also labels for search.
*/
object Model extends org.jacop.core.Store {

  var n = 0

  import scala.collection.mutable.ListBuffer

  val constr = new ListBuffer[Constraint]

  def imposeAllConstraints() {
    Model.constr.foreach(e => Model.impose(e))
    if (trace) 
      Model.constr.foreach(println _)
    Model.constr.clear()
  }
}

/**
* Implicit conversions of Int and Bool to IntVar and BoolVar. Used in overloaded operators.
*/
trait jacop {
/**
 * Converts integer to IntVar.
 *
 * @param i intger to be converted.
 */
  implicit def intToIntVar(i: Int): IntVar = {
    val v = new IntVar(i, i)
    v
  }

/**
 * Converts integer to BoolVar.
 *
 * @param i intger to be converted.
 */
  implicit def boolToBoolVar(b: Boolean): BoolVar = {
    val i = if (b) 1 else 0
    val v = new BoolVar(i, i)
    v
  }

/**
 * Converts Array to List, if needed.
 *
 * @param a array to be converted.
 */
  implicit def arrayToList[A](a: Array[A]) = a.toList

  implicit def makeReifiable[T <: PrimitiveConstraint](reifC: T): Reifier[T] = new Reifier(reifC)
}

/**
 * Defines an ordered set of integers and basic operations on these sets.
 *
 * @constructor Create a new ordered empty set of integers.
 * @param min minimal value of a set interval.
 * @param max maximal value of a set interval.
 */
class IntSet extends org.jacop.core.IntervalDomain {

/**
 * Defines an ordered set of integers and basic operations on these sets.
 *
 * @constructor Create a new ordered set of integers.
 * @param min minimal value of a set interval.
 * @param max maximal value of a set interval.
 */
  def this(min: Int, max: Int) {
    this()
    addDom(new org.jacop.core.IntervalDomain(min, max))
  }

/**
 * Defines an ordered set of integers and basic operations on these sets.
 *
 * @constructor Create a new ordered set containing one element.
 * @param el element of set.
 */
  def this(el: Int) {
    this()
    addDom(new org.jacop.core.IntervalDomain(el, el))
  }

/**
 * Set union operation on a set and a set with one value.
 *
 * @param n element of set.
 */
  def + (n: Int) : IntSet =  {
    val tmp = new IntSet
    tmp.unionAdapt(this)
    tmp.unionAdapt(n)
    return tmp
  }

/**
 * Set union operation on two sets.
 *
 * @param that set variable.
 */
  def + (that: IntSet) : IntSet =  {
    val tmp = new IntSet
    tmp.unionAdapt(this)
    tmp.unionAdapt(that)
    return tmp
  }

/**
 * Set intersection operation on a set and a set with one value.
 *
 * @param n element of set.
 */
  def * (n: Int) : IntSet =  {
    val tmp = new IntSet
    tmp.unionAdapt(this)
    tmp.intersectAdapt(n,n)
    return tmp
  }

/**
 * Set intersection operation on two sets.
 *
 * @param that set variable.
 */
  def * (that: IntSet) : IntSet =  {
    val tmp = new IntSet
    tmp.unionAdapt(this)
    tmp.intersectAdapt(that)
    return tmp
  }

/**
 * Set subtraction constraint on a set variable and a set of one value.
 *
 * @param n element of set.
 */
  def \ (n: Int) : IntSet =  {
    val tmp = new IntSet
    tmp.unionAdapt(this)
    tmp.subtractAdapt(n)
    return tmp
  }

/**
 * Set subtraction  operation on a set and a set with one value.
 *
 * @param n element of set.
 */
  def \ (that: IntSet) : IntSet =  {
    val tmp = new IntSet
    tmp.unionAdapt(this)
    for (i <- 0 until that.size) {
      tmp.subtractAdapt(that.intervals(i).min, that.intervals(i).max)
    }
    return tmp
  }

/**
 * Set complement operation on a set.
 *
 */
  def unary_~ : IntSet =  {
    val tmp = new IntSet(org.jacop.core.IntDomain.MinInt, org.jacop.core.IntDomain.MaxInt)
    for (i <- 0 until this.size)
      tmp.subtractAdapt(intervals(i).min, intervals(i).max)
    return tmp
  }

/**
 * Produces string representation of a set.
 *
 */
  override def toString : String = {
    val s = if (singleton) "{" + value +"}" else super.toString
    return s
  }
}

/**
 * Defines a finite domain integer variable and its primitive constraints.
 *
 * @constructor Creates a new finite domain integer variable.
 * @param name variable identifier.
 * @param min minimal value of variable's domain.
 * @param max maximal value of variable's domain.
 */
class IntVar(name: String, min: Int, max: Int) extends org.jacop.core.IntVar(Model, name, min, max) with jacop {

/**
 * Defines an anonymous finite domain integer variable.
 *
 * @constructor Creates a new finite domain integer variable.
 * @param min minimal value of variable's domain.
 * @param max maximal value of variable's domain.
 */
  def this(min: Int, max: Int) = {
    this ("_$" + Model.n, min, max)
    Model.n += 1
  }

/**
 * Defines an anonymous finite domain integer variable.
 *
 * @constructor Creates a new finite domain integer variable with minimal and maximal
 * values in the domain defined by org.jacop.
 * @param name variable's identifier.
 */
  def this(name: String) = {
    this (name, org.jacop.core.IntDomain.MinInt, org.jacop.core.IntDomain.MaxInt)
    Model.n += 1
  }

/**
 * Defines an anonymous finite domain integer variable.
 *
 * @constructor Creates a new finite domain integer variable with minimal and maximal
 * values in the domain defined by org.jacop.
 */
  def this() = {
    this (org.jacop.core.IntDomain.MinInt, org.jacop.core.IntDomain.MaxInt)
    Model.n += 1
  }

/**
 * Defines a finite domain integer variable.
 *
 * @constructor Create a new finite domain integer variable with the domain defined by IntSet.
 * @param dom variable's domain defined as a set of integers (IntSet).
 */
  def this(dom: IntSet) = {
    this ()
    this.dom.intersectAdapt(dom)
    Model.n += 1
  }

/**
 * Defines a finite domain integer variable.
 *
 * @constructor Create a new finite domain integer variable with the domain
 * defined by IntSet.
 * @param name variable's identifier.
 * @param dom variable's domain defined as a set of integers (IntSet).
 */
  def this(name:String, dom: IntSet) = {
    this (name)
    this.dom.intersectAdapt(dom)
    Model.n += 1
  }

/**
 * Defines add constraint between two IntVar.
 *
 * @param that a second parameter for the addition constraint.
 * @return IntVar variable being the result of the addition constraint. 
 */
   def +(that: org.jacop.core.IntVar) = {
     val result = new IntVar()
     val c = new XplusYeqZ(this, that, result)
     Model.constr += c
     result
   }

/**
 * Defines add constraint between IntVar and an integer value.
 *
 * @param that a second integer parameter for the addition constraint.
 * @return IntVar variable being the result of the addition constraint. 
 */
  def +(that: Int) = {
    val result = new IntVar()
    val c = new XplusCeqZ(this, that, result)
    Model.constr += c
    result
  }

/**
 * Defines subtract constraint between two IntVar.
 *
 * @param that a second parameter for the subtraction constraint.
 * @return IntVar variable being the result of the subtraction constraint. 
 */
  def -(that: org.jacop.core.IntVar) = {
    val result = new IntVar()
    val c = new XplusYeqZ(result, that, this)
    Model.constr += c
    result
  }

/**
 * Defines subtract constraint between IntVar and an integer value.
 *
 * @param that a second integer parameter for the subtraction constraint.
 * @return IntVar variable being the result of the subtraction constraint. 
 */
  def -(that: Int) = {
    val result = new IntVar()
    val c = new XplusCeqZ(result, that, this)
    Model.constr += c
    result
  }

/**
 * Defines multiplication constraint between two IntVar.
 *
 * @param that a second parameter for the multiplication constraint.
 * @return IntVar variable being the result of the multiplication constraint.
 */
   def *(that: org.jacop.core.IntVar) = {
     val result = new IntVar()
     val c = new XmulYeqZ(this, that, result)
     Model.constr += c
     result
   }

/**
 * Defines multiplication constraint between IntVar and an integer value.
 *
 * @param that a second integer parameter for the multiplication constraint.
 * @return IntVar variable being the result of the multiplication constraint. 
  */
  def *(that: Int) = {
    val result = new IntVar()
    val c = new XmulCeqZ(this, that, result)
    Model.constr += c
    result
  }

/**
 * Defines integer division constraint between two IntVar.
 *
 * @param that a second parameter for the integer division constraint.
 * @return IntVar variable being the result of the integer division constraint.
 */
  def div(that: org.jacop.core.IntVar) = {
    val result = new IntVar()
    val c = new XdivYeqZ(this, that, result)
    Model.constr += c
    result
  }

/**
 * Defines constraint for integer reminder from division between two IntVar.
 *
 * @param that a second parameter for integer reminder from division constraint.
 * @return IntVar variable being the result of the integer reminder from division constraint.
 */
  def mod(that: org.jacop.core.IntVar) = {
     val result = new IntVar()
     val c = new XmodYeqZ(this, that, result)
     Model.constr += c
     result
   }

/**
 * Defines exponentiation constraint between two IntVar.
 *
 * @param that exponent for the exponentiation constraint.
 * @return IntVar variable being the result of the exponentiation constraint.
 */
  def ^(that: org.jacop.core.IntVar) = {
     val result = new IntVar()
     val c = new XexpYeqZ(this, that, result)
     Model.constr += c
     result
   }

/**
 * Defines unary "-" constraint for IntVar.
 *
 * @return the defined constraint.
 */
  def unary_- = {
    val result = new IntVar()
    val c = new XplusYeqC(this, result, 0)
    Model.constr += c
    result
  }

/**
 * Defines equation constraint between two IntVar.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  @deprecated("use #= instead", "1.0")
  def ==(that: org.jacop.core.IntVar) = { 
    val c = new XeqY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines equation constraint between two IntVar.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  def #=(that: org.jacop.core.IntVar) = { 
    val c = new XeqY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines equation constraint between IntVar and a integer constant.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  @deprecated("use #= instead", "1.0") 
  def ==(that: Int) = {
    val c = new XeqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines equation constraint between IntVar and a integer constant.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  def #=(that: Int) = {
    val c = new XeqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines inequality constraint between two IntVar.
 *
 * @param that a second parameter for inequality constraint.
 * @return the defined constraint.
 */
  @deprecated("use #\\= instead", "1.0") 
  def !=(that: org.jacop.core.IntVar) = {
    val c = new XneqY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines inequality constraint between two IntVar.
 *
 * @param that a second parameter for inequality constraint.
 * @return the defined constraint.
 */
  def #\=(that: org.jacop.core.IntVar) = {
    val c = new XneqY(this, that)
    Model.constr += c
    c
  }


/**
 * Defines inequality constraint between IntVar and integer constant.
 *
 * @param that a second parameter for inequality constraint.
 * @return the defined constraint.
 */
  @deprecated("use #\\= instead", "1.0") 
  def !=(that: Int) = {
    val c = new XneqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines inequality constraint between IntVar and integer constant.
 *
 * @param that a second parameter for inequality constraint.
 * @return the defined constraint.
 */
  def #\=(that: Int) = {
    val c = new XneqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "less than" constraint between two IntVar.
 *
 * @param that a second parameter for "less than" constraint.
 * @return the defined constraint.
 */
  @deprecated("use #< instead", "1.0") 
  def <(that: org.jacop.core.IntVar) = {
    val c = new XltY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "less than" constraint between two IntVar.
 *
 * @param that a second parameter for "less than" constraint.
 * @return the defined constraint.
 */
  def #<(that: org.jacop.core.IntVar) = {
    val c = new XltY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "less than" constraint between IntVar and integer constant.
 *
 * @param that a second parameter for "less than" constraint.
 * @return the equation constraint.
 */
  @deprecated("use #< instead", "1.0") 
  def <(that: Int) = {
    val c = new XltC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "less than" constraint between IntVar and integer constant.
 *
 * @param that a second parameter for "less than" constraint.
 * @return the equation constraint.
 */
  def #<(that: Int) = {
    val c = new XltC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "less than or equal" constraint between two IntVar.
 *
 * @param that a second parameter for "less than or equal" constraint.
 * @return the defined constraint.
 */
  @deprecated("use #<= instead", "1.0") 
  def <=(that: org.jacop.core.IntVar) = {
    val c = new XlteqY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "less than or equal" constraint between two IntVar.
 *
 * @param that a second parameter for "less than or equal" constraint.
 * @return the defined constraint.
 */
  def #<=(that: org.jacop.core.IntVar) = {
    val c = new XlteqY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "less than or equal" constraint between IntVar and integer constant.
 *
 * @param that a second parameter for "less than or equal" constraint.
 * @return the equation constraint.
 */
  @deprecated("use #<= instead", "1.0") 
  def <=(that: Int) = {
    val c = new XlteqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "less than or equal" constraint between IntVar and integer constant.
 *
 * @param that a second parameter for "less than or equal" constraint.
 * @return the equation constraint.
 */
  def #<=(that: Int) = {
    val c = new XlteqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "greater than" constraint between two IntVar.
 *
 * @param that a second parameter for "greater than" constraint.
 * @return the defined constraint.
 */
  @deprecated("use #> instead", "1.0") 
  def >(that: org.jacop.core.IntVar) = {
    val c = new XgtY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "greater than" constraint between two IntVar.
 *
 * @param that a second parameter for "greater than" constraint.
 * @return the defined constraint.
 */
  def #>(that: org.jacop.core.IntVar) = {
    val c = new XgtY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "greater than" constraint between IntVar and integer constant.
 *
 * @param that a second parameter for "greater than" constraint.
 * @return the equation constraint.
 */
  @deprecated("use #> instead", "1.0") 
  def >(that: Int) = {
    val c = new XgtC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "greater than" constraint between IntVar and integer constant.
 *
 * @param that a second parameter for "greater than" constraint.
 * @return the equation constraint.
 */
  def #>(that: Int) = {
    val c = new XgtC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "greater than or equal" constraint between two IntVar.
 *
 * @param that a second parameter for "greater than or equal" constraint.
 * @return the defined constraint.
 */
  @deprecated("use #>= instead", "1.0") 
  def >=(that: org.jacop.core.IntVar) = {
    val c = new XgteqY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "greater than or equal" constraint between two IntVar.
 *
 * @param that a second parameter for "greater than or equal" constraint.
 * @return the defined constraint.
 */
  def #>=(that: org.jacop.core.IntVar) = {
    val c = new XgteqY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "greater than or equal" constraint between IntVar and integer constant.
 *
 * @param that a second parameter for "greater than or equal" constraint.
 * @return the equation constraint.
 */
  @deprecated("use #>= instead", "1.0") 
  def >=(that: Int) = {
    val c = new XgteqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines "greater than or equal" constraint between IntVar and integer constant.
 *
 * @param that a second parameter for "greater than or equal" constraint.
 * @return the equation constraint.
 */
  def #>=(that: Int) = {
    val c = new XgteqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines constraint on inclusion of a IntVar variable value in a set.
 *
 * @param that set that this variable's value must be included.
 * @return the equation constraint.
 */
  def in (that: SetVar) : PrimitiveConstraint = {
    if (min == max) {
      val c = new EinA(min, that)
      Model.constr += c
      return c
    }
    else {
      val c = new XinA(this, that)
      Model.constr += c
      return c
    }
  }
}


/**
 * Defines a set variable and its primitive constraints.
 *
 * @constructor Creates a new set variable.
 * @param name variable's identifier.
 * @param glb greatest lower bound for variable's domain.
 * @param lub least upper bound on variable's domain.
 */
class SetVar(name : String, glb : Int, lub : Int) extends org.jacop.set.core.SetVar(Model, name, glb, lub) {

/**
 * Defines an anonymous set variable.
 *
 * @constructor Creates a new set variable.
 * @param glb greatest lower bound for variable's domain.
 * @param lub least upper bound on variable's domain.
 */
  def this(glb: Int, lub: Int) = {
    this("_$" + Model.n, glb, lub)
    Model.n += 1
  }

/**
 * Defines an anonymous set variable with maximal set domain.
 *
 * @constructor Creates a new finite domain integer variable.
 */
  def this() = {
    this("_$" + Model.n, org.jacop.core.IntDomain.MinInt, org.jacop.core.IntDomain.MaxInt)
    Model.n += 1
  }

/**
 * Defines set intersection constraint between two set variables.
 *
 * @param that second parameter for the constraint.
 * @return result set variable that is the result for this constraint.
 */
  def * (that: SetVar) =  {
    val result = new SetVar()
    val c = new AintersectBeqC(this, that, result)
    Model.constr += c
    result
  }

/**
 * Defines set union constraint between two set variables.
 *
 * @param that second parameter for the constraint.
 * @return result set variable that is the result for this constraint.
 */
  def + (that: SetVar) =  {
    val result = new SetVar()
    val c = new AunionBeqC(this, that, result)
    Model.constr += c
    result
  }

/**
 * Defines set subtraction constraint between two set variables.
 *
 * @param that second parameter for the constraint.
 * @return result set variable that is the result for this constraint.
 */
  def \ (that: SetVar) {
    val result = new SetVar()
    val c = new AdiffBeqC(this, that, result)
    Model.constr += c
    result
  }

/**
 * Defines set disjoint constraint between two set variables.
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  def <> (that: SetVar)  = {
    val c = new AdisjointB(this, that)
    Model.constr += c
    c
  }

/**
 * Defines set inclusion constraint between two set variables.
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  def in (that: SetVar)  = {
    val c = new AinB(this, that)
    Model.constr += c
    c
  }

/**
 * Defines set inclusion constraint between a set variables and a set.
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  def in (that: IntSet)  = {
    val c = new AinS(this, that)
    Model.constr += c
    c
  }

/**
 * Defines set equality constraint between two set variables.
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  @deprecated("use #= instead", "1.0") 
  def == (that: SetVar) = {
    val c = new AeqB(this, that)
    Model.constr += c
    c
  }

/**
 * Defines set equality constraint between two set variables.
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  def #= (that: SetVar) = {
    val c = new AeqB(this, that)
    Model.constr += c
    c
  }

/**
 * Defines set equality constraint between a set variable and a set.
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  @deprecated("use #= instead", "1.0") 
  def == (that: IntSet) = {
    val c = new AeqS(this, that)
    Model.constr += c
    c
  }

/**
 * Defines set equality constraint between a set variable and a set.
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  def #= (that: IntSet) = {
    val c = new AeqS(this, that)
    Model.constr += c
    c
  }

/**
 * Defines constraint this ordered set is lexicographically greater or equal than set "that".
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  @deprecated("use #>= instead", "1.0") 
  def >= (that: SetVar) = {
    val c = new org.jacop.set.constraints.Lex(that, this)
    Model.constr += c
    c
  }

/**
 * Defines constraint this ordered set is lexicographically greater or equal than set "that".
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  def #>= (that: SetVar) = {
    val c = new org.jacop.set.constraints.Lex(that, this)
    Model.constr += c
    c
  }

/**
 * Defines constraint this ordered set is lexicographically less or equal than set "that".
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  @deprecated("use #<= instead", "1.0") 
  def <= (that: SetVar) = {
    val c = new org.jacop.set.constraints.Lex(this, that)
    Model.constr += c
    c
  }

/**
 * Defines constraint this ordered set is lexicographically less or equal than set "that".
 *
 * @param that second parameter for the constraint.
 * @return result this constraint.
 */
  def #<= (that: SetVar) = {
    val c = new org.jacop.set.constraints.Lex(this, that)
    Model.constr += c
    c
  }
}

/**
 * Define a boolean variable and its primitive constraints.
 *
 * @constructor Creates a new boolean variable.
 * @param name variable's identifier.
 * @param min minimal value for variable's domain.
 * @param max maximal value for variable's domain.
 */
class BoolVar(name: String, min1: Int, max1: Int) extends org.jacop.core.BooleanVar (Model, name, min1, max1) 
               with jacop {

/**
 * Define a boolean variable with {0..1} domain.
 *
 * @constructor Creates a new boolean variable.
 * @param name variable's identifier.
 */
  def this(name: String) = {
     this (name, 0, 1)
     Model.n += 1
   }

/**
 * Define an anonymous boolean variable with {0..1} domain.
 *
 * @constructor Creates a new boolean variable.
 */
  def this() = {
    this ("_$" + Model.n, 0, 1)
    Model.n += 1
  }

/**
 * Define an anonymous boolean variable.
 *
 * @constructor Creates a new boolean variable.
 * @param min minimal value for variable's domain.
 * @param max maximal value for variable's domain.
 */
  def this(l: Int, r: Int) = {
    this ("_$" + Model.n, l, r)
    Model.n += 1
  }

/**
 * Defines equation constraint between two BoolVar.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  @deprecated("use #= instead", "1.0") 
  def ==(that: org.jacop.core.IntVar) = { 
    val c = new org.jacop.constraints.XeqY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines equation constraint between two BoolVar.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  def #=(that: org.jacop.core.IntVar) = { 
    val c = new org.jacop.constraints.XeqY(this, that)
    Model.constr += c
    c
  }

/**
 * Defines equation constraint a BoolVar and a integer value.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  @deprecated("use #= instead", "1.0") 
  def ==(that: Int) = {
    val c = new XeqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines equation constraint a BoolVar and a integer value.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  def #=(that: Int) = {
    val c = new XeqC(this, that)
    Model.constr += c
    c
  }

/**
 * Defines logical and (conjunction) constraint between two BoolVar.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  def /\(that: org.jacop.core.IntVar) = {
    val result = new BoolVar()
    val parameters = Array(this, that)
    val c = new org.jacop.constraints.AndBool(parameters, result)
    Model.constr += c
    result
  }

/**
 * Defines logical or (disjunction) constraint between two BoolVar.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  def \/(that: org.jacop.core.IntVar) = {
    val result = new BoolVar()
    val parameters = Array(this, that)
    val c = new org.jacop.constraints.OrBool(parameters, result)
    Model.constr += c
    result
  }

/**
 * Defines logical exclusive or constraint between two BoolVar.
 *
 * @param that a second parameter for equation constraint.
 * @return the defined constraint.
 */
  def xor(that: org.jacop.core.IntVar) = {
    val result = new BoolVar()
    val c = new org.jacop.constraints.XorBool(this, that, result)
    Model.constr += c
    result
  }

/**
 * Defines logical negation constraint for BoolVar.
 *
 * @return boolean variable that is the result for this constraint.
 */
  def unary_~ = {
    val result = new BoolVar()
    val c = new XplusYeqC(this, result, 1)
    Model.constr += c
    result
  }

/**
 * Defines implication constraint.
 *
 * @param thenConstr a primitive constraint that will hold if this variable is 1.
 * @return the defined constraint.
 */
  def ->(thenConstr: PrimitiveConstraint): Constraint = {
    val c: Constraint = new IfThen(new XeqC(this, 1), thenConstr)
    Model.constr.remove(Model.constr.length - 1)
    Model.constr += c
    c
  }

/**
 * Defines reified constraint.
 *
 * @param reifC a primitive constraint that is used in reification.
 * @return the defined constraint.
 */
  def <=>(reifC: PrimitiveConstraint): Constraint = {
    val c: Constraint = new Reified(reifC, this)
    Model.constr.remove(Model.constr.length - 1)
    Model.constr += c
    c
  }
}

//class XgtC(name: IntVar, const: Int) extends org.jacop.constraints.XgtC(name, const) {
//  def <=>(that: IntVar) = {
//    val c = new Reified(this, that)
//    Model.constr.remove(Model.constr.length - 1)
//    Model.constr += c
//    c
//  }
//}

/**
 * FSM specification for regular constraint.
 *
 * @constructor Creates a new FSM.
 */
class fsm extends org.jacop.util.fsm.FSM {

  import scala.collection.mutable.ArrayBuffer

  var states = ArrayBuffer[state]()

/**
 * FSM specification for regular constraint.
 * 
 * @constructor Creates a new FSM.
 * @param n number of states in this FSM.
 */
  def this(n: Int) {
    this()
    states = ArrayBuffer.tabulate(n)( i => new state)
    states.foreach( s => allStates.add(s))
  }

/**
 * Defines initial state for this FSM.
 *
 * @param s state.
 */
  def init(s: state) {
    initState = s
    states += s
    allStates.add(s)
  }

/**
 * Defines a list of final state for this FSM.
 *
 * @param st array of states.
 */
  def addFinalStates(st: Array[state]) {
    st.foreach( s => states += s)
    st.foreach( s => finalStates.add(s))
  }

  def +(s: state) : fsm = {
    states +=  s
    allStates.add(s)
    return this
  }

/**
 * Number of states in this FSM.
 *
 */
  def length = states.length

/**
 * Get state n of this FSM.
 *
 * @param n index of state.
 * @return n-th state
 */
  def apply(n: Int) : state = {     
    return states(n)
  }
}

/**
 * state specification for FSM for regular constraint.
 *
 * @constructor Creates a new state for FSM.
 */
class state extends org.jacop.util.fsm.FSMState {

  import org.jacop.util.fsm._

/**
 * Transition of FSM.
 *
 * @param tran values for executing this transition.
 * @param that next state for this transition.
 */
  def -> (tran: IntSet, that: state) {
    transitions.add(new FSMTransition(tran, that))
  }

/**
 * Transition of FSM.
 *
 * @param tran integer value for executing this transition.
 * @param that next state for this transition.
 */
  def -> (tran: Int, that: state) {
    transitions.add(new FSMTransition(new IntSet(tran, tran), that))
  }
}

/**
 * Network specification for networkflow constraint
 *
 * @constructor Creates an empty network
 */ 
class network extends org.jacop.constraints.netflow.NetworkBuilder {

  import scala.collection.mutable.HashMap

  var nodes = HashMap[node, org.jacop.constraints.netflow.simplex.Node]()

/**
 * Adds nodes to the network
 *
 * @param n node
 */ 
  def + (n: node): network = {
    val N = addNode(n.name, n.balance)
    nodes += (n -> N)
    // println("## " + N.name + ", " + N.balance) 
    return this
  }

/**
 * Get a node of the network in network format
 *
 * @param n node
 */ 
  def apply(n: node): org.jacop.constraints.netflow.simplex.Node = {
    return nodes(n)
  }

/**
 * Creates an arc between two nodes.
 *
 * @param source start node of the arc
 * @param destination end node the arc
 * @param weight weight of this arc for cost calculation
 * @param capacity capacity for the flow on this arc
 */ 
  def arc(source: node, destination: node, weight: IntVar, capacity: IntVar) {
    // println(source.name + " -> " + destination.name) 
    addArc(nodes(source), nodes(destination), weight, capacity)
  }

  def cost(c: IntVar) {
    setCostVariable(c)
  }
}

/**
 * Node definition for network for networkflow constraint
 */ 
case class node(var name: String, var balance: Int) { //extends org.jacop.constraints.netflow.simplex.Node(name, balance) {

}


/**
 * Solution listener that does not print anything (empty).
 * Used to prohibit printing from search.
 */ 
/*
class EmptyListener[T <: org.jacop.core.Var] extends org.jacop.search.SimpleSolutionListener[T] {

  override def executeAfterSolution( search: org.jacop.search.Search[T], select: org.jacop.search.SelectChoicePoint[T]) : Boolean = {

    val returnCode = super.executeAfterSolution(search, select);

    return returnCode;
  }
}
*/


/**
 * Solution listener that prints solutions of search
 * using user specified functions.
 */ 
class ScalaSolutionListener[T <: org.jacop.core.Var] extends org.jacop.search.SimpleSolutionListener[T] {

  override def executeAfterSolution(search: org.jacop.search.Search[T], select: org.jacop.search.SelectChoicePoint[T]) : Boolean = {

    val returnCode = super.executeAfterSolution(search, select);

    printFunctions.foreach(_.apply)

    return returnCode;
  }
}

class Reifier[T <: PrimitiveConstraint](reifC: T) {
	def <=>(b: BoolVar): Constraint = {
		val c: Constraint = new Reified(reifC, b)
		Model.constr.remove(Model.constr.length - 1)
		Model.constr += c
		c
	}
}

