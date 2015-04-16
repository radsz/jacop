package org.jacop.examples.scala

import org.jacop.core._
import org.jacop.constraints._
import org.jacop.search._
import org.slf4j.Logger
import org.slf4j.LoggerFactory
/*
 * Created by IntelliJ IDEA.
 * User: kris
 * Date: 2012-06-13
 * Time: 12:11
 */

object GraphColoringJ extends App {
  val logger = LoggerFactory.getLogger("GraphColoringJ")
  val store = new Store()
  val size = 4
  val v = Array.tabulate(size)(i => new IntVar(store, "v"+i, 1, size))
  v.foreach(x => println(x.toString))
  store.impose( new XneqY(v(0), v(1)) )
  store.impose( new XneqY(v(0), v(2)) )
  store.impose( new XneqY(v(1), v(2)) )
  store.impose( new XneqY(v(1), v(3)) )
  store.impose( new XneqY(v(2), v(3)) )

  val search = new DepthFirstSearch[IntVar]
  val select = new InputOrderSelect[IntVar](store, v, new IndomainMin[IntVar]())
  val result = search.labeling(store, select)
  if ( result )
    logger.info("Solution: " + v(0)+", "+v(1) +", "+ v(2) +", "+v(3))
  else
    logger.info("*** No")

}
