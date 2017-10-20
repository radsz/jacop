/*
 * BreakingNews.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.examples.scala

import org.jacop.scala._

/**
  * A problem defined as in Java based examples.
  *
  * rewriting to Scala by Krzysztof Kuchcinski.
  * @author Krzysztof Kuchcinski and Radoslaw Szymanek
  * @version 4.4
  */
object BreakingNews extends App with jacop {

  println("Program to solve Breaking News ")

  // String arrays with reporters names.
  val ReporterName = Array( "Corey", "Jimmy", "Lous", "Perry" )

  // Constant indexes to ease referring to variables denoting reporters.
  val iCorey = 1; val iJimmy = 2; val iLous = 3; /* val iPerry = 0; */ 
		
  // String arrays with locations names.
  val LocationName = Array( "Bayonne", "NewHope", "PortCharles",
				"SouthAmboy" )
		
  // Constant indexes to ease referring to variables denoting locations.
  val iBayonne = 0; val iNewHope = 1; val iPortCharles = 2; val iSouthAmboy = 3

  // String arrays with stories names.
  val StoryName = Array( "30pound", "blimp", "skyscraper", "beached" )

  // Constant indexes to ease referring to variables denoting stories.
  val i30pound = 0; val iblimp = 1; val iskyscraper = 2; val ibeached = 3

  // All variables are created with domain 1..4. Variables from
  // different arrays with the same values denote the same person.

  val reporter = Array.tabulate(4)( i => new IntVar(ReporterName(i), 1, 4))
  val location = Array.tabulate(4)( i => new IntVar(LocationName(i), 1, 4))
  val story = Array.tabulate(4)( i => new IntVar(StoryName(i), 1, 4))

  // It is not possible that one person has two names, or
  // has been in two locations.

  alldifferent(reporter)
  alldifferent(location)
  alldifferent(story)

  // 1. The 30-pound baby wasn't born in South Amboy or New Hope.
  OR( story(i30pound) #\= location(iNewHope), story(i30pound) #\= location(iSouthAmboy))

  // 2. Jimmy didn't go to Port Charles.
  reporter(iJimmy) #\= location(iPortCharles)

  // 3.The blimp launching and the skyscraper dedication were
  // covered, in some order, by Lois and the reporter who was
  // sent to Port Charles.

  OR( AND(story(iblimp) #= reporter(iLous), story(iskyscraper) #= location(iPortCharles)), 
      AND(story(iblimp) #= location(iPortCharles), story(iskyscraper) #= reporter(iLous)) )

  // 4. South Amboy was not the site of either the beached whale
  // or the skyscraper dedication.
  OR( location(iSouthAmboy) #\= story(ibeached), location(iSouthAmboy) #\= story(iskyscraper) )

  // 5. Bayonne is either the place that Corey went or the place
  // where the whale was beached, or both.
   OR( location(iBayonne) #= reporter(iCorey), location(iBayonne) #= story(ibeached),
       AND( story(ibeached) #= reporter(iCorey), reporter(iCorey) #= location(iBayonne)) )


  val result = satisfy( search( reporter ++ location ++ story, input_order, indomain_min) )
}
