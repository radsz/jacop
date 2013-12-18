package org.jacop.examples.scala

/**
 * 
 * It solves a simple logic puzzle about reporters breaking news stories.
 * 
 * @author Marcin Chrapek, Miroslaw Klos, and Radoslaw Szymanek
 * 
 * Logic Puzzle : Breaking News.
 *
 * The Daily Galaxy sent its four best reporters (Corey, Jimmy, Lois,
 * and Perry) to different locations (Bayonne, New Hope, Port Charles,
 * and South Amboy) to cover four breaking news events (30-pound baby,
 * blimp launching, skyscraper dedication, and beached whale). Their
 * editor is trying to remember where each of the reporters is. Can
 * you match the name of each reporter with the place he or she was
 * sent, and the event that each covered?
 *
 * 1. The 30-pound baby wasn't born in South Amboy or New Hope.
 *
 * 2. Jimmy didn't go to Port Charles.
 *
 * 3. The blimp launching and the skyscraper dedication were covered, in
 * some order, by Lois and the reporter who was sent to Port Charles.
 *
 * 4. South Amboy was not the site of either the beached whale or the
 * skyscraper dedication.
 *
 * 5. Bayonne is either the place that Corey went or the place where the
 * whale was beached, or both.
 *
 * Determine: Reporter -- Location -- Story
 *
 */

import org.jacop.scala._

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
