
package org.jacop.examples.scala


/**
 * 
 * It is a simple logic puzzle about shoe purchases.
 * 
 * @author Adam Plonka, Piotr Ogrodzki, and Radoslaw Szymanek
 * 
 * Logic Puzzle

 * Title       : Arch Friends
 * Author      : Mark T. Zegarelli
 * Publication : Dell Logic Puzzles
 * Issue       : April, 1998
 * Page        : 7
 * Stars       : 1

 * Description : 

 * Harriet, upon returning from the mall, is happily describing her
 * four shoe purchases to her friend Aurora. Aurora just loves the four
 * different kinds of shoes that Harriet bought (ecru espadrilles,
 * fuchsia flats, purple pumps, and suede sandals), but Harriet can't
 * recall at which different store (Foot Farm, Heels in a Handcart, The
 * Shoe Palace, or Tootsies) she got each pair. Can you help these two
 * figure out the order in which Harriet bought each pair of shoes, and
 * where she bought each?
 */

import org.jacop.scala._

object ArchFriends extends App with jacop {
	
  println("Program to solve ArchFriends problem ")

  // Declaration of constants (names, variables' indexes

  val shoeNames = Array( "EcruEspadrilles", "FuchsiaFlats",
				"PurplePumps", "SuedeSandals" )

  val iFuchsiaFlats = 1; val iPurplePumps = 2; val iSuedeSandals = 3; /* iEcruEspadrilles = 0, */ 

  val shopNames = Array( "FootFarm", "HeelsInAHandcart", "TheShoePalace",
				"Tootsies" )

  val iFootFarm = 0; val iHeelsInAHandcart = 1; val iTheShoePalace = 2; val iTootsies = 3

  // Variables shoe and shop

  // Each variable has a domain 1..4 as there are four different
  // shoes and shops. Values 1 to 4 within variables shoe
  // denote the order in which the shoes were bought.
  val shoe = Array.tabulate(4)(i => new IntVar(shoeNames(i), 1, 4))
  val shop = Array.tabulate(4)(i => new IntVar(shopNames(i), 1, 4))

  // Each shoe, shop have to have a unique identifier.
  alldifferent(shoe)
  alldifferent(shop)

  // Constraints given in the problem description.

  // 1. Harriet bought fuchsia flats at Heels in a Handcart.
  shoe(iFuchsiaFlats) #= shop(iHeelsInAHandcart)

  // 2.The store she visited just after buying her purple pumps
  // was not Tootsies.

  // Nested constraint by applying constraint Not to constraint XplusCeqZ
  // NOT( shoe(iPurplePumps) + 1 #= shop(iTootsies) )
  shoe(iPurplePumps) + 1 #\= shop(iTootsies)

  // 3. The Foot Farm was Harriet's second stop.
  shop(iFootFarm) #= 2

  // 4. Two stops after leaving The Shoe Place, Harriet
  // bought her suede sandals.
  shop(iTheShoePalace) + 2 #= shoe(iSuedeSandals)

  val result = satisfyAll( search( shoe ++ shop, input_order, indomain_min))

}

