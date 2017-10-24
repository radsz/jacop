/*
 * ArchFriends.java
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

