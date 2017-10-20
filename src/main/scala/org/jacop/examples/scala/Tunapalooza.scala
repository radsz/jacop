/*
 * Tunapalooza.java
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

import scala.collection.mutable.ArrayBuffer
import org.jacop.scala._

/**
  * A problem defined as in Java based examples.
  *
  * rewriting to Scala by Krzysztof Kuchcinski.
  * @author Krzysztof Kuchcinski and Radoslaw Szymanek
  * @version 4.5
  */
object Tunapalooza extends App with jacop {

  var vars = new ArrayBuffer[org.jacop.core.IntVar]()
		
  // names
  val Ellyfish = 1; val Korrupt = 2; val Retread = 3; val Yellow = 4


  // types
  val country = new IntVar("country", 1, 4)
  val grunge = new IntVar("grunge", 1, 4)
  val reggae = new IntVar("reggae", 1, 4)
  val metal = new IntVar("metal", 1, 4)
  // places
  val carnival = new IntVar("carnival", 1, 4)
  val information = new IntVar("information", 1, 4)
  val mosh = new IntVar("mosh", 1, 4)
  val vendor = new IntVar("vendor", 1, 4)

		// arrays of variables
  val types= Array( country, grunge, reggae, metal )
  val places = Array( carnival, information, mosh, vendor )

  for (v <- types) vars :+= v
  for (v <- places) vars :+= v

   // All types and places have to be associated with different band.
   alldifferent(types)
   alldifferent(places)

  // 1. Korrupt isn't a country or grunge music band.

  AND( country #\= Korrupt, grunge #\= Korrupt )

  // 2. Tim and Kerri won't meet at the carnival games during Ellyfish's
  // performance.

  carnival #\= Ellyfish

  // 3. The pair won't meet at the T-shirt vendor during the reggae band's
  // show.

  vendor #\= reggae

  // 4. Exactly two of the following three statements are true:
  // a) Ellyfish plays grunge music.
  // b) Tim and Kerri won't meet at the information booth during a
  // performance by Retread Ed and the Flat Tires.
  // c) The two friends won't meet at the T-shirt vendor while Yellow Reef
  // is playing.

  val statement1 = new BoolVar("s1")
  val statement2 = new BoolVar("s2")
  val statement3 = new BoolVar("s3")

  (grunge #= Ellyfish) <=> statement1
  statement2 <=> (information #\= Retread)
  statement3 <=> (vendor #\= Yellow)

  sum(List( statement1, statement2, statement3 )) #= 2

  for (v <-  Array( statement1, statement2, statement3 ))
    vars :+= v 

  // 5. The country and speed metal acts are, in some order, Retread Ed
  // and the Flat Tires
  // and the act during which Tim and Kerri will meet at the mosh pit.

  OR( country #= mosh, metal #= mosh )
  OR( country #= Retread, metal #= Retread )
  mosh #\=  Retread

  // 6. The reggae band is neither Korrupt nor the act during which Tim
  // and
  // Kerri will meet at the information booth.

  reggae #\= Korrupt
  reggae #\= information

  val result = satisfyAll( search(vars.toList, input_order, indomain_min))

}
