/*
 * StonesOfHeaven.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.examples.fd;

import java.util.ArrayList;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * It solves a simple logic puzzle about artifacts.
 *
 * <p>Title: Stones of Heaven Author: Jo Mason Publication: Dell Logic Puzzles Issue: April, 1998
 * Page: 13
 *
 * <p>Wan Li, a dealer in Chinese antiques and artifacts, had an excellent month recently when he
 * made sales to four customers from around the world -- Finland, Italy, Japan, and the United
 * States -- who were willing and able to pay very good prices. The four items were rare jade
 * figurines (a belt buckle, dragon, grasshopper, and horse), each carved from a different color of
 * jade (dark green, light green, red, and white). Each piece dates from a different Chinese dynasty
 * (Ching, Ming, Sung, and Tang). Can you match each figurine with its color and dynasty, and give
 * the home country of each buyer?
 *
 * <p>1. The rare white dragon (which the American didn't buy) didn't come from the Sung dynasty.
 *
 * <p>2. The exquisite belt buckle (which wasn't any shade of green) was created in 618 A.D. for an
 * emperor of the Tang dynasty.
 *
 * <p>3. Three of the figurines were the one bought by the Finn (which wasn't the dragon), the one
 * from the Ching dynasty (which didn't go to the buyer from Japan), and the light green object
 * (which wasn't the horse).
 *
 * <p>4. The American decided against both the grasshopper and the piece from the Sung dynasty,
 * neither of which she felt would match her home decor.
 *
 * <p>Belt buckle, red, Tang, U.S Dragon, white, Ching, Italy Grasshopper, light green, Ming, Japan
 * Horse, dark green, Sung, Finland
 *
 * @author Janusz Kociolek, Sebastian Czypek, and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class StonesOfHeaven extends ExampleFd {

  /**
   * It executes a simple program to solve this logic puzzle.
   *
   * @param args command arguments (none here)
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    StonesOfHeaven example = new StonesOfHeaven();

    example.model();

    if (example.search()) {
      log.info("Solution(s) found");
    }
  }

  @Override
  public void model() {

    store = new Store();
    vars = new ArrayList<>();

    log.info("Solution for problem Stones of Heaven");

    String[] colorNames = {"red", "lightgreen", "white", "darkgreen"};
    final int /* ired = 0, */ iLgreen = 1;
    final int iwhite = 2;
    final int iDgreen = 3;

    String[] countryNames = {"USA", "Finland", "Japan", "Italy"};
    final int iusa = 0;
    final int ifin = 1;
    final int ijapan = 2; /*, iitaly = 3 */

    String[] itemNames = {"beltbuckle", "dragon", "grasshopper", "horse"};
    final int ibelt = 0;
    final int idragon = 1;
    final int igrasshopper = 2;
    final int ihorse = 3;

    String[] dynastyNames = {"Ching", "Ming", "Sung", "Tang"};
    final int iChing = 0; /* iMing = 1, */
    final int iSung = 2;
    final int iTang = 3;

    IntVar[] color = new IntVar[4];
    IntVar[] country = new IntVar[4];
    IntVar[] item = new IntVar[4];
    IntVar[] dynasty = new IntVar[4];

    for (int i = 0; i < 4; i++) {
      color[i] = new IntVar(store, colorNames[i], 1, 4);
      country[i] = new IntVar(store, countryNames[i], 1, 4);
      item[i] = new IntVar(store, itemNames[i], 1, 4);
      dynasty[i] = new IntVar(store, dynastyNames[i], 1, 4);
      vars.add(color[i]);
      vars.add(country[i]);
      vars.add(item[i]);
      vars.add(dynasty[i]);
    }

    store.impose(new Alldifferent(color));
    store.impose(new Alldifferent(country));
    store.impose(new Alldifferent(item));
    store.impose(new Alldifferent(dynasty));

    // 1. The rare white dragon (which the American didn't buy) didn't come
    // from the Sung dynasty.

    store.impose(new XeqY(color[iwhite], item[idragon]));
    store.impose(new XneqY(dynasty[iSung], item[idragon]));
    store.impose(new XneqY(country[iusa], item[idragon]));

    // 2. The exquisite belt buckle (which wasn't any shade of green) was
    // created in 618 A.D. for an emperor of the Tang dynasty.

    store.impose(new XneqY(item[ibelt], color[iLgreen]));
    store.impose(new XneqY(item[ibelt], color[iDgreen]));
    store.impose(new XeqY(item[ibelt], dynasty[iTang]));

    // 3. Three of the figurines were the one bought by the Finn (which
    // wasn't the dragon), the one from the Ching dynasty (which didn't go
    // to the buyer from Japan), and the light green object (which wasn't
    // the horse).
    store.impose(new XneqY(country[ifin], item[idragon]));
    store.impose(new XneqY(country[ifin], dynasty[iChing]));
    store.impose(new XneqY(country[ifin], color[iLgreen]));

    store.impose(new XneqY(dynasty[iChing], country[ijapan]));
    store.impose(new XneqY(dynasty[iChing], color[iLgreen]));

    store.impose(new XneqY(color[iLgreen], item[ihorse]));

    // 4. The American decided against both the grasshopper and the piece
    // from the Sung dynasty, neither of which she felt would match her
    // home decor.
    store.impose(new XneqY(country[iusa], item[igrasshopper]));
    store.impose(new XneqY(country[iusa], dynasty[iSung]));

    store.impose(new XneqY(item[igrasshopper], dynasty[iSung]));
  }
}
