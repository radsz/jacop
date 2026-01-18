/*
 * ExampleBasedTest.java
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

package org.jacop.examples.set;

import org.junit.Test;

public class ExampleBasedTest {

  private static final int TIMEOUT_MS = 10_000;

  @Test(timeout = TIMEOUT_MS)
  public void testGardner() {
    Gardner example = new Gardner();
    example.model();

    example.search();
  }

  @Test(timeout = TIMEOUT_MS)
  public void testSocialGolfer() {
    SocialGolfer example = new SocialGolfer();

    example.setup(3, 2, 2);
    example.model();
    example.search();

    example.setup(2, 5, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(2, 6, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(2, 7, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(3, 5, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(3, 6, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(3, 7, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(4, 5, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(4, 6, 5); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(4, 7, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(4, 9, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(5, 5, 3); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(5, 7, 4); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(5, 8, 3); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(6, 6, 3); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(5, 3, 2); // weeks - groups - players in each group
    example.model();
    example.search();

    example.setup(4, 3, 3); // weeks - groups - players in each group
    example.model();
    example.search();
  }

  @Test(timeout = TIMEOUT_MS)
  public void testSteiner() {
    Steiner example = new Steiner();
    example.n = 7;
    example.model();

    example.search();
  }
}
