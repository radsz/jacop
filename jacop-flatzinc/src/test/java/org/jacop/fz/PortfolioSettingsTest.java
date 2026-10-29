/*
 * PortfolioSettingsTest.java
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

package org.jacop.fz;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

import java.util.List;
import org.junit.jupiter.api.Test;

/** Which settings the threads of the portfolio get. */
class PortfolioSettingsTest {

  private static List<String> names(String given, int count, boolean satisfaction) {
    return Portfolio.settings(given, count, satisfaction).stream().map(c -> c[0]).toList();
  }

  @Test
  void objectiveSettingsDoNotMatterWithoutAnObjective() {
    List<String> lcgBb = List.of("--lcg", "-f", "--free-config", "lcg-core=0,lcg-lb=0");
    List<String> lcg = List.of("--lcg", "-f");
    assertEquals(Portfolio.search(lcg, true), Portfolio.search(lcgBb, true));
    assertNotEquals(Portfolio.search(lcg, false), Portfolio.search(lcgBb, false));
  }

  @Test
  void satisfactionSkipsTheSettingsThatRepeatAnEarlierThread() {
    String free = Portfolio.search(List.of("-f"), true);
    assertEquals(List.of("lcg", "free-chs-luby", "free-cacd"), names(free, 3, true));
  }

  @Test
  void optimisationKeepsTheOrder() {
    String free = Portfolio.search(List.of("-f"), false);
    assertEquals(List.of("lcg", "free-chs-luby", "lcg-bb"), names(free, 3, false));
    String none = Portfolio.search(List.of(), false);
    assertEquals(List.of("free", "lcg", "free-chs-luby"), names(none, 3, false));
  }
}
