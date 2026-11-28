/*
 * MinizincBasedUpTo5SecondsTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop;

import java.io.IOException;
import java.util.stream.Stream;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Minizinc based tests for problems that run upTo5seconds.
 *
 * @author Mariusz Świerkot and Radoslaw Szymanek
 * @version 5.0
 */
class MinizincBasedUpTo5SecondsTest extends MinizincBasedTestsHelper {
  protected static final String TIME_CATEGORY = "upTo5sec/";

  public MinizincBasedUpTo5SecondsTest() {
    super(TIME_CATEGORY);
  }

  static Stream<String> parametricTest() throws IOException {
    return fileReader(TIME_CATEGORY).stream();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  @Timeout(20) // The test will be completed within 20 seconds
  void testMinizinc(String testFilename) throws IOException {
    this.testFilename = testFilename;
    testExecution(TIME_CATEGORY);
  }
}
