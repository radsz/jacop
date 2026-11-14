/*
 * FloatImposeGroundingTest.java
 * <p>
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

package org.jacop.floats;

import java.util.Arrays;
import java.util.Random;
import java.util.function.Function;
import java.util.stream.Stream;
import org.jacop.floats.FloatImposeGroundingHarness.Case;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Imposes each float constraint with none, all and chosen subsets of its variables already ground
 * (see {@link FloatImposeGroundingHarness}) and compares the accepted grid points with brute force.
 * The instance generators are in {@link FloatImposeGroundingCases}.
 *
 * <pre>
 * mvn -Pnocs -pl jacop-floats test -Dtest=FloatImposeGroundingTest \
 *     -Dsurefire.rerunFailingTestsCount=0 -Dgrounding.cases=PeqC,Max -Dgrounding.trials=200
 * </pre>
 */
class FloatImposeGroundingTest {

  private static final int TRIALS = Integer.getInteger("grounding.trials", 40);

  /** Comma-separated parts of case names to run, e.g. {@code -Dgrounding.cases=PeqC,Max}. */
  private static final String FILTER = System.getProperty("grounding.cases", "");

  static Stream<Arguments> cases() {
    return FloatImposeGroundingCases.cases()
        .filter(
            a ->
                FILTER.isEmpty()
                    || Arrays.stream(FILTER.split(","))
                        .anyMatch(part -> a.get()[0].toString().contains(part)));
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void imposeWithGroundedVariables(String name, Function<Random, Case> generator) {
    FloatImposeGroundingHarness.check(name, generator, TRIALS);
  }
}
