/*
 * ImposeGroundingTest.java
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

package org.jacop;

import java.util.Arrays;
import java.util.Random;
import java.util.function.Function;
import java.util.stream.Stream;
import org.jacop.ImposeGroundingHarness.Case;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Imposes each constraint with none, all and chosen subsets of its variables already ground (see
 * {@link ImposeGroundingHarness}) and compares all solutions with brute force.
 *
 * <p>The global constraints reuse the instance generators of {@link
 * GlobalConstraintBruteForceTest}; constraints without a generator there get one in {@link
 * ImposeGroundingCases}.
 *
 * <pre>
 * mvn -Pnocs -pl jacop-core test -Dtest=ImposeGroundingTest -Dsurefire.rerunFailingTestsCount=0 \
 *     -Dgrounding.cases=GCC,Knapsack -Dgrounding.trials=200
 * </pre>
 */
class ImposeGroundingTest {

  private static final int TRIALS = Integer.getInteger("grounding.trials", 40);

  /** Comma-separated parts of case names to run, e.g. {@code -Dgrounding.cases=GCC,Knapsack}. */
  private static final String FILTER = System.getProperty("grounding.cases", "");

  static Stream<Arguments> cases() {
    Stream<Arguments> globals =
        GlobalConstraintBruteForceTest.cases()
            // GCC(x, counters) takes its counted values from the union of the domains of x when it
            // is created, so grounding x first changes the constraint; "GCC with first value" in
            // ImposeGroundingCases checks GCC(x, counters, firstValue) instead
            .filter(a -> !a.get()[0].equals("GCC"))
            .map(
                a -> {
                  @SuppressWarnings("unchecked")
                  Function<Random, GlobalConstraintBruteForceTest.Instance> g =
                      (Function<Random, GlobalConstraintBruteForceTest.Instance>) a.get()[1];
                  Function<Random, Case> generator =
                      random -> {
                        GlobalConstraintBruteForceTest.Instance i = g.apply(random);
                        return Case.of(i.domains(), i.impose(), i.semantics(), i.description());
                      };
                  return Arguments.of(a.get()[0], generator);
                });
    return Stream.concat(globals, ImposeGroundingCases.cases())
        .filter(
            a ->
                FILTER.isEmpty()
                    || Arrays.stream(FILTER.split(","))
                        .anyMatch(part -> a.get()[0].toString().contains(part)));
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void imposeWithGroundedVariables(String name, Function<Random, Case> generator) {
    ImposeGroundingHarness.check(name, generator, TRIALS);
  }
}
