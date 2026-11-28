/*
 * MinizincPortfolioTest.java
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
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Runs the parallel portfolio ({@code -p 4}) on the upTo5sec models of {@code
 * free-search-reference.txt} and checks its answers as {@link MinizincFreeSearchTest} checks free
 * search: the same satisfiability and optimum as the model's own search, never an objective better
 * than the optimum. Its threads share the objective bound, so an optimum proved by one of them
 * under a bound found by another is checked here too.
 *
 * <p>The system property {@code portfolio.every} (default 8) takes every n-th model; 1 runs all of
 * them.
 */
class MinizincPortfolioTest {

  static Stream<String> reference() throws IOException {
    int every = Integer.getInteger("portfolio.every", 8);
    AtomicInteger i = new AtomicInteger();
    return MinizincFreeSearchTest.reference().filter(l -> i.getAndIncrement() % every == 0);
  }

  @ParameterizedTest
  @MethodSource("reference")
  @Timeout(30)
  void portfolioAgreesWithTheModelSearch(String line) throws IOException {
    MinizincFreeSearchTest.check(line, List.of("-f", "-p", "4"));
  }
}
