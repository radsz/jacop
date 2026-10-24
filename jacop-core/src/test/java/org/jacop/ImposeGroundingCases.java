/*
 * ImposeGroundingCases.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import java.util.stream.Stream;
import org.jacop.ImposeGroundingHarness.Case;
import org.jacop.constraints.GCC;
import org.jacop.constraints.XplusYeqZ;
import org.junit.jupiter.params.provider.Arguments;

/**
 * Instance generators for {@link ImposeGroundingTest} for constraints that have none in {@link
 * GlobalConstraintBruteForceTest}. Add a generator per constraint and list it in {@link #cases()}.
 */
final class ImposeGroundingCases {

  private ImposeGroundingCases() {}

  static Stream<Arguments> cases() {
    return Stream.of(
        Arguments.of(
            "XplusYeqZ",
            (Function<Random, Case>)
                random ->
                    Case.primitive(
                        domains(random, 3, -2, 4),
                        x -> new XplusYeqZ(x[0], x[1], x[2]),
                        t -> t[0] + t[1] == t[2],
                        "")),
        Arguments.of("GCC with first value", (Function<Random, Case>) ImposeGroundingCases::gcc));
  }

  static int[][] domains(Random random, int n, int lo, int hi) {
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      domains[i] = domain(random, lo, hi);
    }
    return domains;
  }

  /** A random non-empty subset of lo..hi, so domains may have holes. */
  static int[] domain(Random random, int lo, int hi) {
    List<Integer> values = new ArrayList<>();
    for (int v = lo; v <= hi; v++) {
      if (random.nextInt(4) != 0) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(lo + random.nextInt(hi - lo + 1));
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }
}
