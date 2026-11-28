/*
 * MinizincDefaultSettingsTest.java
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
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Solves a sample of the upTo5sec models with the settings fzn-jacop users get and checks the
 * answers against {@code free-search-reference.txt}, as {@link MinizincFreeSearchTest} does.
 *
 * <p>The test JVMs set {@code jacop.lcg=off}, {@code jacop.symmetry=presolve}, {@code
 * org.jacop.fz.symmetryTime} and {@code org.jacop.fz.lpProbe} (parent pom), and the upTo5sec test
 * adds {@code --default-search input}, so no other corpus test runs lazy clause generation, default
 * symmetry breaking or default free search for models without annotation. This test clears those
 * properties for its runs (Options reads them per run) and passes no option but the model's own
 * {@code options.opt}: each model is solved with the defaults and with {@code -f}. {@code
 * jacop.asserts.enabled} is read once per JVM and stays on.
 *
 * <p>The sample, {@code default-settings-sample.txt}, holds models whose default run differs from
 * the test configuration (lazy clause generation, symmetry breaking or free search fired) and
 * finishes within a second. The system property {@code defaults.instances} limits the number of
 * models taken from its start (default all).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class MinizincDefaultSettingsTest {

  private static final String SAMPLE = "src/test/fz/upTo5sec/default-settings-sample.txt";

  /** The properties of the test JVMs that change the defaults of the front end. */
  private static final List<String> TEST_PROPERTIES =
      List.of("jacop.lcg", "jacop.symmetry", "org.jacop.fz.symmetryTime", "org.jacop.fz.lpProbe");

  static Stream<String> sample() throws IOException {
    Map<String, String> reference =
        MinizincFreeSearchTest.reference()
            .collect(Collectors.toMap(l -> l.trim().split("\\s+")[0], l -> l, (a, b) -> a));
    Set<String> seen = new HashSet<>();
    return Files.readAllLines(Path.of(SAMPLE), StandardCharsets.UTF_8).stream()
        .map(String::trim)
        .filter(l -> !l.isEmpty() && !l.startsWith("#") && seen.add(l))
        .limit(Long.getLong("defaults.instances", Long.MAX_VALUE))
        .map(
            m -> {
              String line = reference.get(m);
              if (line == null) {
                throw new IllegalStateException(m + " of " + SAMPLE + " has no reference answer");
              }
              return line;
            });
  }

  @ParameterizedTest
  @MethodSource("sample")
  @Timeout(60)
  void defaultSettingsAgreeWithTheReference(String line) throws IOException {
    Map<String, String> saved = new HashMap<>();
    for (String p : TEST_PROPERTIES) {
      saved.put(p, System.clearProperty(p));
    }
    try {
      MinizincFreeSearchTest.check(line, List.of());
      MinizincFreeSearchTest.check(line, List.of("-f"));
    } finally {
      saved.forEach(
          (p, v) -> {
            if (v != null) {
              System.setProperty(p, v);
            }
          });
    }
  }
}
