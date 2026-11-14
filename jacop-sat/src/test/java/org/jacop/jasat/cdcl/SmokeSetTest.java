/*
 * SmokeSetTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.cdcl;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;
import java.util.zip.GZIPInputStream;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Solves part of the smoke set of the osolpro SAT kit (generated CP-like and classic CNF families)
 * and checks every answer: the status against CaDiCaL's, a model against the formula, and an UNSAT
 * answer through its DRAT proof with {@link RupChecker}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class SmokeSetTest {

  private static final String DIR = "smoke/";

  static Stream<String[]> instances() throws IOException {
    List<String[]> result = new ArrayList<>();
    try (BufferedReader in = reader(SmokeSetTest.class.getResourceAsStream(DIR + "expected.txt"))) {
      for (String line = in.readLine(); line != null; line = in.readLine()) {
        if (!line.isBlank() && !line.startsWith("#")) {
          result.add(line.trim().split("\\s+"));
        }
      }
    }
    return result.stream();
  }

  private static BufferedReader reader(InputStream in) {
    assertNotNull(in, "missing test resource");
    return new BufferedReader(new InputStreamReader(in, StandardCharsets.US_ASCII));
  }

  private static byte[] read(String file) throws IOException {
    try (InputStream in = new GZIPInputStream(SmokeSetTest.class.getResourceAsStream(DIR + file))) {
      return in.readAllBytes();
    }
  }

  private static List<int[]> clauses(byte[] cnf) {
    List<int[]> result = new ArrayList<>();
    List<Integer> clause = new ArrayList<>();
    for (String line : new String(cnf, StandardCharsets.US_ASCII).split("\n")) {
      line = line.trim();
      if (line.isEmpty() || line.startsWith("c") || line.startsWith("p")) {
        continue;
      }
      for (String token : line.split("\\s+")) {
        int lit = Integer.parseInt(token);
        if (lit == 0) {
          result.add(clause.stream().mapToInt(Integer::intValue).toArray());
          clause.clear();
        } else {
          clause.add(lit);
        }
      }
    }
    return result;
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("instances")
  void answersAreChecked(String file, String status) throws IOException {
    byte[] cnf = read(file);
    CdclSolver s = new CdclSolver();
    ByteArrayOutputStream proof = new ByteArrayOutputStream();
    DratWriter drat = new DratWriter(proof);
    s.setProof(drat);
    DimacsReader.read(new ByteArrayInputStream(cnf), s);
    s.setConflictLimit(2_000_000);
    int result = s.solve();
    drat.close();
    assertEquals("sat".equals(status) ? CdclSolver.SAT : CdclSolver.UNSAT, result, file);
    List<int[]> formula = clauses(cnf);
    if (result == CdclSolver.SAT) {
      for (int[] c : formula) {
        boolean satisfied = false;
        for (int l : c) {
          satisfied |= s.modelValue(Math.abs(l)) == l > 0;
        }
        assertTrue(satisfied, "the model falsifies a clause");
      }
    } else {
      assertNull(RupChecker.check(s.numVars(), formula, proof.toString(StandardCharsets.US_ASCII)));
    }
  }
}
