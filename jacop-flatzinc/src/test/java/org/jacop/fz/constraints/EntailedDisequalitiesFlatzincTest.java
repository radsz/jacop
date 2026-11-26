/*
 * EntailedDisequalitiesFlatzincTest.java
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

package org.jacop.fz.constraints;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.fz.Fz2jacop;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * The disequalities that the declared domains satisfy are removed before the detectors read the
 * model (org.jacop.fz.entailedDisequalities): random models of int_ne and int_lin_ne over domains
 * with holes, some of them true by the domains and some not, must keep the number of solutions
 * found by enumeration.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class EntailedDisequalitiesFlatzincTest {

  @TempDir Path tmp;

  private record Model(String fzn, long solutions, int entailed) {}

  // a constraint a . x != c over the positions of x
  private record Ne(int[] a, int[] x, int c) {}

  private static Model randomModel(Random random) {
    int n = 3 + random.nextInt(2);
    List<int[]> domains = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int lo = random.nextInt(8);
      List<Integer> values = new ArrayList<>();
      for (int v = lo; v <= lo + 3; v++) {
        if (v == lo || random.nextInt(3) > 0) {
          values.add(v);
        }
      }
      domains.add(values.stream().mapToInt(Integer::intValue).toArray());
    }
    List<Ne> ne = new ArrayList<>();
    for (int k = 0; k < 6; k++) {
      int arity = 1 + random.nextInt(3);
      int[] x = random.ints(0, n).distinct().limit(arity).toArray();
      int[] a = new int[x.length];
      for (int j = 0; j < x.length; j++) {
        a[j] = random.nextBoolean() ? 1 + random.nextInt(2) : -1 - random.nextInt(2);
      }
      ne.add(new Ne(a, x, random.nextInt(25) - 10));
    }
    StringBuilder s = new StringBuilder();
    for (int i = 0; i < n; i++) {
      StringBuilder set = new StringBuilder();
      for (int v : domains.get(i)) {
        set.append(set.isEmpty() ? "" : ",").append(v);
      }
      s.append("var {").append(set).append("}: x").append(i).append(":: output_var;\n");
    }
    int entailed = 0;
    for (Ne c : ne) {
      if (c.x().length == 2 && c.a()[0] == 1 && c.a()[1] == -1 && c.c() == 0) {
        s.append("constraint int_ne(x").append(c.x()[0]).append(",x").append(c.x()[1]);
        s.append(");\n");
      } else {
        StringBuilder a = new StringBuilder();
        StringBuilder x = new StringBuilder();
        for (int j = 0; j < c.x().length; j++) {
          a.append(j == 0 ? "" : ",").append(c.a()[j]);
          x.append(j == 0 ? "" : ",").append('x').append(c.x()[j]);
        }
        s.append("constraint int_lin_ne([").append(a).append("],[").append(x).append("],");
        s.append(c.c()).append(");\n");
      }
      if (trueByDomains(c, domains)) {
        entailed++;
      }
    }
    s.append("solve satisfy;\n");

    long solutions = 0;
    int[] pos = new int[n];
    while (true) {
      boolean ok = true;
      for (Ne c : ne) {
        long sum = 0;
        for (int j = 0; j < c.x().length; j++) {
          sum += (long) c.a()[j] * domains.get(c.x()[j])[pos[c.x()[j]]];
        }
        ok &= sum != c.c();
      }
      if (ok) {
        solutions++;
      }
      int i = 0;
      while (i < n && pos[i] == domains.get(i).length - 1) {
        pos[i] = 0;
        i++;
      }
      if (i == n) {
        break;
      }
      pos[i]++;
    }
    return new Model(s.toString(), solutions, entailed);
  }

  // as the pass decides: a unary row by the values of its domain, a longer one by the bounds
  private static boolean trueByDomains(Ne c, List<int[]> domains) {
    if (c.x().length == 1) {
      int a = c.a()[0];
      if (c.c() % a != 0) {
        return true;
      }
      for (int v : domains.get(c.x()[0])) {
        if (v == c.c() / a) {
          return false;
        }
      }
      return true;
    }
    long min = 0;
    long max = 0;
    for (int j = 0; j < c.x().length; j++) {
      int[] d = domains.get(c.x()[j]);
      long lo = (long) c.a()[j] * d[0];
      long hi = (long) c.a()[j] * d[d.length - 1];
      min += Math.min(lo, hi);
      max += Math.max(lo, hi);
    }
    return c.c() < min || c.c() > max;
  }

  @Test
  void solutionsOfRandomDisequalityModels() throws IOException {
    Random random = new Random(Long.getLong("entailedne.seed", 20261121L));
    int trials = Integer.getInteger("entailedne.trials", 40);
    int removed = 0;
    for (int t = 0; t < trials; t++) {
      Model model = randomModel(random);
      String out = run(model.fzn(), "-a", "-debug");
      String context = "trial " + t + "\n" + model.fzn() + out;
      long found = out.lines().filter("----------"::equals).count();
      if (model.solutions() == 0) {
        assertTrue(out.contains("=====UNSATISFIABLE====="), context);
      } else {
        assertEquals(model.solutions(), found, context);
      }
      if (model.entailed() > 0) {
        assertTrue(
            out.contains("% " + model.entailed() + " disequalities true by the domains removed"),
            context);
        removed++;
      }
    }
    assertTrue(removed > 0, "no model had a disequality true by its domains");
  }

  private String run(String model, String... opts) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    List<String> args = new ArrayList<>(List.of(opts));
    args.add(fzn.toString());
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
