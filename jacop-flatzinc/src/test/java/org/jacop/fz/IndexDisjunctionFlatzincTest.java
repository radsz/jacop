/*
 * IndexDisjunctionFlatzincTest.java
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
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks {@link org.jacop.fz.constraints.IndexDisjunctionDetector}: index variables that only pick
 * the position where a relation holds become a disjunction, and get their values back when a
 * solution is printed. Every printed solution is checked against the model as written, and the
 * answer is compared with the model solved without the rewrite.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class IndexDisjunctionFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.indexDisjunction";
  private static final String UNSAT = "=====UNSATISFIABLE=====";
  private static final Pattern VALUE = Pattern.compile("(\\w+) = (-?\\d+);");
  private static final Pattern DISJUNCTIONS = Pattern.compile("indexDisjunctions=(\\d+)");

  @TempDir Path tmp;

  /** An element r = a[k] with a[j] at index value first + j, and the relation of its group. */
  private record Element(String k, String[] a, String r, int first, boolean constants) {}

  /** A relation sum(w * r) op c over the results of one index, op one of le, eq, ne. */
  private record Relation(String op, int[] w, String[] r, int c) {}

  /** A random model and what is needed to check a solution of it. */
  private record Model(
      String fzn, List<Element> elements, List<Relation> relations, List<int[]> notEqual) {}

  @Test
  void antichainRowsNeedTheirOwnPosition() throws IOException {
    // 4 pairwise incomparable vectors in {0,1}^3 do not exist (the width is 3), 3 do
    for (int n = 3; n <= 4; n++) {
      String fzn = antichain(n, 3, 2);
      String on = FlatzincTestRunner.run(tmp, fzn, "--search-statistics");
      assertEquals(n == 4, on.contains(UNSAT), on);
      assertTrue(disjunctions(on) == n * (n - 1), on);
      if (n == 3) {
        Map<String, Integer> v = values(on);
        for (int i = 0; i < n; i++) {
          for (int j = i + 1; j < n; j++) {
            int lo = v.get("lo_" + i + "_" + j);
            int hi = v.get("hi_" + i + "_" + j);
            assertTrue(v.get("x_" + i + "_" + lo) < v.get("x_" + j + "_" + lo), on);
            assertTrue(v.get("x_" + i + "_" + hi) > v.get("x_" + j + "_" + hi), on);
            assertEquals(v.get("x_" + j + "_" + lo), v.get("a_" + i + "_" + j), on);
          }
        }
      }
    }
  }

  @Test
  void randomModelsKeepTheirSolutions() throws IOException {
    Random random = new Random(3);
    int trials = Integer.getInteger("indexDisjunction.trials", 300);
    int fired = 0;
    int unsat = 0;
    for (int trial = 0; trial < trials; trial++) {
      Model model = randomModel(random);
      String on = FlatzincTestRunner.run(tmp, model.fzn(), "--search-statistics");
      String off;
      System.setProperty(PROPERTY, "false");
      try {
        off = FlatzincTestRunner.run(tmp, model.fzn());
      } finally {
        System.clearProperty(PROPERTY);
      }
      String why = "trial " + trial + "\n" + model.fzn() + "\n" + on;
      assertEquals(off.contains(UNSAT), on.contains(UNSAT), why + "\n" + off);
      if (on.contains(UNSAT)) {
        unsat++;
      } else {
        check(model, values(on), why);
      }
      if (disjunctions(on) > 0) {
        fired++;
      }
      String lcg = FlatzincTestRunner.run(tmp, model.fzn(), "--lcg", "off");
      assertEquals(on.contains(UNSAT), lcg.contains(UNSAT), why + "\n" + lcg);
      if (!lcg.contains(UNSAT)) {
        check(model, values(lcg), why + "\n" + lcg);
      }
    }
    assertTrue(fired > trials / 3, "fired " + fired);
    assertTrue(unsat > 0 && unsat < trials, "unsatisfiable " + unsat);
  }

  // the solution satisfies every constraint of the model as written
  private static void check(Model model, Map<String, Integer> v, String why) {
    for (Element e : model.elements()) {
      int k = v.get(e.k());
      int j = k - e.first();
      assertTrue(j >= 0 && j < e.a().length, why);
      assertEquals(value(e.a()[j], v), (int) v.get(e.r()), why);
    }
    for (Relation r : model.relations()) {
      long sum = 0;
      for (int i = 0; i < r.w().length; i++) {
        sum += (long) r.w()[i] * v.get(r.r()[i]);
      }
      boolean holds =
          switch (r.op()) {
            case "le" -> sum <= r.c();
            case "eq" -> sum == r.c();
            default -> sum != r.c();
          };
      assertTrue(holds, why);
    }
    for (int[] ne : model.notEqual()) {
      assertTrue(!v.get("x" + ne[0]).equals(v.get("x" + ne[1])), why);
    }
  }

  private static int value(String atom, Map<String, Integer> v) {
    return atom.startsWith("x") ? v.get(atom) : Integer.parseInt(atom);
  }

  private static Model randomModel(Random random) {
    int nx = 3 + random.nextInt(4);
    int hi = 1 + random.nextInt(3);
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < nx; i++) {
      fzn.append("var 0..").append(hi).append(": x").append(i).append(" :: output_var;\n");
    }
    StringBuilder cs = new StringBuilder();
    List<Element> elements = new ArrayList<>();
    List<Relation> relations = new ArrayList<>();
    List<int[]> notEqual = new ArrayList<>();
    int groups = 1 + random.nextInt(3);
    for (int g = 0; g < groups; g++) {
      int length = 1 + random.nextInt(4);
      int kind = random.nextInt(3);
      int first = kind == 0 ? random.nextInt(3) : 1;
      // the values of k: positions of the arrays, sometimes with a hole, sometimes one outside
      TreeSet<Integer> dom = new TreeSet<>();
      for (int j = 0; j < length; j++) {
        if (random.nextInt(4) > 0) {
          dom.add(first + j);
        }
      }
      if (random.nextInt(8) == 0) {
        dom.add(first + length);
      }
      if (dom.isEmpty()) {
        dom.add(first);
      }
      String k = "k" + g;
      fzn.append("var ").append(set(dom)).append(": ").append(k).append(" :: output_var;\n");
      int m = 1 + random.nextInt(3);
      String[] rs = new String[m];
      int[] w = new int[m];
      for (int i = 0; i < m; i++) {
        String[] a = new String[length];
        boolean constants = kind == 2;
        for (int j = 0; j < length; j++) {
          a[j] =
              constants || random.nextInt(4) == 0
                  ? String.valueOf(random.nextInt(hi + 1))
                  : "x" + random.nextInt(nx);
        }
        rs[i] = "r" + g + "_" + i;
        fzn.append("var 0..").append(hi).append(": ").append(rs[i]).append(" :: output_var;\n");
        Element e = new Element(k, a, rs[i], first, constants);
        elements.add(e);
        String array = "[" + String.join(",", a) + "]";
        if (kind == 0) {
          cs.append("constraint jacop_array_var_int_element_nonshifted(")
              .append(k)
              .append(',')
              .append(array)
              .append(',')
              .append(rs[i])
              .append(',')
              .append(first)
              .append(");\n");
        } else {
          cs.append("constraint ")
              .append(constants ? "array_int_element(" : "array_var_int_element(")
              .append(k)
              .append(',')
              .append(array)
              .append(',')
              .append(rs[i])
              .append(");\n");
        }
        w[i] = random.nextBoolean() ? 1 + random.nextInt(2) : -1 - random.nextInt(2);
      }
      String op = new String[] {"le", "eq", "ne"}[random.nextInt(3)];
      int c = random.nextInt(2 * hi + 1) - hi;
      if (m == 2 && random.nextBoolean()) {
        // int_lt / int_le / int_eq / int_ne
        String name = new String[] {"int_lt", "int_le", "int_eq", "int_ne"}[random.nextInt(4)];
        cs.append("constraint ")
            .append(name)
            .append('(')
            .append(rs[0])
            .append(',')
            .append(rs[1])
            .append(");\n");
        op = name.equals("int_eq") ? "eq" : name.equals("int_ne") ? "ne" : "le";
        w = new int[] {1, -1};
        c = name.equals("int_lt") ? -1 : 0;
      } else {
        StringBuilder ws = new StringBuilder();
        for (int i = 0; i < m; i++) {
          ws.append(i > 0 ? "," : "").append(w[i]);
        }
        cs.append("constraint int_lin_")
            .append(op)
            .append("([")
            .append(ws)
            .append("],[")
            .append(String.join(",", rs))
            .append("],")
            .append(c)
            .append(");\n");
      }
      relations.add(new Relation(op, w, rs, c));
      if (random.nextInt(6) == 0) {
        // a result used once more is left as it is
        cs.append("constraint int_le(").append(rs[0]).append(',').append(hi).append(");\n");
      }
    }
    for (int i = 0; i < nx / 2; i++) {
      int a = random.nextInt(nx);
      int b = random.nextInt(nx);
      if (a != b) {
        cs.append("constraint int_ne(x").append(a).append(",x").append(b).append(");\n");
        notEqual.add(new int[] {a, b});
      }
    }
    return new Model(
        fzn.append(cs).append("solve satisfy;\n").toString(), elements, relations, notEqual);
  }

  private static String set(TreeSet<Integer> values) {
    StringBuilder s = new StringBuilder("{");
    for (int v : values) {
      s.append(s.length() > 1 ? "," : "").append(v);
    }
    return s.append('}').toString();
  }

  /**
   * The Antichain2 model as XCSP3 translations write it: n rows of d values below v, rows in
   * lexicographic order, and for each pair i &lt; j a position lo where row i is smaller and a
   * position hi where it is larger, chosen by index variables.
   */
  private static String antichain(int n, int d, int v) {
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < d; j++) {
        fzn.append("var 0..").append(v - 1).append(": x_").append(i).append('_').append(j);
        fzn.append(" :: output_var;\n");
      }
    }
    StringBuilder cs = new StringBuilder();
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        for (String side : new String[] {"lo", "hi"}) {
          String k = side + "_" + i + "_" + j;
          String a = (side.equals("lo") ? "a_" : "b_") + i + "_" + j;
          String t = "t" + k;
          fzn.append("var 0..").append(d - 1).append(": ").append(k).append(" :: output_var;\n");
          fzn.append("var 0..").append(v - 1).append(": ").append(a).append(" :: output_var;\n");
          fzn.append("var 0..").append(v - 1).append(": ").append(t).append(";\n");
          cs.append("constraint jacop_array_var_int_element_nonshifted(")
              .append(k)
              .append(',')
              .append(row(i, d))
              .append(',')
              .append(t)
              .append(",0);\n");
          cs.append("constraint jacop_array_var_int_element_nonshifted(")
              .append(k)
              .append(',')
              .append(row(j, d))
              .append(',')
              .append(a)
              .append(",0);\n");
          // x[i][k] < x[j][k] at lo, x[i][k] > x[j][k] at hi
          cs.append("constraint int_lin_le(")
              .append(side.equals("lo") ? "[1,-1]" : "[-1,1]")
              .append(",[")
              .append(t)
              .append(',')
              .append(a)
              .append("],-1);\n");
        }
      }
    }
    for (int i = 0; i + 1 < n; i++) {
      cs.append("constraint jacop_lex_lesseq_int(")
          .append(row(i, d))
          .append(',')
          .append(row(i + 1, d))
          .append(");\n");
    }
    return fzn.append(cs).append("solve satisfy;\n").toString();
  }

  private static String row(int i, int d) {
    StringBuilder s = new StringBuilder("[");
    for (int j = 0; j < d; j++) {
      s.append(j > 0 ? "," : "").append("x_").append(i).append('_').append(j);
    }
    return s.append(']').toString();
  }

  private static Map<String, Integer> values(String out) {
    Map<String, Integer> v = new HashMap<>();
    Matcher m = VALUE.matcher(out);
    while (m.find()) {
      v.put(m.group(1), Integer.parseInt(m.group(2)));
    }
    return v;
  }

  private static int disjunctions(String out) {
    Matcher m = DISJUNCTIONS.matcher(out);
    return m.find() ? Integer.parseInt(m.group(1)) : 0;
  }
}
