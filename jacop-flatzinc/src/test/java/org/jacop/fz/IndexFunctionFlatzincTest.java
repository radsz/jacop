/*
 * IndexFunctionFlatzincTest.java
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

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.concurrent.TimeUnit;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random models in the shape MiniZinc gives an option chosen per item with attributes looked up by
 * the choice (the 2020 Challenge stable-goods model): products of two lookups by one index, and
 * clauses of implied comparisons between lookups by two indexes and a variable array. The index
 * function detector must keep every solution and every optimum.
 */
class IndexFunctionFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.indexFunctions";

  @TempDir Path tmp;

  private static String constants(Random random, int n, int lo, int hi) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < n; i++) {
      s.append(i > 0 ? "," : "").append(lo + random.nextInt(hi - lo + 1));
    }
    return s.append(']').toString();
  }

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    List<String> cs = new ArrayList<>();
    int items = 2 + random.nextInt(2);
    int options = 2 + random.nextInt(3);
    int goods = 3;
    // r[g]: the remainders, a variable array indexed by a looked up good
    fzn.append("array [1..").append(goods).append("] of int: VAL = ");
    fzn.append(constants(random, goods, 1, 5)).append(";\n");
    for (int g = 1; g <= goods; g++) {
      fzn.append("var 0..4: r").append(g).append(":: output_var;\n");
    }
    fzn.append("array [1..").append(goods).append("] of var int: R = [r1,r2,r3];\n");
    for (int p = 0; p < items; p++) {
      String good = "G" + p;
      String num = "N" + p;
      fzn.append("array [1..").append(options).append("] of int: ").append(good).append(" = ");
      fzn.append(constants(random, options, 1, goods)).append(";\n");
      fzn.append("array [1..").append(options).append("] of int: ").append(num).append(" = ");
      fzn.append(constants(random, options, 0, 3)).append(";\n");
      fzn.append("var 1..").append(options).append(": pref").append(p).append(":: output_var;\n");
      fzn.append("var 1..").append(goods).append(": g").append(p).append(";\n");
      fzn.append("var 0..3: n").append(p).append(";\n");
      fzn.append("var 0..4: rem").append(p).append(";\n");
      cs.add("jacop_array_var_int_element_nonshifted(pref" + p + "," + good + ",g" + p + ",1)");
      cs.add("jacop_array_var_int_element_nonshifted(pref" + p + "," + num + ",n" + p + ",1)");
      cs.add("jacop_array_var_int_element_nonshifted(g" + p + ",R,rem" + p + ",1)");
      for (int g = 1; g <= goods; g++) {
        String b = "is" + p + "_" + g;
        String i = "i" + p + "_" + g;
        String z = "z" + p + "_" + g;
        fzn.append("var bool: ").append(b).append(";\n");
        fzn.append("var 0..1: ").append(i).append(";\n");
        fzn.append("var 0..3: ").append(z).append(";\n");
        cs.add("int_eq_reif(g" + p + "," + g + "," + b + ")");
        cs.add("bool2int(" + b + "," + i + ")");
        cs.add(
            random.nextBoolean()
                ? "int_times(" + i + ",n" + p + "," + z + ")"
                : "int_times(n" + p + "," + i + "," + z + ")");
      }
    }
    // the usage of each good plus its remainder is 4
    for (int g = 1; g <= goods; g++) {
      StringBuilder vars = new StringBuilder("[");
      StringBuilder ones = new StringBuilder("[");
      for (int p = 0; p < items; p++) {
        vars.append(p > 0 ? "," : "").append('z').append(p).append('_').append(g);
        ones.append(p > 0 ? "," : "").append('1');
      }
      cs.add("int_lin_eq(" + ones + ",1]," + vars + ",r" + g + "],4)");
    }
    // a stability-like clause per pair: one of the implied comparisons holds
    int k = 0;
    for (int p = 0; p < items; p++) {
      for (int q = p + 1; q < items; q++) {
        String b1 = "c" + k++;
        String b2 = "c" + k++;
        String b3 = "c" + k++;
        fzn.append("var bool: ").append(b1).append(";\nvar bool: ").append(b2);
        fzn.append(";\nvar bool: ").append(b3).append(";\n");
        cs.add(
            "int_lin_le_imp([1,-1],[n"
                + p
                + ",rem"
                + q
                + "],"
                + random.nextInt(2)
                + ","
                + b1
                + ")");
        cs.add("int_eq_imp(g" + p + ",g" + q + "," + b2 + ")");
        cs.add(
            random.nextBoolean()
                ? "int_le_imp(n" + q + ",n" + p + "," + b3 + ")"
                : "int_ne_imp(n" + q + "," + random.nextInt(3) + "," + b3 + ")");
        cs.add("bool_clause([" + b1 + "," + b2 + "," + b3 + "],[])");
      }
    }
    if (optimise) {
      fzn.append("var 0..60: obj:: output_var;\n");
      cs.add("int_lin_eq([1,1,1,-1],[r1,r2,r3,obj],0)");
    }
    cs.forEach(s -> fzn.append("constraint ").append(s).append(";\n"));
    fzn.append(optimise ? "solve maximize obj;\n" : "solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void rewritingKeepsAllSolutions() throws IOException {
    Random random = new Random(71);
    int rewritten = 0;
    int unfolded = 0;
    int trials = Integer.getInteger("indexfn.trials", 150);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String on = run(model, true, "-a", "-debug");
      rewritten += on.contains("% index function products: ") ? 1 : 0;
      unfolded += on.contains("unfolded clauses: 0 ") ? 0 : 1;
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model + "\n" + on);
    }
    assertTrue(rewritten > trials / 2, "rewritten " + rewritten);
    assertTrue(unfolded > trials / 2, "unfolded " + unfolded);
  }

  @Test
  void rewritingKeepsOptima() throws IOException {
    Random random = new Random(72);
    int trials = Integer.getInteger("indexfn.trials", 150) / 2;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"));
      for (String[] options :
          List.of(
              new String[] {"--lcg", "off"}, new String[] {"--lcg", "on"}, new String[] {"-f"})) {
        assertEquals(
            expected,
            optimum(run(model, true, options)),
            "trial " + trial + " " + Arrays.toString(options) + "\n" + model);
      }
    }
  }

  /**
   * A disjunction of two precedences whose durations are looked up by the modes of the tasks keeps
   * every comparison open for each combination of modes: unfolding it would replace its one
   * ordering literal by a clause and two reified comparisons per combination (EchoSched).
   */
  @Test
  void disjunctionsWithLookedUpDurationsStayFolded() throws IOException {
    String model =
        """
        var 0..20: s1;
        var 0..20: s2;
        var 1..2: m1;
        var 1..2: m2;
        var {3, 7}: d1 :: var_is_introduced :: is_defined_var;
        var {2, 5}: d2 :: var_is_introduced :: is_defined_var;
        var bool: b1 :: var_is_introduced :: is_defined_var;
        var bool: b2 :: var_is_introduced :: is_defined_var;
        constraint array_int_element(m1, [3, 7], d1) :: defines_var(d1);
        constraint array_int_element(m2, [5, 2], d2) :: defines_var(d2);
        constraint int_lin_le_imp([1, 1, -1], [s1, d1, s2], 0, b1) :: defines_var(b1);
        constraint int_lin_le_imp([1, 1, -1], [s2, d2, s1], 0, b2) :: defines_var(b2);
        constraint bool_clause([b1, b2], []);
        solve satisfy;
        """;
    String on = run(model, true, "-a", "-debug");
    assertTrue(on.contains("unfolded clauses: 0 "), on);
    assertEquals(solutions(run(model, false, "-a")), solutions(on));
  }

  /**
   * The unfolded clauses of two items compare the remainders of different goods with the same
   * bound. Each comparison needs a 0/1 variable of its own even when the two remainders have the
   * same identity hash code, which a JVM run with {@code -XX:hashCode=2} gives every object: the
   * model is solved there in a JVM of its own.
   */
  @Test
  void comparisonsOfVariablesWithEqualHashCodesKeepTheirOwnLiterals()
      throws IOException, InterruptedException {
    String model =
        """
        array [1..3] of int: VAL = [2,4,3];
        var 0..4: r1:: output_var;
        var 0..4: r2:: output_var;
        var 0..4: r3:: output_var;
        array [1..3] of var int: R = [r1,r2,r3];
        array [1..3] of int: G0 = [2,2,3];
        array [1..3] of int: N0 = [0,3,2];
        var 1..3: pref0:: output_var;
        var 1..3: g0;
        var 0..3: n0;
        var 0..4: rem0;
        var bool: is0_1;
        var 0..1: i0_1;
        var 0..3: z0_1;
        var bool: is0_2;
        var 0..1: i0_2;
        var 0..3: z0_2;
        var bool: is0_3;
        var 0..1: i0_3;
        var 0..3: z0_3;
        array [1..3] of int: G1 = [1,1,2];
        array [1..3] of int: N1 = [2,1,3];
        var 1..3: pref1:: output_var;
        var 1..3: g1;
        var 0..3: n1;
        var 0..4: rem1;
        var bool: is1_1;
        var 0..1: i1_1;
        var 0..3: z1_1;
        var bool: is1_2;
        var 0..1: i1_2;
        var 0..3: z1_2;
        var bool: is1_3;
        var 0..1: i1_3;
        var 0..3: z1_3;
        array [1..3] of int: G2 = [1,3,3];
        array [1..3] of int: N2 = [0,0,2];
        var 1..3: pref2:: output_var;
        var 1..3: g2;
        var 0..3: n2;
        var 0..4: rem2;
        var bool: is2_1;
        var 0..1: i2_1;
        var 0..3: z2_1;
        var bool: is2_2;
        var 0..1: i2_2;
        var 0..3: z2_2;
        var bool: is2_3;
        var 0..1: i2_3;
        var 0..3: z2_3;
        var bool: c0;
        var bool: c1;
        var bool: c2;
        var bool: c3;
        var bool: c4;
        var bool: c5;
        var bool: c6;
        var bool: c7;
        var bool: c8;
        constraint jacop_array_var_int_element_nonshifted(pref0,G0,g0,1);
        constraint jacop_array_var_int_element_nonshifted(pref0,N0,n0,1);
        constraint jacop_array_var_int_element_nonshifted(g0,R,rem0,1);
        constraint int_eq_reif(g0,1,is0_1);
        constraint bool2int(is0_1,i0_1);
        constraint int_times(n0,i0_1,z0_1);
        constraint int_eq_reif(g0,2,is0_2);
        constraint bool2int(is0_2,i0_2);
        constraint int_times(n0,i0_2,z0_2);
        constraint int_eq_reif(g0,3,is0_3);
        constraint bool2int(is0_3,i0_3);
        constraint int_times(n0,i0_3,z0_3);
        constraint jacop_array_var_int_element_nonshifted(pref1,G1,g1,1);
        constraint jacop_array_var_int_element_nonshifted(pref1,N1,n1,1);
        constraint jacop_array_var_int_element_nonshifted(g1,R,rem1,1);
        constraint int_eq_reif(g1,1,is1_1);
        constraint bool2int(is1_1,i1_1);
        constraint int_times(i1_1,n1,z1_1);
        constraint int_eq_reif(g1,2,is1_2);
        constraint bool2int(is1_2,i1_2);
        constraint int_times(i1_2,n1,z1_2);
        constraint int_eq_reif(g1,3,is1_3);
        constraint bool2int(is1_3,i1_3);
        constraint int_times(n1,i1_3,z1_3);
        constraint jacop_array_var_int_element_nonshifted(pref2,G2,g2,1);
        constraint jacop_array_var_int_element_nonshifted(pref2,N2,n2,1);
        constraint jacop_array_var_int_element_nonshifted(g2,R,rem2,1);
        constraint int_eq_reif(g2,1,is2_1);
        constraint bool2int(is2_1,i2_1);
        constraint int_times(n2,i2_1,z2_1);
        constraint int_eq_reif(g2,2,is2_2);
        constraint bool2int(is2_2,i2_2);
        constraint int_times(i2_2,n2,z2_2);
        constraint int_eq_reif(g2,3,is2_3);
        constraint bool2int(is2_3,i2_3);
        constraint int_times(i2_3,n2,z2_3);
        constraint int_lin_eq([1,1,1,1],[z0_1,z1_1,z2_1,r1],4);
        constraint int_lin_eq([1,1,1,1],[z0_2,z1_2,z2_2,r2],4);
        constraint int_lin_eq([1,1,1,1],[z0_3,z1_3,z2_3,r3],4);
        constraint int_lin_le_imp([1,-1],[n0,rem1],1,c0);
        constraint int_eq_imp(g0,g1,c1);
        constraint int_le_imp(n1,n0,c2);
        constraint bool_clause([c0,c1,c2],[]);
        constraint int_lin_le_imp([1,-1],[n0,rem2],0,c3);
        constraint int_eq_imp(g0,g2,c4);
        constraint int_ne_imp(n2,0,c5);
        constraint bool_clause([c3,c4,c5],[]);
        constraint int_lin_le_imp([1,-1],[n1,rem2],1,c6);
        constraint int_eq_imp(g1,g2,c7);
        constraint int_ne_imp(n2,2,c8);
        constraint bool_clause([c6,c7,c8],[]);
        solve satisfy;
        """;
    Path fzn = tmp.resolve("collide.fzn");
    Files.writeString(fzn, model);
    Path java = Path.of(System.getProperty("java.home"), "bin", "java");
    Process child =
        new ProcessBuilder(
                java.toString(),
                "-XX:+UnlockExperimentalVMOptions",
                "-XX:hashCode=2",
                "-cp",
                System.getProperty("java.class.path"),
                Fz2jacop.class.getName(),
                "-a",
                fzn.toString())
            .redirectErrorStream(true)
            .start();
    String colliding = new String(child.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
    assertTrue(child.waitFor(60, TimeUnit.SECONDS), colliding);
    assertEquals(solutions(run(model, false, "-a")), solutions(colliding), colliding);
  }

  private static int solutions(String out) {
    return out.split("----------", -1).length - 1;
  }

  private static String optimum(String out) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out);
    return last;
  }

  private String run(String model, boolean detect, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, String.valueOf(detect));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
