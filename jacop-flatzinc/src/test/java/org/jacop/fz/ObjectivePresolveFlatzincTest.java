/*
 * ObjectivePresolveFlatzincTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Objective presolve in the FlatZinc front end: the objective, expanded through its defining
 * equations and shifted by exactly-one sets, is imposed as a redundant equation. Runs with presolve
 * in checking mode print the same as runs without presolve, and checking mode verifies every
 * solution against the loaded model.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class ObjectivePresolveFlatzincTest {

  @TempDir Path tmp;

  private static final Pattern SHIFTED = Pattern.compile("presolveObjectiveShifted=(\\d+)");
  private static final Pattern EXPANDED = Pattern.compile("presolveObjectiveExpanded=(\\d+)");

  /**
   * An assignment of three tasks to machines, each by an exactly-one set and one by a value literal
   * encoding; the cost goes through intermediate variables as MiniZinc flattens it.
   */
  private static final String ASSIGNMENT =
      """
      var bool: a1:: output_var;
      var bool: a2:: output_var;
      var bool: a3:: output_var;
      var bool: b1:: output_var;
      var bool: b2:: output_var;
      var 1..3: m:: output_var;
      var bool: m1;
      var bool: m2;
      var bool: m3;
      var 0..1: ia1;
      var 0..1: ia2;
      var 0..1: ia3;
      var 0..1: ib1;
      var 0..1: ib2;
      var 0..1: im1;
      var 0..1: im2;
      var 0..1: im3;
      var 0..100: ca:: is_defined_var;
      var 0..100: cb:: is_defined_var;
      var 0..100: cm:: is_defined_var;
      var 0..300: cost:: output_var:: is_defined_var;
      constraint bool_lin_eq([1,1,1],[a1,a2,a3],1);
      constraint bool_lin_eq([1,1],[b1,b2],1);
      constraint int_eq_reif(m,1,m1);
      constraint int_eq_reif(m,2,m2);
      constraint int_eq_reif(m,3,m3);
      constraint bool2int(a1,ia1);
      constraint bool2int(a2,ia2);
      constraint bool2int(a3,ia3);
      constraint bool2int(b1,ib1);
      constraint bool2int(b2,ib2);
      constraint bool2int(m1,im1);
      constraint bool2int(m2,im2);
      constraint bool2int(m3,im3);
      constraint bool_clause([a3,b1],[m2]);
      constraint int_lin_eq([7,9,12,-1],[ia1,ia2,ia3,ca],0):: defines_var(ca);
      constraint int_lin_eq([4,6,-1],[ib1,ib2,cb],0):: defines_var(cb);
      constraint int_lin_eq([5,3,8,-1],[im1,im2,im3,cm],0):: defines_var(cm);
      constraint int_lin_eq([1,1,1,-1],[ca,cb,cm,cost],0):: defines_var(cost);
      solve :: bool_search([a1,a2,a3,b1,b2],input_order,indomain_min,complete) minimize cost;
      """;

  @Test
  void theObjectiveIsExpandedAndShifted() throws IOException {
    String out = FlatzincTestRunner.run(tmp, ASSIGNMENT, "-s", "--presolve", "on");
    assertThat(stat(EXPANDED, out)).isEqualTo(3);
    assertThat(stat(SHIFTED, out)).isEqualTo(3);
    // the cheapest of each set: 7 + 4 + 3, but a3 or b1 or m = 2 is required
    assertThat(out).contains("cost = 14;").contains("==========");
  }

  @Test
  void checkingModePrintsTheSameAsNoPresolve() throws IOException {
    // the search annotation fixes the order, so the improving solutions are the same; free search
    // would choose by domain sizes, which the stronger bound changes
    for (String[] options : List.of(new String[] {"-a"}, new String[] {})) {
      assertThat(run(ASSIGNMENT, "check", options)).isEqualTo(run(ASSIGNMENT, "off", options));
    }
  }

  @Test
  void theRuleCanBeTurnedOff() throws IOException {
    String key = "org.jacop.fz.objectivePresolve";
    System.setProperty(key, "false");
    try {
      String out = FlatzincTestRunner.run(tmp, ASSIGNMENT, "-s", "--presolve", "on");
      assertThat(out).doesNotContain("presolveObjective").contains("cost = 14;");
    } finally {
      System.clearProperty(key);
    }
  }

  /**
   * Random models: exactly-one sets and value literals with random costs, partly through
   * intermediate variables, random clauses, minimised or maximised. All improving solutions and the
   * optimum are the same with presolve in checking mode as without presolve.
   */
  @Test
  void randomModelsGiveTheSameSolutions() throws IOException {
    Random random = new Random(27102026L);
    int shifted = 0;
    for (int run = 0; run < 60; run++) {
      String model = randomModel(random);
      String off = run(model, "off", "-a");
      assertThat(run(model, "check", "-a")).as(model).isEqualTo(off);
      String stats = FlatzincTestRunner.run(tmp, model, "-s", "--presolve", "on");
      if (stat(SHIFTED, stats) > 0) {
        shifted++;
      }
    }
    assertThat(shifted).isGreaterThan(20);
  }

  private static String randomModel(Random r) {
    StringBuilder vars = new StringBuilder();
    StringBuilder cons = new StringBuilder();
    List<String> lits = new ArrayList<>();
    List<String> decisions = new ArrayList<>();
    int sets = 1 + r.nextInt(3);
    for (int s = 0; s < sets; s++) {
      int n = 2 + r.nextInt(3);
      if (r.nextBoolean()) {
        List<String> b = new ArrayList<>();
        for (int i = 0; i < n; i++) {
          String name = "b" + s + "_" + i;
          vars.append("var bool: ").append(name).append(":: output_var;\n");
          b.add(name);
        }
        cons.append("constraint bool_lin_eq([")
            .append(String.join(",", ones(n)))
            .append("],[")
            .append(String.join(",", b))
            .append("],1);\n");
        lits.addAll(b);
        decisions.addAll(b);
      } else {
        String x = "x" + s;
        vars.append("var 0..").append(n - 1).append(": ").append(x).append(":: output_var;\n");
        decisions.add(x);
        int encoded = r.nextInt(4) == 0 ? n - 1 : n;
        for (int v = 0; v < encoded; v++) {
          String name = x + "_" + v;
          vars.append("var bool: ").append(name).append(";\n");
          cons.append("constraint int_eq_reif(")
              .append(x)
              .append(',')
              .append(v)
              .append(',')
              .append(name)
              .append(");\n");
          lits.add(name);
        }
      }
    }
    // the 0/1 integer of every literal
    for (String b : lits) {
      vars.append("var 0..1: i").append(b).append(";\n");
      cons.append("constraint bool2int(").append(b).append(",i").append(b).append(");\n");
    }
    if (r.nextBoolean()) {
      cons.append("constraint bool_clause([")
          .append(lits.get(r.nextInt(lits.size())))
          .append(',')
          .append(lits.get(r.nextInt(lits.size())))
          .append("],[")
          .append(lits.get(r.nextInt(lits.size())))
          .append("]);\n");
    }
    List<String> terms = new ArrayList<>();
    List<Integer> coefs = new ArrayList<>();
    int y = 0;
    for (int start = 0; start < lits.size(); ) {
      int k = Math.min(lits.size() - start, 1 + r.nextInt(4));
      List<String> part = lits.subList(start, start + k);
      start += k;
      if (r.nextBoolean()) {
        String name = "y" + y++;
        vars.append("var -200..200: ").append(name).append(":: is_defined_var;\n");
        List<String> c = new ArrayList<>();
        List<String> v = new ArrayList<>();
        for (String b : part) {
          c.add(String.valueOf(r.nextInt(21) - 5));
          v.add("i" + b);
        }
        c.add("-1");
        v.add(name);
        cons.append("constraint int_lin_eq([")
            .append(String.join(",", c))
            .append("],[")
            .append(String.join(",", v))
            .append("],")
            .append(r.nextInt(7) - 3)
            .append("):: defines_var(")
            .append(name)
            .append(");\n");
        terms.add(name);
        coefs.add(1 + r.nextInt(3));
      } else {
        for (String b : part) {
          terms.add("i" + b);
          coefs.add(r.nextInt(21) - 5);
        }
      }
    }
    vars.append("var -1000..1000: obj:: output_var:: is_defined_var;\n");
    List<String> c = new ArrayList<>();
    for (int coef : coefs) {
      c.add(String.valueOf(coef));
    }
    c.add("-1");
    terms.add("obj");
    cons.append("constraint int_lin_eq([")
        .append(String.join(",", c))
        .append("],[")
        .append(String.join(",", terms))
        .append("],0):: defines_var(obj);\n");
    String search =
        "solve :: int_search(["
            + String.join(",", decisions)
            + "],input_order,indomain_min,complete) "
            + (r.nextBoolean() ? "minimize" : "maximize")
            + " obj;\n";
    return vars.toString() + cons + search;
  }

  private static List<String> ones(int n) {
    List<String> l = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      l.add("1");
    }
    return l;
  }

  private String run(String model, String presolve, String... options) throws IOException {
    String[] args = new String[options.length + 2];
    System.arraycopy(options, 0, args, 0, options.length);
    args[options.length] = "--presolve";
    args[options.length + 1] = presolve;
    return FlatzincTestRunner.run(tmp, model, args);
  }

  private static int stat(Pattern p, String out) {
    Matcher m = p.matcher(out);
    return m.find() ? Integer.parseInt(m.group(1)) : -1;
  }
}
