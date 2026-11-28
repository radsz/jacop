/*
 * XcspReaderTest.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in material modified versions of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.xcsp;

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
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.jacop.fz.Fz2jacop;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the native XCSP3 reader construct by construct: each small instance is read, solved for
 * all solutions and compared with the solutions of the relation enumerated over the variables.
 */
@Timeout(120)
class XcspReaderTest {

  @TempDir Path tmp;

  private static final Pattern INT = Pattern.compile("-?\\d+|true|false");

  /** Variables x0..x(n-1) with the domain lo..hi each. */
  private static String vars(int n, int lo, int hi) {
    return "<array id=\"x\" size=\"[" + n + "]\"> " + lo + ".." + hi + " </array>";
  }

  private void check(
      String variables, String constraints, int n, int lo, int hi, Predicate<int[]> relation)
      throws IOException {
    int[][] doms = new int[n][];
    for (int i = 0; i < n; i++) {
      doms[i] = new int[hi - lo + 1];
      for (int v = lo; v <= hi; v++) {
        doms[i][v - lo] = v;
      }
    }
    check(variables, constraints, doms, relation);
  }

  private void check(String variables, String constraints, int[][] doms, Predicate<int[]> relation)
      throws IOException {
    String xml =
        "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            + variables
            + "</variables><constraints>"
            + constraints
            + "</constraints></instance>";
    Set<String> expected = new TreeSet<>();
    enumerate(doms, new int[doms.length], 0, relation, expected);
    Set<String> actual = solve(xml);
    assertEquals(expected, actual, "solutions of\n" + xml);
  }

  private static void enumerate(
      int[][] doms, int[] t, int i, Predicate<int[]> relation, Set<String> out) {
    if (i == doms.length) {
      if (relation.test(t)) {
        out.add(Arrays.toString(t));
      }
      return;
    }
    for (int v : doms[i]) {
      t[i] = v;
      enumerate(doms, t, i + 1, relation, out);
    }
  }

  private Set<String> solve(String xml) throws IOException {
    Path in = tmp.resolve("model.xml");
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(in, xml, StandardCharsets.UTF_8);
    PrintStream originalOut = System.out;
    ByteArrayOutputStream read = new ByteArrayOutputStream();
    try {
      System.setOut(new PrintStream(read, true, StandardCharsets.UTF_8));
      Xcsp2jacop.run(new String[] {"--fzn", fzn.toString(), "--fzn-only", in.toString()});
    } finally {
      System.setOut(originalOut);
    }
    assertTrue(Files.exists(fzn), "no FlatZinc model: " + read.toString(StandardCharsets.UTF_8));
    ByteArrayOutputStream captured = new ByteArrayOutputStream();
    try {
      System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
      new Fz2jacop().callMain(new String[] {"-a", fzn.toString()});
    } finally {
      System.setOut(originalOut);
    }
    List<String> lines = captured.toString(StandardCharsets.UTF_8).lines().toList();
    Set<String> solutions = new TreeSet<>();
    if (lines.contains("=====UNSATISFIABLE=====")) {
      return solutions;
    }
    assertTrue(
        lines.contains("=========="),
        "search did not complete: " + lines + "\n" + Files.readString(fzn));
    List<Integer> current = new ArrayList<>();
    for (String line : lines) {
      String l = line.trim();
      if (l.equals("----------")) {
        solutions.add(current.toString());
        current.clear();
      } else if (l.contains("=") && !l.startsWith("=") && !l.startsWith("%")) {
        String value = l.substring(l.indexOf('=') + 1);
        if (value.contains("[")) {
          value = value.substring(value.indexOf('['));
        }
        Matcher m = INT.matcher(value);
        while (m.find()) {
          String g = m.group();
          current.add(g.equals("true") ? 1 : g.equals("false") ? 0 : Integer.parseInt(g));
        }
      }
    }
    return solutions;
  }

  @Test
  void unaryBounds() throws IOException {
    // ge(x,1) of a variable 0..3 posted alone and inside a disjunction
    check(
        vars(2, 0, 3),
        "<intension> ge(x[0],1) </intension><intension> or(eq(x[0],3),ge(x[1],2)) </intension>",
        2,
        0,
        3,
        t -> t[0] >= 1 && (t[0] == 3 || t[1] >= 2));
    check(
        vars(2, -3, 3),
        "<intension> or(gt(mul(-2,x[0]),3),le(mul(3,x[1]),-4)) </intension>",
        2,
        -3,
        3,
        t -> -2 * t[0] > 3 || 3 * t[1] <= -4);
    check(
        vars(2, -3, 3),
        "<intension> ge(mul(-2,x[0]),3) </intension><intension> lt(add(x[1],x[1]),-1) </intension>",
        2,
        -3,
        3,
        t -> -2 * t[0] >= 3 && 2 * t[1] < -1);
  }

  @Test
  void arithmetic() throws IOException {
    check(
        vars(3, -3, 3),
        "<intension> eq(x[2],mod(x[0],x[1])) </intension>",
        3,
        -3,
        3,
        t -> t[1] != 0 && t[2] == t[0] % t[1]);
    check(
        vars(3, -3, 3),
        "<intension> eq(x[2],div(x[0],x[1])) </intension>",
        3,
        -3,
        3,
        t -> t[1] != 0 && t[2] == t[0] / t[1]);
    check(
        vars(3, -3, 3),
        "<intension> eq(dist(x[0],x[1]),abs(x[2])) </intension>",
        3,
        -3,
        3,
        t -> Math.abs(t[0] - t[1]) == Math.abs(t[2]));
    check(
        vars(3, -2, 3),
        "<intension> le(add(mul(x[0],x[1]),sqr(x[2])),2) </intension>",
        3,
        -2,
        3,
        t -> t[0] * t[1] + t[2] * t[2] <= 2);
    check(
        vars(3, -2, 3),
        "<intension> eq(x[0],max(x[1],x[2],1)) </intension>",
        3,
        -2,
        3,
        t -> t[0] == Math.max(Math.max(t[1], t[2]), 1));
    check(
        vars(3, -2, 3),
        "<intension> eq(x[0],if(lt(x[1],x[2]),x[1],add(x[2],1))) </intension>",
        3,
        -2,
        3,
        t -> t[0] == (t[1] < t[2] ? t[1] : t[2] + 1));
    check(
        vars(2, -2, 2),
        "<intension> eq(pow(x[0],2),add(x[1],2)) </intension>",
        2,
        -2,
        2,
        t -> t[0] * t[0] == t[1] + 2);
  }

  @Test
  void logic() throws IOException {
    check(
        vars(3, 0, 2),
        "<intension> imp(eq(x[0],1),and(ne(x[1],x[2]),in(x[2],set(0,2)))) </intension>",
        3,
        0,
        2,
        t -> t[0] != 1 || t[1] != t[2] && (t[2] == 0 || t[2] == 2));
    check(
        vars(3, 0, 2),
        "<intension> xor(eq(x[0],1),lt(x[1],x[2]),notin(x[0],set(2))) </intension>",
        3,
        0,
        2,
        t -> (t[0] == 1 ^ t[1] < t[2] ^ t[0] != 2));
    check(
        vars(3, 0, 2),
        "<intension> iff(eq(x[0],1),lt(x[1],x[2])) </intension>",
        3,
        0,
        2,
        t -> t[0] == 1 == t[1] < t[2]);
    check(
        vars(3, 0, 1),
        "<intension> eq(add(x[0],x[1]),x[2]) </intension>",
        3,
        0,
        1,
        t -> t[0] + t[1] == t[2]);
    check(
        vars(3, 0, 1),
        "<intension> or(x[0],not(x[1]),and(x[2],x[0])) </intension>",
        3,
        0,
        1,
        t -> t[0] == 1 || t[1] == 0);
    check(
        vars(3, 0, 2),
        "<intension> eq(x[0],x[1],x[2]) </intension>",
        3,
        0,
        2,
        t -> t[0] == t[1] && t[1] == t[2]);
  }

  @Test
  void naryComparisonsInLiterals() throws IOException {
    // RotatingRostering of XCSP 2025
    check(
        vars(4, 0, 2),
        "<intension> imp(eq(x[0],x[1],x[2]),ne(x[0],x[3])) </intension>",
        4,
        0,
        2,
        t -> !(t[0] == t[1] && t[1] == t[2]) || t[0] != t[3]);
    check(
        vars(4, 0, 2),
        "<group><intension> imp(eq(%0,%1,%2),ne(%0,%3)) </intension><args> x[0] x[1] x[2] x[3] </args>"
            + "<args> x[1] x[2] x[3] x[0] </args></group>",
        4,
        0,
        2,
        t ->
            (!(t[0] == t[1] && t[1] == t[2]) || t[0] != t[3])
                && (!(t[1] == t[2] && t[2] == t[3]) || t[1] != t[0]));
  }

  /** A domain beyond JaCoP's integer range is cut, so no UNSATISFIABLE or OPTIMUM is claimed. */
  @Test
  void clippedDomainsClaimNoProof() throws IOException {
    String csp =
        "<instance format=\"XCSP3\" type=\"CSP\"><variables><var id=\"x\"> 0..9999999999 </var></variables>"
            + "<constraints><intension> gt(x,1000000000) </intension></constraints></instance>";
    assertTrue(competitionOutput(csp).contains("s UNKNOWN"), competitionOutput(csp));
    String cop =
        "<instance format=\"XCSP3\" type=\"COP\"><variables><var id=\"x\"> 0..9999999999 </var></variables>"
            + "<constraints><intension> lt(x,5000000000) </intension></constraints><objectives><minimize> x </minimize></objectives></instance>";
    String out = competitionOutput(cop);
    assertTrue(out.contains("s SATISFIABLE") && out.contains("o 0"), out);
  }

  private String competitionOutput(String xml) throws IOException {
    Path in = tmp.resolve("model.xml");
    Files.writeString(in, xml, StandardCharsets.UTF_8);
    PrintStream originalOut = System.out;
    ByteArrayOutputStream captured = new ByteArrayOutputStream();
    try {
      System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
      Xcsp2jacop.run(new String[] {"-t", "10000", in.toString()});
    } finally {
      System.setOut(originalOut);
    }
    return captured.toString(StandardCharsets.UTF_8);
  }

  @Test
  void extension() throws IOException {
    check(
        vars(3, 0, 2),
        "<extension><list> x[] </list><supports> (0,*,1)(2,1,*)(1,1,1) </supports></extension>",
        3,
        0,
        2,
        t ->
            t[0] == 0 && t[2] == 1
                || t[0] == 2 && t[1] == 1
                || t[0] == 1 && t[1] == 1 && t[2] == 1);
    // rows outside the domains are dropped and the domains narrowed to the columns
    check(
        vars(3, 0, 3),
        "<intension> eq(x[0],1) </intension><group><extension><list> %0 %1 </list>"
            + "<supports> (0,1)(1,2)(1,3)(2,0)(3,3)(2,*) </supports>"
            + "</extension><args> x[0] x[1] </args><args> x[1] x[2] </args></group>",
        3,
        0,
        3,
        t -> t[0] == 1 && (t[1] == 2 || t[1] == 3) && (t[1] == 2 || t[2] == 3));
    check(
        vars(3, 0, 2),
        "<extension><list> x[] </list><conflicts> (0,*,1)(2,1,2) </conflicts></extension>",
        3,
        0,
        2,
        t -> !(t[0] == 0 && t[2] == 1) && !(t[0] == 2 && t[1] == 1 && t[2] == 2));
    check(
        vars(2, 0, 5),
        "<extension><list> x[0] </list><supports> 1 3..4 </supports></extension>",
        2,
        0,
        5,
        t -> t[0] == 1 || t[0] == 3 || t[0] == 4);
  }

  @Test
  void sumsAndCounts() throws IOException {
    check(
        vars(4, 0, 3),
        "<sum><list> x[] </list><coeffs> 1x2 2 -1 </coeffs><condition> (in,2..4) </condition></sum>",
        4,
        0,
        3,
        t -> t[0] + t[1] + 2 * t[2] - t[3] >= 2 && t[0] + t[1] + 2 * t[2] - t[3] <= 4);
    check(
        vars(4, 0, 3),
        "<count><list> x[0..2] </list><values> 1 2 </values><condition> (eq,x[3]) </condition></count>",
        4,
        0,
        3,
        t ->
            (t[0] == 1 || t[0] == 2 ? 1 : 0)
                    + (t[1] == 1 || t[1] == 2 ? 1 : 0)
                    + (t[2] == 1 || t[2] == 2 ? 1 : 0)
                == t[3]);
    check(
        vars(4, 0, 3),
        "<count><list> eq(x[0],add(x[1],1)) lt(x[2],x[1]) </list><values> 1 </values><condition> (eq,x[3]) </condition></count>",
        4,
        0,
        3,
        t -> (t[0] == t[1] + 1 ? 1 : 0) + (t[2] < t[1] ? 1 : 0) == t[3]);
    check(
        vars(4, 0, 3),
        "<nValues><list> x[0..2] </list><condition> (eq,x[3]) </condition></nValues>",
        4,
        0,
        3,
        t -> Arrays.stream(t, 0, 3).distinct().count() == t[3]);
    check(
        vars(4, 0, 2),
        "<cardinality><list> x[0..2] </list><values closed=\"true\"> 0 1 </values><occurs> x[3] 1 </occurs></cardinality>",
        4,
        0,
        2,
        t ->
            Arrays.stream(t, 0, 3).allMatch(v -> v <= 1)
                && Arrays.stream(t, 0, 3).filter(v -> v == 0).count() == t[3]
                && Arrays.stream(t, 0, 3).filter(v -> v == 1).count() == 1);
  }

  @Test
  void globals() throws IOException {
    check(
        vars(3, 0, 2),
        "<allDifferent> x[] </allDifferent>",
        3,
        0,
        2,
        t -> t[0] != t[1] && t[1] != t[2] && t[0] != t[2]);
    check(
        vars(3, 0, 2),
        "<allDifferent><list> x[] </list><except> 0 </except></allDifferent>",
        3,
        0,
        2,
        t ->
            (t[0] == 0 || t[1] == 0 || t[0] != t[1])
                && (t[1] == 0 || t[2] == 0 || t[1] != t[2])
                && (t[0] == 0 || t[2] == 0 || t[0] != t[2]));
    check(
        vars(3, 0, 2),
        "<ordered><list> x[] </list><operator> le </operator></ordered>",
        3,
        0,
        2,
        t -> t[0] <= t[1] && t[1] <= t[2]);
    check(
        vars(4, 0, 2),
        "<maximum><list> x[0..2] </list><condition> (eq,x[3]) </condition></maximum>",
        4,
        0,
        2,
        t -> Math.max(t[0], Math.max(t[1], t[2])) == t[3]);
    check(
        vars(4, 0, 2),
        "<element><list startIndex=\"0\"> x[0..2] </list><index> x[3] </index><value> 1 </value></element>",
        4,
        0,
        2,
        t -> t[t[3]] == 1);
    check(
        vars(4, 0, 3),
        "<element><list> x[0..2] </list><value> x[3] </value></element>",
        4,
        0,
        3,
        t -> t[0] == t[3] || t[1] == t[3] || t[2] == t[3]);
    check(
        vars(4, 0, 1),
        "<lex><list> x[0..1] </list><list> x[2..3] </list><operator> lt </operator></lex>",
        4,
        0,
        1,
        t -> t[0] < t[2] || t[0] == t[2] && t[1] < t[3]);
    check(
        vars(6, 0, 2),
        "<lex><list> x[0..1] </list><list> x[2..3] </list><list> x[4..5] </list><operator> le </operator></lex>",
        6,
        0,
        2,
        t -> Arrays.compare(t, 0, 2, t, 2, 4) <= 0 && Arrays.compare(t, 2, 4, t, 4, 6) <= 0);
    check(
        "<array id=\"y\" size=\"[2][3]\"> 0..1 </array>",
        "<lex><matrix> y[][] </matrix><operator> lt </operator></lex>",
        6,
        0,
        1,
        t ->
            Arrays.compare(t, 0, 3, t, 3, 6) < 0
                && Arrays.compare(new int[] {t[0], t[3]}, new int[] {t[1], t[4]}) < 0
                && Arrays.compare(new int[] {t[1], t[4]}, new int[] {t[2], t[5]}) < 0);
    check(vars(3, 0, 2), "<circuit> x[] </circuit>", 3, 0, 2, XcspReaderTest::subcircuit);
    check(
        vars(4, 0, 1),
        "<channel><list> x[0..1] </list><list> x[2..3] </list></channel>",
        4,
        0,
        1,
        t -> t[t[0] + 2] == 0 && t[t[1] + 2] == 1);
    check(
        vars(4, 0, 1),
        "<regular><list> x[] </list><transitions> (a,0,a)(a,1,b)(b,0,a) </transitions><start> a </start><final> a b </final></regular>",
        4,
        0,
        1,
        t -> !(t[0] == 1 && t[1] == 1) && !(t[1] == 1 && t[2] == 1) && !(t[2] == 1 && t[3] == 1));
    check(
        vars(3, 0, 1),
        "<mdd><list> x[] </list><transitions> (r,0,n)(r,1,m)(n,1,t1)(m,0,t1)(t1,0,t)(t1,1,t) </transitions></mdd>",
        3,
        0,
        1,
        t -> t[0] != t[1]);
    check(
        vars(3, 0, 2),
        "<instantiation><list> x[0] x[2] </list><values> 1 0 </values></instantiation>",
        3,
        0,
        2,
        t -> t[0] == 1 && t[2] == 0);
  }

  @Test
  void halfReifiedClauses() throws IOException {
    // literals only in clauses are half reified; the same comparison is also used fully
    check(
        vars(3, 0, 2),
        "<intension> or(lt(x[0],x[1]),eq(add(x[1],x[2]),3),ne(x[0],x[2])) </intension>"
            + "<intension> imp(ge(x[0],x[1]),gt(x[2],sub(x[0],x[1]))) </intension>"
            + "<intension> iff(lt(x[0],x[1]),ne(x[1],x[2])) </intension>",
        3,
        0,
        2,
        t ->
            (t[0] < t[1] || t[1] + t[2] == 3 || t[0] != t[2])
                && (t[0] < t[1] || t[2] > t[0] - t[1])
                && (t[0] < t[1]) == (t[1] != t[2]));
  }

  @Test
  void halfReifiedUnaryLiterals() throws IOException {
    check(
        vars(3, -2, 3),
        "<intension> or(ne(x[0],1),eq(x[1],0),gt(mul(-3,x[2]),-4)) </intension>"
            + "<intension> or(eq(x[0],1),le(x[1],-1),ne(x[2],2)) </intension>"
            + "<intension> or(lt(x[0],0),ge(mul(2,x[1]),3)) </intension>",
        3,
        -2,
        3,
        t ->
            (t[0] != 1 || t[1] == 0 || -3 * t[2] > -4)
                && (t[0] == 1 || t[1] <= -1 || t[2] != 2)
                && (t[0] < 0 || 2 * t[1] >= 3));
  }

  @Test
  void halfReifiedSums() throws IOException {
    // WordDesign of XCSP 2023: comparisons in a sum bounded on one side
    check(
        vars(4, 0, 2),
        "<sum><list> ne(x[0],x[1]) ne(x[1],x[2]) eq(x[2],x[3]) lt(x[0],x[3]) </list><coeffs> 1 2 -1 1 </coeffs>"
            + "<condition> (ge,2) </condition></sum>"
            + "<sum><list> eq(x[0],x[2]) gt(x[1],x[3]) </list><condition> (le,1) </condition></sum>",
        4,
        0,
        2,
        t ->
            (t[0] != t[1] ? 1 : 0)
                        + 2 * (t[1] != t[2] ? 1 : 0)
                        - (t[2] == t[3] ? 1 : 0)
                        + (t[0] < t[3] ? 1 : 0)
                    >= 2
                && (t[0] == t[2] ? 1 : 0) + (t[1] > t[3] ? 1 : 0) <= 1);
  }

  @Test
  void matrixElement() throws IOException {
    // a constant matrix (SEDF of XCSP 2025) and one of variables
    check(
        vars(3, 0, 3),
        "<element><matrix> (1,2,3)(2,0,1) </matrix><index> x[0] x[1] </index><value> x[2] </value></element>",
        3,
        0,
        3,
        t -> t[0] <= 1 && t[1] <= 2 && new int[][] {{1, 2, 3}, {2, 0, 1}}[t[0]][t[1]] == t[2]);
    check(
        vars(4, 0, 2),
        "<element><matrix startRowIndex=\"1\"> (x[2],1)(2,x[3]) </matrix><index> x[0] x[1] </index>"
            + "<condition> (ge,2) </condition></element>",
        4,
        0,
        2,
        t -> t[0] >= 1 && t[1] <= 1 && new int[][] {{t[2], 1}, {2, t[3]}}[t[0] - 1][t[1]] >= 2);
  }

  @Test
  void scheduling() throws IOException {
    check(
        vars(3, 0, 3),
        "<noOverlap><origins> x[] </origins><lengths> 2 1 1 </lengths></noOverlap>",
        3,
        0,
        3,
        t ->
            disjoint(t[0], 2, t[1], 1) && disjoint(t[0], 2, t[2], 1) && disjoint(t[1], 1, t[2], 1));
    check(
        vars(3, 0, 3),
        "<cumulative><origins> x[] </origins><lengths> 2 1 2 </lengths><heights> 1 2 1 </heights><condition> (le,2) </condition></cumulative>",
        3,
        0,
        3,
        t -> cumulative(t, new int[] {2, 1, 2}, new int[] {1, 2, 1}, 2));
  }

  @Test
  void groupsAndSlides() throws IOException {
    check(
        vars(4, 0, 3),
        "<group><intension> lt(%0,%1) </intension><args> x[0] x[1] </args><args> x[2] x[3] </args></group>",
        4,
        0,
        3,
        t -> t[0] < t[1] && t[2] < t[3]);
    check(
        vars(4, 0, 3),
        "<slide><list> x[] </list><intension> ne(%0,%1) </intension></slide>",
        4,
        0,
        3,
        t -> t[0] != t[1] && t[1] != t[2] && t[2] != t[3]);
    check(
        vars(3, 0, 2),
        "<slide circular=\"true\"><list> x[] </list><intension> ne(%0,%1) </intension></slide>",
        3,
        0,
        2,
        t -> t[0] != t[1] && t[1] != t[2] && t[2] != t[0]);
    check(
        vars(4, 0, 2),
        "<group><sum><list> %... </list><condition> (eq,%0) </condition></sum><args> x[0] x[1] x[2] </args></group>",
        4,
        0,
        2,
        t -> t[1] + t[2] == t[0]);
  }

  private static boolean disjoint(int s1, int d1, int s2, int d2) {
    return s1 + d1 <= s2 || s2 + d2 <= s1;
  }

  private static boolean cumulative(int[] s, int[] d, int[] h, int cap) {
    for (int time = -10; time < 20; time++) {
      int load = 0;
      for (int i = 0; i < s.length; i++) {
        if (s[i] <= time && time < s[i] + d[i]) {
          load += h[i];
        }
      }
      if (load > cap) {
        return false;
      }
    }
    return true;
  }

  // XCSP3 circuit: a subcircuit with at least one node not a loop
  private static boolean subcircuit(int[] t) {
    int nonLoop = -1;
    for (int i = 0; i < t.length; i++) {
      if (t[i] != i) {
        nonLoop = i;
      }
    }
    if (nonLoop < 0) {
      return false;
    }
    int len = 0;
    int i = nonLoop;
    do {
      i = t[i];
      len++;
    } while (i != nonLoop && len <= t.length);
    int moved = 0;
    for (int k = 0; k < t.length; k++) {
      if (t[k] != k) {
        moved++;
      }
    }
    return i == nonLoop && len == moved;
  }

  /**
   * An XCSP3 identifier may be a name the translation generates for the output array or a table:
   * the generated names keep clear of it, so the one solution is printed with the right values.
   */
  @Test
  void identifiersOfGeneratedNamesKeepTheirValues() throws IOException {
    String xml =
        "<instance format=\"XCSP3\" type=\"CSP\"><variables><var id=\"XCSP_ARRAY_0_\"> 0..3 </var>"
            + "<array id=\"x\" size=\"[2]\"> 0..3 </array><var id=\"T_XCSP_0_\"> 0..3 </var></variables>"
            + "<constraints><intension> lt(XCSP_ARRAY_0_,x[0]) </intension>"
            + "<extension><list> x[0] x[1] T_XCSP_0_ </list><supports> (1,2,3)(2,0,1)(3,3,3) </supports></extension>"
            + "<intension> ne(x[1],T_XCSP_0_) </intension><intension> eq(XCSP_ARRAY_0_,1) </intension>"
            + "</constraints></instance>";
    String out = competitionOutput(xml);
    assertTrue(out.contains("s SATISFIABLE") && out.contains("<values> 1 2 0 1 </values>"), out);
  }

  /**
   * A matrix element whose column index has no value in the column range is unsatisfiable: the
   * constant matrix was read as a table over the index domains as they were, out of the matrix.
   */
  @Test
  void matrixElementWithAnIndexOutOfRangeIsUnsatisfiable() throws IOException {
    String xml =
        "<instance format=\"XCSP3\" type=\"CSP\"><variables><array id=\"x\" size=\"[3]\"> 0..1 </array>"
            + "</variables><constraints><element><matrix startColIndex=\"2\"> (-2) </matrix>"
            + "<index> x[0] x[1] </index><value> x[2] </value></element></constraints></instance>";
    String out = competitionOutput(xml);
    assertTrue(out.contains("s UNSATISFIABLE"), out);
  }

  /**
   * The power of a base that can only be 0 is 1 when the exponent is 0: the result was given the
   * domain 0..0, so the instance was unsatisfiable.
   */
  @Test
  void powerOfZeroToTheZeroIsOne() throws IOException {
    String xml =
        "<instance format=\"XCSP3\" type=\"CSP\"><variables><var id=\"x\"> 0 1 3 </var></variables>"
            + "<constraints><intension> eq(pow(0,x),1) </intension></constraints></instance>";
    String out = competitionOutput(xml);
    assertTrue(out.contains("s SATISFIABLE") && out.contains("<values> 0 </values>"), out);
  }

  /**
   * The tuples of a table over symbolic variables hold symbols: the letters were dropped as
   * separators, so supports became a table without rows (unsatisfiable) and conflicts were
   * entailed.
   */
  @Test
  void symbolicTablesReadTheirSymbols() throws IOException {
    String vars =
        "<var id=\"p\" type=\"symbolic\"> r g b </var><var id=\"q\" type=\"symbolic\"> g b </var>";
    String supports =
        "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            + vars
            + "</variables><constraints><extension><list> p q </list><supports> (r,g)(g,b) </supports>"
            + "</extension><intension> eq(p,g) </intension></constraints></instance>";
    String out = competitionOutput(supports);
    assertTrue(out.contains("s SATISFIABLE") && out.contains("<values> g b </values>"), out);
    String conflicts =
        "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            + vars
            + "</variables><constraints><extension><list> p q </list><conflicts> (r,*)(g,g)(b,*) </conflicts>"
            + "</extension></constraints></instance>";
    out = competitionOutput(conflicts);
    assertTrue(out.contains("s SATISFIABLE") && out.contains("<values> g b </values>"), out);
    String unary =
        "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            + vars
            + "</variables><constraints><extension><list> p </list><conflicts> r g </conflicts>"
            + "</extension></constraints></instance>";
    out = competitionOutput(unary);
    assertTrue(out.contains("s SATISFIABLE") && out.contains("<values> b "), out);
  }
}
