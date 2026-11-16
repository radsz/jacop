/*
 * RootRefutationFuzzTest.java
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

package org.jacop.fz;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random small models near the feasibility threshold for the three root passes that declare a
 * satisfaction model unsatisfiable from a linear relaxation: the value encodings of {@code
 * LinearRelaxation.refutation}, its pseudo-objective form for models with no value encoding ({@code
 * org.jacop.lp.refutationObjective}) and the clause refutation with at-most-one cliques ({@code
 * org.jacop.lp.clauseRefutation}). A wrong refutation is a wrong UNSAT, so every model is solved in
 * several modes, with the relaxation and without it ({@code --lp off}), and each answer is checked
 * against enumeration: an UNSAT claim needs a model with no solution, a solution must satisfy every
 * constraint, and an optimum must be the least cost. The test also counts the unsatisfiable models
 * that each pass refutes ({@code lpRefutation=refuted} with its {@code lpRefutationKind}) and fails
 * when a pass stops firing, so that the fuzz keeps reaching them.
 *
 * <p>The models are 0/1 models of clauses with duplicated and complementary literals, at-most-one
 * groups stated as rows or as their pairs of binary clauses, exactly-one rows, cardinality,
 * covering and packing rows with negated literals and repeated variables, variables fixed where
 * they are declared, pigeonhole and odd-cycle vertex cover cores, and small integer models of
 * all-different and counting constraints linked to 0/1 variables by reified equalities.
 *
 * <p>{@code -DrootRefutation.fuzz.trials=20000} (2,000 by default, 1,000 in the min profile, about
 * 2 minutes for 20,000) and {@code -DrootRefutation.fuzz.seed=N} run it at volume; {@code
 * -DrootRefutation.fuzz.dump=DIR} writes the unsatisfiable satisfaction models to DIR.
 */
class RootRefutationFuzzTest {

  private static final int TRIALS = Integer.getInteger("rootRefutation.fuzz.trials", 2000);
  private static final long SEED = Long.getLong("rootRefutation.fuzz.seed", 20261116L);
  // runs with the relaxation, as fzn-jacop runs (LCG and symmetry breaking on) and in other
  // modes, and the run without it. The build turns LCG off by default (jacop.lcg) and symmetry
  // breaking without presolve (jacop.symmetry), so the runs ask for what they need; the
  // refutations take their clauses from LCG. The first two runs count the refutations
  private static final String[][] RUNS = {
    {"--lcg", "--symmetry", "on"},
    {"--lcg", "--symmetry", "off"},
    {"--lcg", "-f", "--symmetry", "on"},
    {},
    {"--lcg", "--lp", "off"}
  };
  // brute force gives up past this many nodes and the trial makes a new model
  private static final long NODE_LIMIT = 2_000_000;

  @TempDir Path tmp;

  // a constraint of the model: the variables it reads, its relation and its FlatZinc text
  private record Con(int[] scope, Predicate<int[]> holds, String fzn) {}

  private static final class Model {
    final String family;
    final int bools;
    final int[] lo;
    final int[] hi;
    final Map<Integer, Integer> fixed = new HashMap<>();
    final List<Con> cons = new ArrayList<>();
    // the 0/1 views of the Booleans that integer rows use
    final TreeSet<Integer> views = new TreeSet<>();
    // the objective sum weight[k] * value(var[k]), or null for a satisfaction model
    int[] objVars;
    int[] objWeights;

    Model(String family, int bools, int[] lo, int[] hi) {
      this.family = family;
      this.bools = bools;
      this.lo = lo;
      this.hi = hi;
    }

    int size() {
      return bools + lo.length;
    }

    int min(int v) {
      return v < bools ? 0 : lo[v - bools];
    }

    int max(int v) {
      return v < bools ? 1 : hi[v - bools];
    }

    String name(int v) {
      return v < bools ? "b" + v : "v" + (v - bools);
    }

    void add(int[] scope, Predicate<int[]> holds, String fzn) {
      cons.add(new Con(scope, holds, fzn));
    }
  }

  // ---- literals: 2 * variable + 1 when negated

  private static int lit(Random r, int bools) {
    return 2 * r.nextInt(bools) + (r.nextInt(3) == 0 ? 1 : 0);
  }

  private static int value(int[] a, int lit) {
    return (lit & 1) == 0 ? a[lit >> 1] : 1 - a[lit >> 1];
  }

  private static int[] scopeOf(int[] lits) {
    return Arrays.stream(lits).map(l -> l >> 1).distinct().toArray();
  }

  private static void clause(Model m, int... lits) {
    StringBuilder pos = new StringBuilder();
    StringBuilder neg = new StringBuilder();
    for (int l : lits) {
      StringBuilder sb = (l & 1) == 0 ? pos : neg;
      sb.append(sb.isEmpty() ? "" : ", ").append(m.name(l >> 1));
    }
    m.add(
        scopeOf(lits),
        a -> Arrays.stream(lits).anyMatch(l -> value(a, l) == 1),
        "constraint bool_clause([" + pos + "], [" + neg + "]);");
  }

  private static final int LE = 0;
  private static final int EQ = 1;
  private static final int GE = 2;

  // sum w[k] * lit[k] rel c over literals, as bool_lin_* when it can be, int_lin_* over views
  private static void row(Model m, Random r, int[] w, int[] lits, int rel, int c) {
    int[] wc = w.clone();
    int[] lc = lits.clone();
    Predicate<int[]> holds =
        a -> {
          long s = 0;
          for (int k = 0; k < wc.length; k++) {
            s += (long) wc[k] * value(a, lc[k]);
          }
          return rel == LE ? s <= c : rel == EQ ? s == c : s >= c;
        };
    boolean positive =
        Arrays.stream(lits).allMatch(l -> (l & 1) == 0) && Arrays.stream(w).allMatch(x -> x > 0);
    if (positive && rel != GE && r.nextInt(3) == 0) {
      m.add(
          scopeOf(lits),
          holds,
          "constraint bool_lin_"
              + (rel == LE ? "le" : "eq")
              + "("
              + list(w)
              + ", ["
              + names(lits, "b")
              + "], "
              + c
              + ");");
      return;
    }
    // negated literal: w * (1 - y) = w - w * y
    long rhs = c;
    int[] coef = new int[w.length];
    for (int k = 0; k < w.length; k++) {
      coef[k] = (lits[k] & 1) == 0 ? w[k] : -w[k];
      if ((lits[k] & 1) == 1) {
        rhs -= w[k];
      }
      m.views.add(lits[k] >> 1);
    }
    if (rel == GE) {
      for (int k = 0; k < coef.length; k++) {
        coef[k] = -coef[k];
      }
      rhs = -rhs;
    }
    m.add(
        scopeOf(lits),
        holds,
        "constraint int_lin_"
            + (rel == EQ ? "eq" : "le")
            + "("
            + list(coef)
            + ", ["
            + names(lits, "y")
            + "], "
            + rhs
            + ");");
  }

  private static String list(int[] w) {
    StringBuilder sb = new StringBuilder("[");
    for (int k = 0; k < w.length; k++) {
      sb.append(k == 0 ? "" : ", ").append(w[k]);
    }
    return sb.append(']').toString();
  }

  private static String names(int[] lits, String prefix) {
    StringBuilder sb = new StringBuilder();
    for (int k = 0; k < lits.length; k++) {
      sb.append(k == 0 ? "" : ", ").append(prefix).append(lits[k] >> 1);
    }
    return sb.toString();
  }

  // at most one of the literals: a row, or its pairs of binary clauses (cliques to merge)
  private static void atMostOne(Model m, Random r, int[] lits) {
    if (r.nextBoolean()) {
      for (int i = 0; i < lits.length; i++) {
        for (int j = i + 1; j < lits.length; j++) {
          clause(m, lits[i] ^ 1, lits[j] ^ 1);
        }
      }
    } else {
      int[] ones = new int[lits.length];
      Arrays.fill(ones, 1);
      row(m, r, ones, lits, LE, 1);
    }
  }

  private static int[] lits(Random r, int bools, int length) {
    int[] lits = new int[length];
    for (int k = 0; k < length; k++) {
      lits[k] = lit(r, bools);
    }
    return lits;
  }

  // distinct variables, each as a literal of random sign (negated with probability 1/neg)
  private static int[] distinctLits(Random r, int bools, int length, int neg) {
    List<Integer> vars = new ArrayList<>();
    for (int v = 0; v < bools; v++) {
      vars.add(v);
    }
    Collections.shuffle(vars, r);
    int[] lits = new int[Math.min(length, bools)];
    for (int k = 0; k < lits.length; k++) {
      lits[k] = 2 * vars.get(k) + (neg > 0 && r.nextInt(neg) == 0 ? 1 : 0);
    }
    return lits;
  }

  // ---- side constraints over the Booleans of a model: the noise around a core

  private static void sideConstraint(Model m, Random r) {
    int n = m.bools;
    switch (r.nextInt(7)) {
      case 0, 1 -> {
        // a clause, sometimes a unit, with duplicated or complementary literals
        int[] c = lits(r, n, 1 + r.nextInt(4));
        if (c.length > 1 && r.nextInt(6) == 0) {
          c[1] = r.nextBoolean() ? c[0] : c[0] ^ 1;
        }
        clause(m, c);
      }
      case 2 -> atMostOne(m, r, distinctLits(r, n, 3 + r.nextInt(3), 4));
      case 3 -> {
        int[] l = distinctLits(r, n, 2 + r.nextInt(4), 4);
        int[] ones = new int[l.length];
        Arrays.fill(ones, 1);
        row(m, r, ones, l, EQ, 1);
      }
      default -> {
        // a cardinality, covering or packing row with weights 1..3, sometimes a negative one
        // and a repeated variable, its right-hand side near the middle of its range
        int[] l = lits(r, n, 3 + r.nextInt(4));
        int[] w = new int[l.length];
        long lo = 0;
        long hi = 0;
        for (int k = 0; k < w.length; k++) {
          w[k] = 1 + (r.nextInt(3) == 0 ? r.nextInt(3) : 0);
          if (r.nextInt(8) == 0) {
            w[k] = -w[k];
          }
          lo += Math.min(0, w[k]);
          hi += Math.max(0, w[k]);
        }
        int rel = r.nextInt(3);
        int c = (int) (lo + (hi - lo) * (1 + r.nextInt(3)) / 4);
        row(m, r, w, l, rel, c);
      }
    }
  }

  // ---- model families

  private static Model random01(Random r) {
    Model m = new Model("random01", 6 + r.nextInt(9), new int[0], new int[0]);
    int count = m.bools / 3 + r.nextInt(m.bools / 2 + 3);
    for (int i = 0; i < count; i++) {
      sideConstraint(m, r);
    }
    return m;
  }

  // p pigeons in h holes, sometimes with a hole too many or a pigeon removed, around noise
  private static Model pigeons(Random r) {
    int h = 3 + r.nextInt(2);
    int p = h + (r.nextInt(4) == 0 ? 0 : 1);
    // in clauses alone a third of the time: the clause refutation, with cliques of the pairs
    boolean cnf = r.nextInt(3) == 0;
    Model m =
        new Model(cnf ? "pigeonsCnf" : "pigeons", p * h + r.nextInt(3), new int[0], new int[0]);
    // pigeon i in hole j is the literal of variable i * h + j, negated in a mirrored model
    boolean mirrored = r.nextInt(4) == 0;
    int flip = mirrored ? 1 : 0;
    for (int i = 0; i < p; i++) {
      int[] row = new int[h];
      for (int j = 0; j < h; j++) {
        row[j] = 2 * (i * h + j) + flip;
      }
      if (cnf || r.nextBoolean()) {
        clause(m, row);
      } else {
        int[] ones = new int[h];
        Arrays.fill(ones, 1);
        row(m, r, ones, row, r.nextBoolean() ? GE : EQ, 1);
      }
    }
    for (int j = 0; j < h; j++) {
      int[] column = new int[p];
      for (int i = 0; i < p; i++) {
        column[i] = 2 * (i * h + j) + flip;
      }
      if (r.nextInt(12) != 0) {
        if (cnf) {
          for (int a = 0; a < p; a++) {
            for (int b = a + 1; b < p; b++) {
              clause(m, column[a] ^ 1, column[b] ^ 1);
            }
          }
        } else {
          atMostOne(m, r, column);
        }
      }
    }
    int noise = r.nextInt(3);
    for (int i = 0; i < noise; i++) {
      if (cnf) {
        clause(m, lits(r, m.bools, 2 + r.nextInt(2)));
      } else {
        sideConstraint(m, r);
      }
    }
    return m;
  }

  // a vertex cover of at most k vertices of odd cycles, k at or just below the least cover
  private static Model oddCycles(Random r) {
    int cycles = 1 + r.nextInt(2);
    int[] length = new int[cycles];
    int n = 0;
    int least = 0;
    for (int c = 0; c < cycles; c++) {
      length[c] = 3 + 2 * r.nextInt(3);
      n += length[c];
      least += (length[c] + 1) / 2;
    }
    Model m = new Model("oddCycles", n + r.nextInt(3), new int[0], new int[0]);
    int first = 0;
    for (int c = 0; c < cycles; c++) {
      for (int i = 0; i < length[c]; i++) {
        int u = 2 * (first + i);
        int v = 2 * (first + (i + 1) % length[c]);
        if (r.nextInt(3) == 0) {
          row(m, r, new int[] {1, 1}, new int[] {u, v}, GE, 1);
        } else {
          clause(m, u, v);
        }
      }
      first += length[c];
    }
    int[] all = new int[n];
    int[] ones = new int[n];
    for (int v = 0; v < n; v++) {
      all[v] = 2 * v;
      ones[v] = 1;
    }
    row(m, r, ones, all, LE, least - (r.nextBoolean() ? 1 : 0));
    int noise = r.nextInt(3);
    for (int i = 0; i < noise; i++) {
      sideConstraint(m, r);
    }
    return m;
  }

  // a colouring of a small graph with k colours near its chromatic number: all-different on the
  // edges and triangles, counting constraints, and Booleans linked to the colours by reified
  // equalities that clauses and rows constrain
  private static Model values(Random r) {
    int ints = 4 + r.nextInt(4);
    int k = 2 + r.nextInt(2);
    int[] lo = new int[ints];
    int[] hi = new int[ints];
    for (int i = 0; i < ints; i++) {
      lo[i] = 0;
      hi[i] = k - 1 + (r.nextInt(10) == 0 ? 1 : 0);
    }
    int links = r.nextInt(5);
    Model m = new Model("values", links, lo, hi);
    boolean[][] edge = new boolean[ints][ints];
    int edges = ints - 1 + r.nextInt(ints + (k == 3 ? ints : 0));
    for (int e = 0; e < edges; e++) {
      int u = r.nextInt(ints);
      int v = r.nextInt(ints);
      if (u != v) {
        edge[Math.min(u, v)][Math.max(u, v)] = true;
      }
    }
    for (int u = 0; u < ints; u++) {
      for (int v = u + 1; v < ints; v++) {
        if (!edge[u][v]) {
          continue;
        }
        int w = -1;
        for (int t = v + 1; t < ints && w < 0; t++) {
          if (edge[u][t] && edge[v][t] && r.nextBoolean()) {
            w = t;
          }
        }
        int[] xs =
            w < 0
                ? new int[] {m.bools + u, m.bools + v}
                : new int[] {m.bools + u, m.bools + v, m.bools + w};
        if (w >= 0) {
          edge[u][w] = false;
          edge[v][w] = false;
        }
        if (xs.length == 2 && r.nextInt(3) == 0) {
          m.add(
              xs,
              a -> a[xs[0]] != a[xs[1]],
              "constraint int_ne(" + m.name(xs[0]) + ", " + m.name(xs[1]) + ");");
        } else {
          m.add(
              xs,
              a -> Arrays.stream(xs).map(x -> a[x]).distinct().count() == xs.length,
              "constraint jacop_alldiff([" + intNames(m, xs) + "]);");
        }
      }
    }
    for (int b = 0; b < links; b++) {
      int v = m.bools + r.nextInt(ints);
      int c = m.min(v) + r.nextInt(m.max(v) - m.min(v) + 1);
      int bv = b;
      m.add(
          new int[] {bv, v},
          a -> a[bv] == (a[v] == c ? 1 : 0),
          "constraint int_eq_reif(" + m.name(v) + ", " + c + ", " + m.name(bv) + ");");
    }
    int count = r.nextInt(3);
    for (int i = 0; i < count; i++) {
      int[] xs = distinctInts(r, m, 2 + r.nextInt(ints - 1));
      if (r.nextBoolean()) {
        int val = r.nextInt(k);
        int c = r.nextInt(xs.length / 2 + 2);
        m.add(
            xs,
            a -> Arrays.stream(xs).filter(x -> a[x] == val).count() == c,
            "constraint jacop_count([" + intNames(m, xs) + "], " + val + ", " + c + ");");
      } else {
        // lower and upper counts of some colours
        int n = 1 + r.nextInt(2);
        int[] cover = new int[n];
        int[] lb = new int[n];
        int[] ub = new int[n];
        for (int j = 0; j < n; j++) {
          cover[j] = j == 0 ? r.nextInt(k) : cover[j - 1] + 1;
          lb[j] = r.nextInt(2);
          ub[j] = lb[j] + r.nextInt(3);
        }
        countBounds(m, xs, cover, lb, ub);
      }
    }
    if (links > 0) {
      int noise = r.nextInt(3);
      for (int i = 0; i < noise; i++) {
        sideConstraint(m, r);
      }
    }
    return m;
  }

  // at least lb[j] and at most ub[j] of xs take the value cover[j]
  private static void countBounds(Model m, int[] xs, int[] cover, int[] lb, int[] ub) {
    m.add(
        xs,
        a -> {
          for (int j = 0; j < cover.length; j++) {
            int cj = cover[j];
            long c = Arrays.stream(xs).filter(x -> a[x] == cj).count();
            if (c < lb[j] || c > ub[j]) {
              return false;
            }
          }
          return true;
        },
        "constraint jacop_count_values_bounds(["
            + intNames(m, xs)
            + "], "
            + list(cover)
            + ", "
            + list(lb)
            + ", "
            + list(ub)
            + ");");
  }

  // integer variables whose values are counted over overlapping subsets: each count holds alone,
  // and only their sum over the subsets (the value encodings) shows that they cannot all hold
  private static Model counts(Random r) {
    int ints = 4 + r.nextInt(4);
    int k = 2 + r.nextInt(2);
    int[] lo = new int[ints];
    int[] hi = new int[ints];
    Arrays.fill(hi, k - 1);
    Model m = new Model("counts", r.nextInt(3), lo, hi);
    int groups = 2 + r.nextInt(3);
    for (int g = 0; g < groups; g++) {
      int[] xs = distinctInts(r, m, Math.min(ints, 3 + r.nextInt(3)));
      int[] cover = new int[k];
      int[] lb = new int[k];
      int[] ub = new int[k];
      for (int v = 0; v < k; v++) {
        cover[v] = v;
        // xs.length / k of each value, rounded either way, now and then one less or more
        lb[v] = Math.max(0, xs.length / k - (r.nextInt(4) == 0 ? 1 : 0));
        ub[v] =
            (r.nextInt(3) == 0 ? xs.length / k : (xs.length + k - 1) / k)
                + (r.nextInt(4) == 0 ? 1 : 0);
      }
      countBounds(m, xs, cover, lb, ub);
    }
    for (int b = 0; b < m.bools; b++) {
      int v = m.bools + r.nextInt(ints);
      int c = r.nextInt(k);
      int bv = b;
      m.add(
          new int[] {bv, v},
          a -> a[bv] == (a[v] == c ? 1 : 0),
          "constraint int_eq_reif(" + m.name(v) + ", " + c + ", " + m.name(bv) + ");");
    }
    if (m.bools > 1 && r.nextBoolean()) {
      clause(m, lits(r, m.bools, 2));
    }
    return m;
  }

  private static int[] distinctInts(Random r, Model m, int length) {
    List<Integer> vars = new ArrayList<>();
    for (int v = m.bools; v < m.size(); v++) {
      vars.add(v);
    }
    Collections.shuffle(vars, r);
    return vars.subList(0, length).stream().mapToInt(Integer::intValue).toArray();
  }

  private static String intNames(Model m, int[] xs) {
    StringBuilder sb = new StringBuilder();
    for (int k = 0; k < xs.length; k++) {
      sb.append(k == 0 ? "" : ", ").append(m.name(xs[k]));
    }
    return sb.toString();
  }

  private static Model randomModel(Random r) {
    Model m =
        switch (r.nextInt(9)) {
          case 0, 1, 2 -> random01(r);
          case 3, 4 -> pigeons(r);
          case 5 -> oddCycles(r);
          case 6 -> values(r);
          default -> counts(r);
        };
    // variables fixed where they are declared
    int fixed = r.nextInt(3) == 0 ? 1 + r.nextInt(2) : 0;
    for (int i = 0; i < fixed; i++) {
      int v = r.nextInt(m.size());
      m.fixed.put(v, m.min(v) + r.nextInt(m.max(v) - m.min(v) + 1));
    }
    // an optimisation model now and then: the relaxation then has no refutation to make
    if (r.nextInt(5) == 0) {
      int k = 2 + r.nextInt(Math.min(5, m.size() - 1));
      m.objVars = new int[k];
      m.objWeights = new int[k];
      for (int i = 0; i < k; i++) {
        m.objVars[i] = r.nextInt(m.size());
        m.objWeights[i] = r.nextInt(7) - 3;
        if (m.objVars[i] < m.bools) {
          m.views.add(m.objVars[i]);
        }
      }
    }
    return m;
  }

  // ---- enumeration

  private static final class Enumeration {
    boolean found;
    long best = Long.MAX_VALUE;
    long nodes;
  }

  // whether the model has a solution, and its least cost; null past the node limit
  private static Enumeration bruteForce(Model m) {
    int n = m.size();
    List<List<Con>> due = new ArrayList<>();
    for (int v = 0; v < n; v++) {
      due.add(new ArrayList<>());
    }
    for (Con c : m.cons) {
      due.get(Arrays.stream(c.scope()).max().orElse(0)).add(c);
    }
    Enumeration e = new Enumeration();
    if (!search(m, due, new int[n], 0, e)) {
      return null;
    }
    return e;
  }

  private static boolean search(Model m, List<List<Con>> due, int[] a, int v, Enumeration e) {
    if (++e.nodes > NODE_LIMIT) {
      return false;
    }
    if (v == a.length) {
      e.found = true;
      if (m.objVars != null) {
        e.best = Math.min(e.best, cost(m, a));
      }
      return true;
    }
    int lo = m.fixed.containsKey(v) ? m.fixed.get(v) : m.min(v);
    int hi = m.fixed.containsKey(v) ? m.fixed.get(v) : m.max(v);
    for (int x = lo; x <= hi; x++) {
      a[v] = x;
      boolean ok = true;
      for (Con c : due.get(v)) {
        if (!c.holds().test(a)) {
          ok = false;
          break;
        }
      }
      if (ok) {
        if (!search(m, due, a, v + 1, e)) {
          return false;
        }
        if (e.found && m.objVars == null) {
          return true;
        }
      }
    }
    return true;
  }

  private static long cost(Model m, int[] a) {
    long s = 0;
    for (int k = 0; k < m.objVars.length; k++) {
      s += (long) m.objWeights[k] * a[m.objVars[k]];
    }
    return s;
  }

  // ---- FlatZinc

  private static String fzn(Model m) {
    StringBuilder sb = new StringBuilder();
    for (int v = 0; v < m.size(); v++) {
      String type = v < m.bools ? "bool" : m.min(v) + ".." + m.max(v);
      sb.append("var ").append(type).append(": ").append(m.name(v)).append(" :: output_var");
      Integer f = m.fixed.get(v);
      if (f != null) {
        sb.append(" = ").append(v < m.bools ? (f == 1 ? "true" : "false") : f.toString());
      }
      sb.append(";\n");
    }
    for (int v : m.views) {
      sb.append("var 0..1: y").append(v).append(";\n");
    }
    long lo = 0;
    long hi = 0;
    if (m.objVars != null) {
      for (int k = 0; k < m.objVars.length; k++) {
        long a = (long) m.objWeights[k] * m.min(m.objVars[k]);
        long b = (long) m.objWeights[k] * m.max(m.objVars[k]);
        lo += Math.min(a, b);
        hi += Math.max(a, b);
      }
      sb.append("var ").append(lo).append("..").append(hi).append(": obj :: output_var;\n");
    }
    for (int v : m.views) {
      sb.append("constraint bool2int(b").append(v).append(", y").append(v).append(");\n");
    }
    for (Con c : m.cons) {
      sb.append(c.fzn()).append('\n');
    }
    if (m.objVars == null) {
      sb.append("solve satisfy;\n");
    } else {
      int[] w = Arrays.copyOf(m.objWeights, m.objWeights.length + 1);
      w[w.length - 1] = -1;
      StringBuilder vars = new StringBuilder();
      for (int v : m.objVars) {
        vars.append(v < m.bools ? "y" + v : m.name(v)).append(", ");
      }
      sb.append("constraint int_lin_eq(")
          .append(list(w))
          .append(", [")
          .append(vars)
          .append("obj], 0);\n");
      sb.append("solve minimize obj;\n");
    }
    return sb.toString();
  }

  private static final Pattern ASSIGNMENT = Pattern.compile("^(\\w+) = (-?\\w+);$");

  private String run(String model, String... options) throws IOException {
    Path file = tmp.resolve("case.fzn");
    Files.writeString(file, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      List<String> args = new ArrayList<>(Arrays.asList(options));
      args.add("-s");
      args.add("-v");
      args.add("-t");
      args.add("20000");
      args.add(file.toString());
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  // the problem with the answer of a run, or null when it is right; timeouts are not problems
  private static String judge(Model m, Enumeration e, String out) {
    if (out.contains("=====UNSATISFIABLE=====")) {
      return e.found ? "UNSAT claimed, the model has a solution" : null;
    }
    if (out.contains("=====UNKNOWN=====") || !out.contains("----------")) {
      return null;
    }
    // the last solution printed
    String[] blocks = out.split("----------");
    String last = blocks[blocks.length - 2];
    Map<String, Integer> values = new HashMap<>();
    for (String line : last.split("\\R")) {
      Matcher x = ASSIGNMENT.matcher(line.trim());
      if (x.matches()) {
        String s = x.group(2);
        values.put(x.group(1), "true".equals(s) ? 1 : "false".equals(s) ? 0 : Integer.valueOf(s));
      }
    }
    int[] a = new int[m.size()];
    for (int v = 0; v < m.size(); v++) {
      Integer x = values.get(m.name(v));
      if (x == null) {
        return "solution without " + m.name(v);
      }
      a[v] = x;
      Integer f = m.fixed.get(v);
      if (x < m.min(v) || x > m.max(v) || (f != null && !f.equals(x))) {
        return "solution with " + m.name(v) + " = " + x + " out of its domain";
      }
    }
    for (Con c : m.cons) {
      if (!c.holds().test(a)) {
        return "solution breaks " + c.fzn();
      }
    }
    if (m.objVars != null) {
      long cost = cost(m, a);
      if (values.get("obj") == null || values.get("obj") != cost) {
        return "objective " + values.get("obj") + " is not the cost " + cost;
      }
      if (out.contains("==========") && cost != e.best) {
        return "optimum " + cost + " claimed, the least cost is " + e.best;
      }
    }
    return null;
  }

  private static final Pattern KIND = Pattern.compile("lpRefutationKind=(\\w+)");

  @Test
  void refutationsAgreeWithEnumeration() throws IOException {
    Random r = new Random(SEED);
    String dump = System.getProperty("rootRefutation.fuzz.dump");
    List<String> failures = new ArrayList<>();
    // unsatisfiable satisfaction models per family, and per kind those the counted runs refuted
    Map<String, Integer> unsat = new TreeMap<>();
    Map<String, Integer> refutedBy = new TreeMap<>();
    int unsatisfiable = 0;
    int refuted = 0;
    int trials = 0;
    int skipped = 0;
    while (trials < TRIALS && failures.isEmpty()) {
      Model m = randomModel(r);
      Enumeration e = bruteForce(m);
      if (e == null) {
        skipped++;
        continue;
      }
      trials++;
      String model = fzn(m);
      boolean counted = !e.found && m.objVars == null;
      if (counted) {
        unsatisfiable++;
        unsat.merge(m.family, 1, Integer::sum);
        if (dump != null) {
          Files.writeString(Path.of(dump, m.family + trials + ".fzn"), model);
        }
      }
      String kind = null;
      for (String[] options : RUNS) {
        String out = run(model, options);
        String problem = judge(m, e, out);
        boolean refutes = out.contains("lpRefutation=refuted");
        if (problem == null && refutes && e.found) {
          problem = "the root refutation refuted a model with a solution";
        }
        if (problem != null) {
          failures.add(
              "trial "
                  + trials
                  + " ("
                  + m.family
                  + ", seed "
                  + SEED
                  + ") ["
                  + String.join(" ", options)
                  + "]: "
                  + problem
                  + "\n"
                  + model);
          break;
        }
        if (refutes && kind == null && (options == RUNS[0] || options == RUNS[1])) {
          Matcher k = KIND.matcher(out);
          kind = k.find() ? k.group(1) : "?";
        }
      }
      if (kind != null) {
        refuted++;
        refutedBy.merge(kind, 1, Integer::sum);
      }
    }
    String summary =
        trials
            + " trials ("
            + skipped
            + " skipped); unsatisfiable satisfaction models "
            + unsat
            + "; refuted by the root LP "
            + refuted
            + " "
            + refutedBy;
    System.out.println("RootRefutationFuzzTest: " + summary);
    assertTrue(failures.isEmpty(), String.join("\n", failures));
    // each pass keeps firing on the unsatisfiable models: over 3 seeds of 20,000 trials the counted
    // runs refuted 34 % of them, the pseudo-objective 2,000, the clause refutation 500 and the
    // value encodings 100 per seed; half of that share is asked
    if (TRIALS >= 300) {
      assertTrue(refuted * 6 >= unsatisfiable, summary);
      for (String k : List.of("values", "objective", "clauses")) {
        assertTrue(refutedBy.getOrDefault(k, 0) > 0, "no " + k + " refutation: " + summary);
      }
    }
  }
}
