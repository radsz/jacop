/*
 * SubsetCardinalities.java
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

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearForm;

/**
 * Merges clauses of three or more 0/1 literals into the cardinality constraints they encode.
 *
 * <p>The clauses over all subsets of m literals of a set S of n literals state that at most m - 1
 * literals of S are false, that is {@code sum of S >= n - m + 1}; CNF encodings of cardinality
 * constraints by their subsets (the binomial encoding) are such sets. The LP of the clauses alone
 * is feasible with every literal at (m - 1) / m or 1/2, while the cardinality rows carry the
 * counts: the fixed-bandwidth formulas of the Pseudo-Boolean Competition 2015 (proof complexity
 * benchmarks, cardinality constraints encoded in clauses) cover their 77 variables once by "at
 * least 2 of 4" and "at least 3 of 5" and once by "at most 2 of 4" and "at most 2 of 5", which the
 * LP of the cardinality rows refutes at once by adding them up, while resolution needs many steps
 * for such counting arguments (A. Haken, "The intractability of resolution", TCS 39, 1985; the
 * cardinality detection from clauses is studied by A. Biere, D. Le Berre, E. Lonca and N. Manthey,
 * "Detecting cardinality constraints in CNF", SAT 2014). For m = 2 these are the cliques of {@link
 * PairCliques}.
 *
 * <p>Each clause not yet covered grows a set greedily: a literal joins when the clauses over it and
 * every subset of m - 1 literals of the set are all present. The clauses covered by a set of more
 * than m literals are replaced by its cardinality row, which implies them in the LP too.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SubsetCardinalities {

  // the clause lengths merged
  static final int MIN_LENGTH = 3;
  static final int MAX_LENGTH = Integer.getInteger("org.jacop.lp.subsetCardinalityLength", 5);

  // the most literals of one set, and the most subsets tested in all
  private static final int MAX_SET = 64;
  private static final long MAX_WORK = 20_000_000;

  /** The rows, with the cardinality rows in place of the clause rows they cover. */
  final List<LinearForm> rows;

  /** The number of cardinality rows. */
  final int cardinalities;

  private SubsetCardinalities(List<LinearForm> rows, int cardinalities) {
    this.rows = rows;
    this.cardinalities = cardinalities;
  }

  private record Key(int[] literals) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Key k && Arrays.equals(literals, k.literals);
    }

    @Override
    public int hashCode() {
      return Arrays.hashCode(literals);
    }

    @Override
    public String toString() {
      return Arrays.toString(literals);
    }
  }

  /**
   * Returns the rows with the clauses that encode cardinality constraints by subsets merged.
   *
   * @param given the rows; not changed
   * @return the rows and the number of cardinality rows
   */
  static SubsetCardinalities merge(List<LinearForm> given) {
    if (!ENABLED) {
      return new SubsetCardinalities(given, 0);
    }
    Map<IntVar, Integer> column = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    // the clause of each row, sorted literals: 2 j for x_j = 1, 2 j + 1 for x_j = 0
    int[][] clause = new int[given.size()][];
    Set<Key> present = new HashSet<>();
    // the literals that complete each subset of m - 1 literals of a clause
    Map<Key, List<Integer>> completions = new HashMap<>();
    long work = 0;
    for (int i = 0; i < given.size(); i++) {
      int[] c = clause(given.get(i), column, vars);
      if (c == null || !present.add(new Key(c))) {
        continue;
      }
      clause[i] = c;
      for (int k = 0; k < c.length; k++) {
        completions.computeIfAbsent(new Key(without(c, k)), x -> new ArrayList<>()).add(c[k]);
      }
      work += c.length;
    }
    if (present.size() < MIN_LENGTH + 1) {
      return new SubsetCardinalities(given, 0);
    }
    Set<Key> covered = new HashSet<>();
    List<int[]> found = new ArrayList<>();
    List<Integer> lengths = new ArrayList<>();
    for (int i = 0; i < clause.length && work < MAX_WORK; i++) {
      int[] c = clause[i];
      if (c == null || covered.contains(new Key(c))) {
        continue;
      }
      int m = c.length;
      List<Integer> set = new ArrayList<>();
      for (int l : c) {
        set.add(l);
      }
      List<Integer> candidates = completions.get(new Key(without(c, m - 1)));
      for (int l : candidates) {
        if (set.size() >= MAX_SET || work >= MAX_WORK) {
          break;
        }
        if (set.contains(l) || set.contains(l ^ 1)) {
          continue;
        }
        boolean all = true;
        for (int[] t : subsets(set, m - 1)) {
          work++;
          if (!present.contains(new Key(with(t, l)))) {
            all = false;
            break;
          }
        }
        if (all) {
          set.add(l);
        }
      }
      if (set.size() <= m) {
        continue;
      }
      for (int[] t : subsets(set, m)) {
        covered.add(new Key(t));
        work++;
      }
      found.add(set.stream().mapToInt(Integer::intValue).sorted().toArray());
      lengths.add(m);
    }
    if (found.isEmpty()) {
      return new SubsetCardinalities(given, 0);
    }
    List<LinearForm> rows = new ArrayList<>();
    for (int i = 0; i < given.size(); i++) {
      if (clause[i] == null || !covered.contains(new Key(clause[i]))) {
        rows.add(given.get(i));
      }
    }
    for (int k = 0; k < found.size(); k++) {
      rows.add(row(found.get(k), lengths.get(k), vars));
    }
    return new SubsetCardinalities(rows, found.size());
  }

  /** Whether the merge is on (system property org.jacop.lp.subsetCardinalities). */
  static final boolean ENABLED =
      !"false".equalsIgnoreCase(System.getProperty("org.jacop.lp.subsetCardinalities"));

  private static int[] without(int[] c, int k) {
    int[] t = new int[c.length - 1];
    System.arraycopy(c, 0, t, 0, k);
    System.arraycopy(c, k + 1, t, k, c.length - k - 1);
    return t;
  }

  private static int[] with(int[] t, int l) {
    int[] c = Arrays.copyOf(t, t.length + 1);
    c[t.length] = l;
    Arrays.sort(c);
    return c;
  }

  // every subset of k elements of the set, each sorted
  private static List<int[]> subsets(List<Integer> set, int k) {
    int[] s = set.stream().mapToInt(Integer::intValue).sorted().toArray();
    List<int[]> out = new ArrayList<>();
    int[] index = new int[k];
    for (int i = 0; i < k; i++) {
      index[i] = i;
    }
    while (true) {
      int[] t = new int[k];
      for (int i = 0; i < k; i++) {
        t[i] = s[index[i]];
      }
      out.add(t);
      int i = k - 1;
      while (i >= 0 && index[i] == s.length - k + i) {
        i--;
      }
      if (i < 0) {
        return out;
      }
      index[i]++;
      for (int j = i + 1; j < k; j++) {
        index[j] = index[j - 1] + 1;
      }
    }
  }

  // sum of the literals >= n - m + 1, as the positive ones minus the negative ones
  // >= n - m + 1 - negatives
  private static LinearForm row(int[] set, int m, List<IntVar> vars) {
    IntVar[] xs = new IntVar[set.length];
    long[] ws = new long[set.length];
    long c = (long) set.length - m + 1;
    for (int q = 0; q < set.length; q++) {
      xs[q] = vars.get(set[q] >> 1);
      if ((set[q] & 1) == 0) {
        ws[q] = 1;
      } else {
        ws[q] = -1;
        c--;
      }
    }
    return new LinearForm(xs, ws, c, LinearForm.GE);
  }

  // the literals of the clause that the row states (one of them is true), sorted, or null when it
  // is no clause of MIN_LENGTH to MAX_LENGTH literals over 0/1 variables with unit weights; fixed
  // variables count as constants
  private static int[] clause(LinearForm f, Map<IntVar, Integer> column, List<IntVar> vars) {
    if (f == null || f.relation() != LinearForm.LE && f.relation() != LinearForm.GE) {
      return null;
    }
    IntVar[] xs = f.vars();
    long[] ws = f.weights();
    // as sign * sum w x >= b
    long sign = f.relation() == LinearForm.GE ? 1 : -1;
    long b = sign * f.c();
    if (xs.length > MAX_LENGTH + 2) {
      return null;
    }
    IntVar[] free = new IntVar[xs.length];
    long[] a = new long[xs.length];
    int count = 0;
    for (int k = 0; k < xs.length; k++) {
      IntVar x = xs[k];
      long w = sign * ws[k];
      if (x.singleton()) {
        b -= w * x.value();
      } else if (w != 0) {
        if (Math.abs(w) != 1 || x.min() != 0 || x.max() != 1) {
          return null;
        }
        free[count] = x;
        a[count++] = w;
      }
    }
    if (count < MIN_LENGTH || count > MAX_LENGTH) {
      return null;
    }
    // sum of the literals (x for w = 1, 1 - x for w = -1) >= b + negatives must be 1
    long negatives = 0;
    for (int k = 0; k < count; k++) {
      if (a[k] < 0) {
        negatives++;
      }
    }
    if (b + negatives != 1) {
      return null;
    }
    int[] c = new int[count];
    for (int k = 0; k < count; k++) {
      int j =
          column.computeIfAbsent(
              free[k],
              x -> {
                vars.add(x);
                return vars.size() - 1;
              });
      c[k] = a[k] > 0 ? 2 * j : 2 * j + 1;
    }
    Arrays.sort(c);
    for (int k = 1; k < count; k++) {
      if (c[k] >> 1 == c[k - 1] >> 1) {
        // a variable twice: a tautology or a repeated literal
        return null;
      }
    }
    return c;
  }
}
