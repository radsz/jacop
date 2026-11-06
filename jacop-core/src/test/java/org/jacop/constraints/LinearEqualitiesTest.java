/*
 * LinearIntDomSumsetTest.java
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
package org.jacop.constraints;

import static org.assertj.core.api.Assertions.assertThat;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.jacop.util.IntLattice;
import org.junit.jupiter.api.Test;

/**
 * Checks {@link LinearEqualities} and {@link IntLattice}: the congruences of small examples, and on
 * random small systems of equalities, with and without the lattice reformulation, that the number
 * of solutions found by search equals the number found by brute force over the box, that no value
 * of a solution is pruned, and that the lattice describes exactly the integer solutions.
 */
class LinearEqualitiesTest {

  private static final int TRIALS = Integer.getInteger("lattice.trials", 3000);

  private static final int SYSTEMS = Integer.getInteger("lattice.systems", 20000);

  private static IntVar[] vars(Store store, int n, int lo, int hi) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, lo, hi);
    }
    return x;
  }

  // 2 x + 4 y + 3 z = 7: z is odd, which bounds propagation does not see
  @Test
  void singleRowCongruence() {
    Store store = new Store();
    IntVar[] x = vars(store, 3, -10, 10);
    LinearEqualities le = new LinearEqualities(store);
    le.apply(List.of(new LinearEqualities.Row(x, new int[] {2, 4, 3}, 7)));
    assertThat(x[2].dom().toString()).isEqualTo("{-9, -7, -5, -3, -1, 1, 3, 5, 7, 9}");
    assertThat(x[0].getSize()).isEqualTo(21);
    assertThat(le.prunedValues).isEqualTo(11);
  }

  // a congruence on a large domain only rounds its bounds: thousands of holes slow every later
  // domain operation (connect__0086_02 went from 5 s to over 60 s)
  @Test
  void largeDomainKeepsOneInterval() {
    Store store = new Store();
    IntVar[] x = vars(store, 2, -10, 10);
    IntVar z = new IntVar(store, "z", 1, 100_000);
    LinearEqualities le = new LinearEqualities(store);
    le.apply(
        List.of(new LinearEqualities.Row(new IntVar[] {x[0], x[1], z}, new int[] {30, 60, -1}, 0)));
    assertThat(z.dom().toString()).isEqualTo("{30..99990}");
  }

  // x + y = 1 and x - y = 0 have a rational solution only
  @Test
  void rationalOnlySystemFails() {
    Store store = new Store();
    IntVar[] x = vars(store, 2, -10, 10);
    LinearEqualities le = new LinearEqualities(store);
    List<LinearEqualities.Row> rows =
        List.of(
            new LinearEqualities.Row(x, new int[] {1, 1}, 1),
            new LinearEqualities.Row(x, new int[] {1, -1}, 0));
    boolean failed = false;
    try {
      le.apply(rows);
    } catch (FailException e) {
      failed = true;
    }
    assertThat(failed).isTrue();
  }

  // 3 x + 5 y = 2 z and z = 2 w + 1 (a definition): z is odd, so 3 x + 5 y is too; then t = x + y
  // (a definition) has no congruence, but u = 2 z + 4 x has u ≡ 2 (mod 4)
  @Test
  void definitionsTakeTheCongruenceOfTheirSum() {
    Store store = new Store();
    IntVar[] x = vars(store, 4, -20, 20);
    IntVar u = new IntVar(store, "u", -100, 100);
    LinearEqualities le = new LinearEqualities(store);
    le.apply(
        List.of(
            new LinearEqualities.Row(new IntVar[] {x[2], x[3]}, new int[] {1, -2}, 1),
            new LinearEqualities.Row(new IntVar[] {u, x[2], x[0]}, new int[] {1, -2, -4}, 0)));
    assertThat(x[2].min()).isEqualTo(-19);
    assertThat(x[2].getSize()).isEqualTo(20);
    assertThat(Math.floorMod(u.min(), 4)).isEqualTo(2);
    assertThat(u.getSize()).isEqualTo(50);
    assertThat(le.definitions).isEqualTo(2);
  }

  @Test
  void latticeIsExact() {
    Random r = new Random(3);
    for (int t = 0; t < TRIALS; t++) {
      int m = 1 + r.nextInt(3);
      int n = m + r.nextInt(4);
      long[][] a = new long[m][n];
      long[] b = new long[m];
      for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
          a[i][j] = r.nextInt(4) == 0 ? 0 : r.nextInt(13) - 6;
        }
        b[i] = r.nextInt(21) - 10;
      }
      IntLattice.Solutions s = IntLattice.solve(a, b, n);
      boolean reduced = r.nextBoolean();
      if (s != null && reduced) {
        IntLattice.reduce(s.basis(), 10_000);
      }
      // every point of the box: a solution iff x - x0 is an integer combination of the basis
      int[] x = new int[n];
      int lo = -3;
      int hi = 3;
      java.util.Arrays.fill(x, lo);
      while (true) {
        boolean solution = true;
        for (int i = 0; i < m && solution; i++) {
          long sum = 0;
          for (int j = 0; j < n; j++) {
            sum += a[i][j] * x[j];
          }
          solution = sum == b[i];
        }
        if (solution) {
          assertThat(s).as("trial %d", t).isNotNull();
        }
        if (s != null && (solution || r.nextInt(64) == 0)) {
          assertThat(inLattice(x, s))
              .as("trial %d at %s", t, java.util.Arrays.toString(x))
              .isEqualTo(solution);
        }
        int k = 0;
        while (k < n && x[k] == hi) {
          x[k++] = lo;
        }
        if (k == n) {
          break;
        }
        x[k]++;
      }
    }
  }

  // x - x0 in the lattice: solve over the rationals by fraction-free elimination on the basis
  private static boolean inLattice(int[] x, IntLattice.Solutions s) {
    int n = x.length;
    BigInteger[][] basis = s.basis();
    int d = basis.length;
    // matrix [B^T | x - x0], n rows, d + 1 columns, reduced over the integers by Euclid row steps
    BigInteger[][] mat = new BigInteger[n][d + 1];
    for (int j = 0; j < n; j++) {
      for (int k = 0; k < d; k++) {
        mat[j][k] = basis[k][j];
      }
      mat[j][d] = BigInteger.valueOf(x[j]).subtract(s.x0()[j]);
    }
    int row = 0;
    for (int c = 0; c < d && row < n; c++) {
      // Euclid on column c over rows row..n-1 (unimodular row operations keep the lattice question)
      while (true) {
        int p = -1;
        for (int i = row; i < n; i++) {
          if (mat[i][c].signum() != 0
              && (p < 0 || mat[i][c].abs().compareTo(mat[p][c].abs()) < 0)) {
            p = i;
          }
        }
        if (p < 0) {
          break;
        }
        BigInteger[] t = mat[p];
        mat[p] = mat[row];
        mat[row] = t;
        boolean clean = true;
        for (int i = row + 1; i < n; i++) {
          if (mat[i][c].signum() != 0) {
            BigInteger q = mat[i][c].divide(mat[row][c]);
            for (int k = c; k <= d; k++) {
              mat[i][k] = mat[i][k].subtract(q.multiply(mat[row][k]));
            }
            clean &= mat[i][c].signum() == 0;
          }
        }
        if (clean) {
          row++;
          break;
        }
      }
    }
    for (int i = row; i < n; i++) {
      if (mat[i][d].signum() != 0) {
        return false;
      }
    }
    // back substitution over the integers on the echelon rows
    BigInteger[] lambda = new BigInteger[d];
    int r = row - 1;
    for (int c = d - 1; c >= 0; c--) {
      // find the echelon row with leading column c
      int lead = -1;
      for (int i = 0; i < row; i++) {
        int first = 0;
        while (first < d && mat[i][first].signum() == 0) {
          first++;
        }
        if (first == c) {
          lead = i;
        }
      }
      if (lead < 0) {
        lambda[c] = BigInteger.ZERO;
        continue;
      }
      BigInteger v = mat[lead][d];
      for (int k = c + 1; k < d; k++) {
        v = v.subtract(mat[lead][k].multiply(lambda[k]));
      }
      BigInteger[] qr = v.divideAndRemainder(mat[lead][c]);
      if (qr[1].signum() != 0) {
        return false;
      }
      lambda[c] = qr[0];
    }
    assertThat(r).isGreaterThanOrEqualTo(-1);
    // check exactly
    for (int j = 0; j < n; j++) {
      BigInteger v = s.x0()[j];
      for (int k = 0; k < d; k++) {
        v = v.add(lambda[k].multiply(basis[k][j]));
      }
      if (!v.equals(BigInteger.valueOf(x[j]))) {
        return false;
      }
    }
    return true;
  }

  @Test
  void randomSystemsKeepTheirSolutions() {
    Random r = new Random(11);
    long pruned = 0;
    int reformulated = 0;
    int infeasible = 0;
    for (int t = 0; t < SYSTEMS; t++) {
      int m = 1 + r.nextInt(3);
      int n = 2 + r.nextInt(4);
      int lo = r.nextInt(4) - 3;
      int hi = lo + 2 + r.nextInt(6);
      int[][] a = new int[m][n];
      int[] b = new int[m];
      for (int i = 0; i < m; i++) {
        int mult = 1 + r.nextInt(3);
        for (int j = 0; j < n; j++) {
          a[i][j] = r.nextInt(5) == 0 ? 0 : (r.nextInt(7) - 3) * (r.nextInt(3) == 0 ? 1 : mult);
        }
        if (r.nextInt(4) == 0) {
          a[i][r.nextInt(n)] = r.nextBoolean() ? 1 : -1;
        }
        b[i] = r.nextInt(15) - 7;
      }
      long expected = bruteForce(a, b, n, lo, hi);
      boolean reformulate = r.nextBoolean();
      Store store = new Store();
      IntVar[] x = vars(store, n, lo, hi);
      List<LinearEqualities.Row> rows = new ArrayList<>();
      for (int i = 0; i < m; i++) {
        store.impose(new LinearInt(x, a[i], "==", b[i]));
        rows.add(new LinearEqualities.Row(x, a[i], b[i]));
      }
      LinearEqualities le = new LinearEqualities(store);
      le.setReformulate(reformulate);
      long found;
      try {
        le.apply(rows);
        found = count(store, x, le.lattice);
      } catch (FailException e) {
        found = 0;
        infeasible++;
      }
      assertThat(found)
          .as(
              "trial %d: %s = %s over %d..%d, reformulate %b",
              t,
              java.util.Arrays.deepToString(a),
              java.util.Arrays.toString(b),
              lo,
              hi,
              reformulate)
          .isEqualTo(expected);
      pruned += le.prunedValues;
      reformulated += le.lattice.isEmpty() ? 0 : 1;
    }
    assertThat(pruned).isPositive();
    assertThat(reformulated).isPositive();
    assertThat(infeasible).isPositive();
  }

  private static long bruteForce(int[][] a, int[] b, int n, int lo, int hi) {
    int[] x = new int[n];
    java.util.Arrays.fill(x, lo);
    long count = 0;
    while (true) {
      boolean ok = true;
      for (int i = 0; i < a.length && ok; i++) {
        long s = 0;
        for (int j = 0; j < n; j++) {
          s += (long) a[i][j] * x[j];
        }
        ok = s == b[i];
      }
      if (ok) {
        count++;
      }
      int k = 0;
      while (k < n && x[k] == hi) {
        x[k++] = lo;
      }
      if (k == n) {
        return count;
      }
      x[k]++;
    }
  }

  private static long count(Store store, IntVar[] x, List<IntVar> lattice) {
    if (!store.consistency()) {
      return 0;
    }
    IntVar[] all = new IntVar[lattice.size() + x.length];
    for (int k = 0; k < lattice.size(); k++) {
      all[k] = lattice.get(k);
    }
    System.arraycopy(x, 0, all, lattice.size(), x.length);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    SimpleSelect<IntVar> select = new SimpleSelect<>(all, null, new IndomainMin<>());
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setPrintInfo(false);
    search.labeling(store, select);
    return search.getSolutionListener().solutionsNo();
  }
}
