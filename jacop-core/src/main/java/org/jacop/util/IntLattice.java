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
package org.jacop.util;

import java.math.BigInteger;

/**
 * Integer lattices of linear equality systems: the integer solutions of A x = b, as a particular
 * solution and a basis of the lattice {x ∈ Z^n : A x = 0}, and the Lenstra-Lenstra-Lovász reduction
 * of that basis.
 *
 * <p>The solutions come from a column Hermite normal form: unimodular column operations (each an
 * extended Euclid step on two columns) turn A into [H | 0] with H lower triangular, A U = [H | 0].
 * Then A x = b has an integer solution if and only if H y = b has one, which forward substitution
 * finds, and the solutions are x = U (y, z) for every integer z: the particular solution U (y, 0)
 * plus the lattice spanned by the last n - rank columns of U (Hermite 1851; Kannan and Bachem, SIAM
 * J. Computing 8(4), 1979; Cohen, A Course in Computational Algebraic Number Theory, 1993, §2.4).
 *
 * <p>The reduction is LLL (Lenstra, Lenstra and Lovász, Math. Annalen 261, 1982) with δ = 0.99, on
 * exact integer vectors with a floating-point Gram-Schmidt orthogonalisation, as in Schnorr and
 * Euchner (Math. Programming 66, 1994). The basis stays a basis of the same lattice whatever the
 * rounding, since every step is an exact unimodular operation; rounding can only make it less
 * reduced. Aardal, Hurkens and Lenstra (Math. of OR 25(3), 2000) solve market split problems by
 * branching on the coordinates of such a reduced basis.
 *
 * <p>All arithmetic is exact ({@link BigInteger}) except the Gram-Schmidt coefficients.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class IntLattice {

  /** Bit length of an entry of the Hermite normal form or of U beyond which solve gives up. */
  static final int MAX_BITS = 256;

  private IntLattice() {}

  /**
   * The integer solutions of a system: x = x0 + Σ_k z_k basis[k] for integer z.
   *
   * @param x0 a particular solution.
   * @param basis the basis of the lattice of solutions of the homogeneous system, one vector per
   *     row; empty when the solution is unique.
   */
  public record Solutions(BigInteger[] x0, BigInteger[][] basis) {}

  /**
   * It computes the integer solutions of a x = b.
   *
   * @param a the coefficients, one row per equation, each of the same length n.
   * @param b the right-hand sides.
   * @param n the number of variables.
   * @return the solutions, or null when the system has no integer solution.
   * @throws ArithmeticException when an entry of the computation grows beyond MAX_BITS bits.
   */
  public static Solutions solve(long[][] a, long[] b, int n) {
    int m = a.length;
    BigInteger[][] h = new BigInteger[m][n];
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        h[i][j] = BigInteger.valueOf(a[i][j]);
      }
    }
    // u[j] is column j of U
    BigInteger[][] u = new BigInteger[n][n];
    for (int j = 0; j < n; j++) {
      for (int k = 0; k < n; k++) {
        u[j][k] = j == k ? BigInteger.ONE : BigInteger.ZERO;
      }
    }
    int rank = 0;
    int[] pivot = new int[m];
    for (int i = 0; i < m; i++) {
      eliminate(h, u, i, rank);
      if (rank < n && h[i][rank].signum() != 0) {
        if (h[i][rank].signum() < 0) {
          negate(h, u, rank);
        }
        pivot[i] = rank++;
      } else {
        pivot[i] = -1;
      }
    }
    // forward substitution in H y = b
    BigInteger[] y = new BigInteger[rank];
    for (int i = 0; i < m; i++) {
      BigInteger s = BigInteger.valueOf(b[i]);
      int known = pivot[i] >= 0 ? pivot[i] : rank;
      for (int c = 0; c < known && c < rank; c++) {
        if (y[c] != null && h[i][c].signum() != 0) {
          s = s.subtract(h[i][c].multiply(y[c]));
        }
      }
      if (pivot[i] >= 0) {
        BigInteger[] qr = s.divideAndRemainder(h[i][pivot[i]]);
        if (qr[1].signum() != 0) {
          return null;
        }
        y[pivot[i]] = qr[0];
      } else if (s.signum() != 0) {
        return null;
      }
    }
    BigInteger[] x0 = new BigInteger[n];
    for (int k = 0; k < n; k++) {
      BigInteger s = BigInteger.ZERO;
      for (int c = 0; c < rank; c++) {
        s = s.add(u[c][k].multiply(y[c]));
      }
      x0[k] = s;
    }
    BigInteger[][] basis = new BigInteger[n - rank][];
    for (int c = rank; c < n; c++) {
      basis[c - rank] = u[c];
    }
    return new Solutions(x0, basis);
  }

  /**
   * Zeroes row i of h right of column r by unimodular column steps: the column with the smallest
   * nonzero entry goes to r and the nearest multiple of it is subtracted from the others, until
   * column r is the only nonzero one (Euclid on the whole row at once). Unlike pairwise extended
   * Euclid, a unit entry needs no multiplication of whole columns, which keeps the entries of U
   * small.
   *
   * @throws ArithmeticException when an entry grows beyond MAX_BITS.
   */
  private static void eliminate(BigInteger[][] h, BigInteger[][] u, int i, int r) {
    int n = u.length;
    while (r < n) {
      int best = -1;
      for (int j = r; j < n; j++) {
        if (h[i][j].signum() != 0 && (best < 0 || h[i][j].abs().compareTo(h[i][best].abs()) < 0)) {
          best = j;
        }
      }
      if (best < 0) {
        return;
      }
      swap(h, u, r, best);
      boolean done = true;
      BigInteger p = h[i][r];
      for (int j = r + 1; j < n; j++) {
        if (h[i][j].signum() != 0) {
          // nearest integer to h[i][j] / p
          BigInteger[] qr = h[i][j].divideAndRemainder(p);
          BigInteger q = qr[0];
          if (qr[1].abs().shiftLeft(1).compareTo(p.abs()) > 0) {
            q = q.add(BigInteger.valueOf(qr[1].signum() * p.signum()));
          }
          subtract(h, u, j, r, q);
          if (h[i][j].signum() != 0) {
            done = false;
          }
        }
      }
      if (done) {
        return;
      }
    }
  }

  // column j -= q column r, in h and u
  private static void subtract(BigInteger[][] h, BigInteger[][] u, int j, int r, BigInteger q) {
    for (BigInteger[] row : h) {
      if (row[r].signum() != 0) {
        row[j] = checked(row[j].subtract(q.multiply(row[r])));
      }
    }
    BigInteger[] uj = u[j];
    BigInteger[] ur = u[r];
    for (int k = 0; k < uj.length; k++) {
      if (ur[k].signum() != 0) {
        uj[k] = checked(uj[k].subtract(q.multiply(ur[k])));
      }
    }
  }

  private static BigInteger checked(BigInteger v) {
    if (v.bitLength() > MAX_BITS) {
      throw new ArithmeticException("lattice entries beyond " + MAX_BITS + " bits");
    }
    return v;
  }

  private static void swap(BigInteger[][] h, BigInteger[][] u, int r, int j) {
    if (r == j) {
      return;
    }
    for (BigInteger[] row : h) {
      BigInteger t = row[r];
      row[r] = row[j];
      row[j] = t;
    }
    BigInteger[] t = u[r];
    u[r] = u[j];
    u[j] = t;
  }

  private static void negate(BigInteger[][] h, BigInteger[][] u, int r) {
    for (BigInteger[] row : h) {
      row[r] = row[r].negate();
    }
    for (int k = 0; k < u[r].length; k++) {
      u[r][k] = u[r][k].negate();
    }
  }

  /**
   * It LLL-reduces a lattice basis in place (δ = 0.99). The vectors must be linearly independent,
   * as those of {@link #solve} are.
   *
   * @param basis the basis, one vector per row.
   * @param maxSteps the most swaps made before it stops; the basis is a basis of the same lattice
   *     whenever it stops.
   * @return false if it stopped at maxSteps or on entries too large for doubles.
   */
  public static boolean reduce(BigInteger[][] basis, int maxSteps) {
    int d = basis.length;
    if (d <= 1) {
      return true;
    }
    int n = basis[0].length;
    double[][] star = new double[d][n];
    double[] norms = new double[d];
    double[][] mu = new double[d][d];
    if (!orthogonalise(basis, star, norms, mu, 0)) {
      return false;
    }
    int k = 1;
    int steps = 0;
    while (k < d) {
      // size reduction, repeated since a large coefficient is only rounded to double precision
      for (int round = 0; round < 64; round++) {
        boolean changed = false;
        for (int j = k - 1; j >= 0; j--) {
          double q = Math.rint(mu[k][j]);
          if (q != 0) {
            changed = true;
            BigInteger bq = new java.math.BigDecimal(q).toBigInteger();
            for (int c = 0; c < n; c++) {
              basis[k][c] = basis[k][c].subtract(bq.multiply(basis[j][c]));
            }
            for (int i = 0; i < j; i++) {
              mu[k][i] -= q * mu[j][i];
            }
            mu[k][j] -= q;
          }
        }
        if (!orthogonalise(basis, star, norms, mu, k)) {
          return false;
        }
        if (!changed) {
          break;
        }
      }
      if (norms[k] >= (0.99 - mu[k][k - 1] * mu[k][k - 1]) * norms[k - 1]) {
        k++;
        if (k < d && !orthogonalise(basis, star, norms, mu, k)) {
          return false;
        }
      } else {
        if (++steps > maxSteps) {
          return false;
        }
        BigInteger[] t = basis[k];
        basis[k] = basis[k - 1];
        basis[k - 1] = t;
        k = Math.max(k - 1, 1);
        if (!orthogonalise(basis, star, norms, mu, k - 1)) {
          return false;
        }
        if (!orthogonalise(basis, star, norms, mu, k)) {
          return false;
        }
      }
    }
    return true;
  }

  // the Gram-Schmidt vector and coefficients of row k from rows 0..k-1 (from row from on when
  // from == 0 is asked: all rows)
  private static boolean orthogonalise(
      BigInteger[][] basis, double[][] star, double[] norms, double[][] mu, int k) {
    int last = k;
    int first = k;
    if (k == 0) {
      last = basis.length - 1;
    }
    for (int r = first; r <= last; r++) {
      int n = basis[r].length;
      double[] v = new double[n];
      for (int c = 0; c < n; c++) {
        if (basis[r][c].bitLength() > 900) {
          return false;
        }
        v[c] = basis[r][c].doubleValue();
      }
      double[] s = v.clone();
      for (int j = 0; j < r; j++) {
        double dot = 0;
        for (int c = 0; c < n; c++) {
          dot += v[c] * star[j][c];
        }
        mu[r][j] = norms[j] == 0 ? 0 : dot / norms[j];
        for (int c = 0; c < n; c++) {
          s[c] -= mu[r][j] * star[j][c];
        }
      }
      star[r] = s;
      double norm = 0;
      for (int c = 0; c < n; c++) {
        norm += s[c] * s[c];
      }
      norms[r] = norm;
      if (!Double.isFinite(norm)) {
        return false;
      }
    }
    return true;
  }

  /**
   * It moves a particular solution by lattice vectors close to a target point (Babai's nearest
   * plane, Combinatorica 6, 1986), so that the coordinates of the solutions in a box around the
   * target are small. The result is exact: only integer multiples of basis vectors are added.
   *
   * @param x0 the particular solution, changed in place.
   * @param basis the (reduced) basis.
   * @param target the point.
   */
  public static void closest(BigInteger[] x0, BigInteger[][] basis, double[] target) {
    int d = basis.length;
    if (d == 0) {
      return;
    }
    int n = x0.length;
    double[][] star = new double[d][n];
    double[] norms = new double[d];
    double[][] mu = new double[d][d];
    if (!orthogonalise(basis, star, norms, mu, 0)) {
      return;
    }
    for (int pass = 0; pass < 8; pass++) {
      double[] t = new double[n];
      for (int c = 0; c < n; c++) {
        t[c] = x0[c].doubleValue() - target[c];
      }
      boolean moved = false;
      for (int k = d - 1; k >= 0; k--) {
        if (norms[k] == 0) {
          continue;
        }
        double dot = 0;
        for (int c = 0; c < n; c++) {
          dot += t[c] * star[k][c];
        }
        double q = Math.rint(dot / norms[k]);
        if (q != 0 && Double.isFinite(q)) {
          moved = true;
          BigInteger bq = new java.math.BigDecimal(q).toBigInteger();
          for (int c = 0; c < n; c++) {
            x0[c] = x0[c].subtract(bq.multiply(basis[k][c]));
            t[c] -= q * basis[k][c].doubleValue();
          }
        }
      }
      if (!moved) {
        return;
      }
    }
  }
}
