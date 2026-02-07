/*
 * Matrix.java
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

package org.jacop.floats.util;

import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatIntervalDomain;

/**
 * Matrix and operations on matrices.
 *
 * <p>This class was moved from org.jacop.util to org.jacop.floats.util as it has float-specific
 * dependencies and is only used in float constraints.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.11
 */
public class Matrix {

  final double[][] A;

  /**
   * Constructs a matrix from a two-dimensional array.
   *
   * @param matrix the source matrix to copy
   */
  public Matrix(double[][] matrix) {

    A = new double[matrix.length][];
    for (int i = 0; i < matrix.length; i++) {
      A[i] = new double[matrix[i].length];
      System.arraycopy(matrix[i], 0, A[i], 0, matrix[i].length);
    }
  }

  /**
   * Multiplies an interval matrix by a double matrix.
   *
   * @param f the interval matrix (m x n)
   * @param b the double matrix (n x p)
   * @return the resulting interval domain matrix (m x p), or null if dimensions are incompatible
   */
  public static FloatIntervalDomain[][] mult(
      FloatInterval[][] f, double[][] b) { // f[m][n] * b[n][p]

    if (f.length == 0) {
      return new FloatIntervalDomain[0][0];
    }
    if (f[0].length != b.length) {
      return null; // incorrect sizes
    }
    int n = f[0].length;
    int m = f.length;
    int p = b[0].length;

    FloatIntervalDomain[][] result = new FloatIntervalDomain[m][p];
    for (int i = 0; i < result.length; i++) {
      for (int j = 0; j < result[i].length; j++) {
        result[i][j] = new FloatIntervalDomain(0.0, 0.0);
      }
    }

    for (int i = 0; i < m; i++) {
      for (int j = 0; j < p; j++) {
        for (int k = 0; k < n; k++) {
          FloatIntervalDomain mBound =
              FloatDomain.mulBounds(f[i][k].min(), f[i][k].max(), b[k][j], b[k][j]);
          result[i][j] =
              FloatDomain.addBounds(
                  result[i][j].min(), result[i][j].max(), mBound.min(), mBound.max());
        }
      }
    }

    return result;
  }

  /**
   * Multiplies this matrix by another matrix.
   *
   * @param b the matrix to multiply by (n x p)
   * @return the resulting matrix (m x p), or null if dimensions are incompatible
   */
  // A*m
  public double[][] mult(double[][] b) { // A[m][n] * b[n][p]

    if (A.length == 0) {
      return new double[0][0];
    }
    if (A[0].length != b.length) {
      return null; // invalid dims
    }
    int n = A[0].length;
    int m = A.length;
    int p = b[0].length;

    double[][] result = new double[m][p];

    for (int i = 0; i < m; i++) {
      for (int j = 0; j < p; j++) {
        for (int k = 0; k < n; k++) {
          result[i][j] += A[i][k] * b[k][j];
        }
      }
    }
    return result;
  }

  /**
   * Multiplies this matrix by a vector.
   *
   * @param b the vector to multiply by (length n)
   * @return the resulting vector (length m), or null if dimensions are incompatible
   */
  // A*m
  public double[] mult(double[] b) { // A[m][n] * b[n]

    if (A.length == 0) {
      return new double[0];
    }
    if (A[0].length != b.length) {
      return null; // invalid dims
    }
    int m = A.length;
    int p = b.length;

    double[] result = new double[m];

    for (int i = 0; i < m; i++) {
      for (int j = 0; j < p; j++) {
        result[i] += A[i][j] * b[j];
      }
    }
    return result;
  }

  /**
   * Computes the determinant of this matrix.
   *
   * @return the determinant value
   */
  public double determinant() {
    return determinant(A);
  }

  /**
   * Computes the determinant of a given matrix.
   *
   * @param matrix the matrix to compute determinant for
   * @return the determinant value
   */
  public double determinant(double[][] matrix) {

    if (!isSquare(matrix)) {
      throw new ArithmeticException("Trying to compute determinat on non-square matrix; aborted");
    }
    if (matrix.length == 1) {
      return matrix[0][0];
    }
    if (matrix.length == 2) {
      return (matrix[0][0] * matrix[1][1]) - (matrix[0][1] * matrix[1][0]);
    }
    double sum = 0.0;
    for (int i = 0; i < matrix[0].length; i++) {
      sum += sign(i) * matrix[0][i] * determinant(subMatrix(matrix, 0, i));
    }
    return sum;
  }

  /**
   * Computes the cofactor matrix.
   *
   * @param m the input matrix
   * @return the cofactor matrix
   */
  public double[][] cofactor(double[][] m) {

    double[][] t = new double[m.length][m[0].length];

    for (int i = 0; i < m.length; i++) {
      for (int j = 0; j < m[i].length; j++) {
        t[i][j] = sign(i) * sign(j) * determinant(subMatrix(m, i, j));
      }
    }

    return t;
  }

  /**
   * Computes the transpose of a matrix.
   *
   * @param m the input matrix
   * @return the transposed matrix
   */
  public double[][] transpose(double[][] m) {

    double[][] t = new double[m[0].length][m.length];
    for (int i = 0; i < m.length; i++) {
      for (int j = 0; j < m[i].length; j++) {
        t[j][i] = m[i][j];
      }
    }

    return t;
  }

  /**
   * Computes the inverse of this matrix.
   *
   * @return the inverse matrix
   */
  public double[][] inverse() {
    return inverse(A);
  }

  /**
   * Computes the inverse of a given matrix.
   *
   * @param m the input matrix
   * @return the inverse matrix
   */
  public double[][] inverse(double[][] m) {

    return multiplyByConstant(transpose(cofactor(m)), 1.0 / determinant(m));
  }

  double[][] multiplyByConstant(double[][] m, double c) {

    double[][] t = new double[m[0].length][m.length];
    for (int i = 0; i < m.length; i++) {
      for (int j = 0; j < m[i].length; j++) {
        t[i][j] = m[i][j] * c;
      }
    }

    return t;
  }

  double[][] subMatrix(double[][] s, int r, int c) {

    double[][] subMatrix = new double[s.length - 1][s.length - 1];

    int k = 0;
    for (int i = 0; i < s.length; i++) {
      int l = 0;
      if (i != r) {
        for (int j = 0; j < s[i].length; j++) {
          if (j != c) {
            subMatrix[k][l++] = s[i][j];
          }
        }
        k++;
      }
    }

    return subMatrix;
  }

  double sign(int n) {

    if (n % 2 == 0) {
      return 1.0;
    } else {
      return -1.0;
    }
  }

  boolean isSquare(double[][] matrix) {
    boolean square = true;

    int n = matrix.length;
    for (double[] doubles : matrix) {
      if (doubles.length != n) {
        square = false;
        break;
      }
    }

    return square;
  }

  void print(double[][] matrix) {
    for (double[] doubles : matrix) {
      for (double aDouble : doubles) {
        IO.print(aDouble + " ");
      }
      IO.println();
    }
  }
}
