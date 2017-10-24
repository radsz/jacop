/*
 * IntervalGaussSeidel.java
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

package org.jacop.floats.constraints;

import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.util.Matrix;

import java.util.Arrays;


/**
 * IntervalGaussSeidel implements Gauss-Seidel method for solving a
 * system of linear equations Ax = b with interval matrix A of
 * coefficients.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class IntervalGaussSeidel {

    final static boolean debug = false;

    int MaxIterations = 100;

    FloatInterval[][] A;
    double[] b;

    public IntervalGaussSeidel(FloatInterval[][] A, double[] b) {

        this.A = new FloatInterval[A.length][];
        for (int i = 0; i < A.length; i++) {
            this.A[i] = new FloatInterval[A[i].length];
            System.arraycopy(A[i], 0, this.A[i], 0, A[i].length);
        }
        this.b = new double[b.length];
        System.arraycopy(b, 0, this.b, 0, b.length);
    }

    double minAbs(FloatInterval v) {

        if (v.min() <= 0 && v.max() >= 0)
            return 0;

        double vMin = Math.abs(v.min());
        double vMax = Math.abs(v.max());

        return (vMax < vMin) ? vMax : vMin;
    }

    double maxAbs(FloatInterval v) {

        double vMin = Math.abs(v.min());
        double vMax = Math.abs(v.max());

        return (vMax > vMin) ? vMax : vMin;
    }

    public boolean restructure(int currentRow, boolean[] done, int[] row) {

        if (currentRow == A.length) {
            FloatInterval[][] tempA = new FloatInterval[A.length][A.length];
            double[] tempb = new double[A.length];
            for (int i = 0; i < A.length; i++) {
                tempb[i] = b[row[i]];
                for (int j = 0; j < A[i].length; j++) {
                    tempA[i][j] = A[row[i]][j];
                }
            }

            A = tempA;
            b = tempb;

            return true;
        }

        for (int i = 0; i < A.length; i++) {
            if (done[i])
                continue;

            double sumMax = 0;

            for (int j = 0; j < A.length; j++)
                if (j != currentRow)
                    sumMax += maxAbs(A[i][j]);

            if (minAbs(A[i][currentRow]) > sumMax) { // interval version of diagonal dominance
                done[i] = true;
                row[currentRow] = i;

                if (restructure(currentRow + 1, done, row))
                    return true;

                done[i] = false;
            }
        }
        return false;
    }


    public FloatInterval[] solve() {
        int N = 0;
        FloatInterval[] x = new FloatInterval[b.length];
        ;
        FloatInterval[] previousX = new FloatInterval[x.length];
        for (int i = 0; i < x.length; i++)
            x[i] = new FloatInterval(0.0, 0.0);

        boolean[] d = new boolean[A.length];
        Arrays.fill(d, false);
        int[] r = new int[A.length];
        boolean dominant = restructure(0, d, r);

        if (!dominant) {

            // try to precondition to make it non-dominant
            // current method for computing preconditioner is far too slow
            // and need to be improved.

            precondition(A, b);

            d = new boolean[A.length];
            Arrays.fill(d, false);
            r = new int[A.length];
            dominant = restructure(0, d, r);

            if (!dominant)
                return null;
        }

        if (debug) {
            System.out.println("dominant = " + dominant + " ===================================");
            for (int i = 0; i < A.length; i++) {
                for (int j = 0; j < A[i].length; j++) {
                    if (A[i][j].min <= 0 && A[i][j].max() >= 0)
                        System.out.print("0 ");
                    else if (A[i][j].min() > 0)
                        System.out.print("+ ");
                    else if (A[i][j].min() < 0)
                        System.out.print("- ");
                    else
                        System.out.print("? ");
                }
                System.out.println();
            }
        }

        while (true) {

            for (int i = 0; i < b.length; i++) {
                FloatIntervalDomain sum = new FloatIntervalDomain(b[i], b[i]);

                for (int j = 0; j < A[i].length; j++)
                    if (j != i) {
                        FloatIntervalDomain v1 = FloatDomain.mulBounds(A[i][j].min(), A[i][j].max(), x[j].min(), x[j].max());
                        sum = FloatDomain.subBounds(sum.min(), sum.max(), v1.min(), v1.max());
                    }


                FloatIntervalDomain w = FloatDomain.divBounds(sum.min(), sum.max(), A[i][i].min(), A[i][i].max());
                x[i] = new FloatInterval(w.min(), w.max());
            }

            if (debug) {
                System.out.print("iteration " + N + ": {");
                for (int i = 0; i < x.length; i++) {
                    if (i == x.length - 1)
                        System.out.print(x[i]);
                    else
                        System.out.print(x[i] + ", ");
                }
                System.out.println("}");
            }

            if (N == 0) {
                N++;
                for (int i = 0; i < x.length; i++)
                    previousX[i] = (FloatInterval) x[i].clone();

                continue;
            } else {
                N++;
                if (N == MaxIterations)
                    break;
            }

            boolean converged = true;
            for (int i = 0; i < x.length; i++)
                if (!x[i].eq(previousX[i]))
                    converged = false;

            if (converged)
                break;

            for (int i = 0; i < x.length; i++)
                previousX[i] = (FloatInterval) x[i].clone();

        }

        return x;
    }

    void precondition(FloatInterval[][] AA, double[] bb) {

        if (debug)
            System.out.println("Before preconditioning\n" + this);

        double[][] midPoint = new double[AA.length][AA[0].length];

        for (int i = 0; i < midPoint.length; i++)
            for (int j = 0; j < midPoint[i].length; j++)
                midPoint[i][j] = (AA[i][j].min() + AA[i][j].max()) / 2;

        Matrix m = new Matrix(midPoint);

        double[][] inv = m.inverse();

        FloatInterval[][] F = new FloatInterval[AA.length][A[0].length];
        for (int i = 0; i < F.length; i++)
            for (int j = 0; j < F[0].length; j++)
                F[i][j] = new FloatInterval(AA[i][j].min(), AA[i][j].max());

        FloatIntervalDomain[][] newA = Matrix.mult(F, inv);
        Matrix comp = new Matrix(inv);
        double[] newB = comp.mult(bb);

        A = new FloatInterval[newA.length][newA[0].length];
        for (int i = 0; i < newA.length; i++)
            for (int j = 0; j < newA[i].length; j++)
                A[i][j] = new FloatInterval(newA[i][j].min(), newA[i][j].max());
        b = newB;

        if (debug)
            System.out.println("After preconditioning\n" + this);

    }

    public String toString() {

        StringBuffer s = new StringBuffer();

        for (int i = 0; i < A.length; i++) {
            for (int j = 0; j < A[i].length; j++)
                s.append(A[i][j] + " ");
            s.append(" = " + b[i] + "\n");
        }

        return s.toString();
    }

}
