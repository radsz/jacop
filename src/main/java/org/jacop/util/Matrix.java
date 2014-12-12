/**
 *  Matrix.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.util;

import java.lang.ArithmeticException;

import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;

/**
 * Matrix and operations on matrices.
 *  
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Matrix {

    double[][] A;

    public Matrix(double[][] M) {
	A = M;
    }

    public double determinant() {
	return determinant(A);
    }

    public double determinant(double[][] M) {

	// System.out.println ("========");
	// print (M);

	if (! isSquare(M))
	    throw new ArithmeticException("Trying to compute determinat on non-square matrix; aborted");
	if (M.length == 1) {
	    return M[0][0];
	}
	if (M.length == 2) {
	    return (M[0][0] * M[1][1]) - ( M[0][1] * M[1][0]);
	}
	double sum = 0.0;
	for (int i=0; i < M[0].length; i++) {
	    sum += sign(i) * M[0][i] * determinant(subMatrix(M, 0, i));
	}
	return sum;
    }

    public double[][] cofactor(double[][] m) {

	double[][] t = new double[m.length][m[0].length];

	for (int i = 0; i < m.length; i++) {
	    for (int j = 0; j < m[i].length; j++) 
		t[i][j] = sign(i) * sign(j) * determinant(subMatrix(m, i, j));
	}
    
	return t;
    }


    public double[][] transpose(double[][] m) {

	double[][] t = new double[m[0].length][m.length];
	for (int i = 0; i < m.length;i++) 
	    for (int j = 0; j < m[i].length; j++) 
		t[j][i] = m[i][j];

	return t;
    } 

    public double[][] inverse() {
	return inverse(A);
    }

    public double[][] inverse(double[][] m) {

	return multiplyByConstant(transpose(cofactor(m)), 1.0/determinant(m));
    }


    // A*m
    public double[][] mult(double[][] b){ //A[m][n] * b[n][p]

	if(A.length == 0) return new double[0][0];
	if(A[0].length != b.length) 
	    return null; //invalid dims
 
	int n = A[0].length;
	int m = A.length;
	int p = b[0].length;
 
	double[][] result = new double[m][p];
 
	for(int i = 0; i < m; i++){
	    for(int j = 0; j < p; j++){
		for(int k = 0; k < n; k++){
		    result[i][j] += A[i][k] * b[k][j];
		}
	    }
	}
	return result;
    }

    // A*m
    public double[] mult(double[] b){ //A[m][n] * b[n]

	if(A.length == 0) return new double[0];
	if(A[0].length != b.length) 
	    return null; //invalid dims
 
	int n = A[0].length;
	int m = A.length;
	int p = b.length;
 
	double[] result = new double[m];
 
	for(int i = 0; i < m; i++){
	    for(int j = 0; j < p; j++){
		    result[i] += A[i][j] * b[j];
	    }
	}
	return result;
    }

    public static FloatIntervalDomain[][] mult(FloatInterval[][] F, double[][] b){ //F[m][n] * b[n][p]

	if(F.length == 0) return new FloatIntervalDomain[0][0];
	if(F[0].length != b.length) 
	    return null; // incorrect sizes
 
	int n = F[0].length;
	int m = F.length;
	int p = b[0].length;
 
	FloatIntervalDomain[][] result = new FloatIntervalDomain[m][p];
	for (int i = 0; i < result.length; i++) 
	    for (int j = 0; j < result[i].length; j++) 
		result[i][j] = new FloatIntervalDomain(0.0, 0.0);

	for(int i = 0; i < m; i++)
	    for(int j = 0; j < p; j++)
		for(int k = 0; k < n; k++) {
		    FloatIntervalDomain mBound = FloatDomain.mulBounds(F[i][k].min(), F[i][k].max(), b[k][j], b[k][j]);
		    result[i][j] = FloatDomain.addBounds(result[i][j].min(), result[i][j].max(), mBound.min(), mBound.max());
		}

	return result;
    }

    double[][] multiplyByConstant(double[][] m, double c) {

	double[][] t = new double[m[0].length][m.length];
	for (int i = 0; i < m.length;i++) 
	    for (int j = 0; j < m[i].length; j++) 
		t[i][j] = m[i][j] * c;

	return t;
	
    }

    double[][] subMatrix(double[][] s, int r, int c) {

	double[][] subMatrix = new double[s.length-1][s.length-1];

	int k=0;
	for (int i = 0; i < s.length; i++) {
	    int l=0;
	    if (i != r) {
		for (int j = 0; j < s[i].length; j++) {
		    if (j != c) 
			subMatrix[k][l++] = s[i][j];
		}
		k++;
	    }
	}

	return subMatrix;
    }

    double sign(int n) {

	if (n % 2 == 0)
	    return 1.0;
	else
	    return -1.0;
    }

    boolean isSquare(double[][] M) {
	boolean square = true;

	int n = M.length;
	for (int i = 0; i < M.length; i++) 
	    if (M[i].length != n)
		square = false;

	return square;
    }

    void print(double[][] M) {
	for (int i = 0; i < M.length; i++) {
	    for (int j = 0; j < M[i].length; j++) 
		System.out.print (M[i][j] + " ");
	    System.out.println ();
	}
    }
}
