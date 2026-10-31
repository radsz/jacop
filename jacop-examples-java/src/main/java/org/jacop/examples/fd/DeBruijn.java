/*
 * DeBruijn.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Hakan Kjellerstrand and Radoslaw Szymanek
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

package org.jacop.examples.fd;

import java.util.ArrayList;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Min;
import org.jacop.constraints.XeqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * A program solving problem of finding de Bruijn sequences.
 *
 * <p>It finds both "normal" and "arbitrary" de Bruijn sequences.
 *
 * <p>This is a port from my MiniZinc model <a
 * href="http://www.hakank.org/minizinc/debruijn_binary.mzn">...</a>
 *
 * <p>and is explained somewhat in the swedish blog post "Constraint Programming: Minizinc,
 * Gecode/flatzinc och ECLiPSe/minizinc" <a
 * href="http://www.hakank.org/webblogg/archives/001209.html">...</a>
 *
 * <p>Related programs: - "Normal" de Bruijn sequences CGI program for calculating the sequences <a
 * href="http://www.hakank.org/comb/debruijn.cgi">...</a> <a
 * href="http://www.hakank.org/comb/deBruijnApplet.html">...</a> (as Java applet)
 *
 * <p>- "Arbitrary" de Bruijn sequences Program "de Bruijn arbitrary sequences" <a
 * href="http://www.hakank.org/comb/debruijn_arb.cgi">...</a>
 *
 * <p>This (swedish) blog post explains the program: "de Bruijn-sekvenser av godtycklig längd" <a
 * href="http://www.hakank.org/webblogg/archives/001114.html">...</a>
 *
 * @author Hakan Kjellerstrand (hakank@bonetmail.com) and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class DeBruijn extends ExampleFd {

  // These parameters may be set by the user:
  //  - base
  //  - n
  //  - m
  public int base = 4; // the base to use. Also known as k.
  public int n = 5; // number of bits representing the numbers
  public int m = 1024; // length of the sequence, defaults to m = base^n

  // The constraint variables
  public IntVar[] x; // the decimal numbers
  public IntVar[][] binary; // the representation of numbers in x, in the choosen base
  IntVar[] binCode; // the de Bruijn sequence (first number in binary)

  // the model

  /**
   * Running the program java DeBruijn base n java DeBruijn base n m.
   *
   * @param args between 2 and 3 arguments are used.
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    int base = 2;
    int n = 4;
    int m = 9;

    if (args.length == 3) {
      m = Integer.parseInt(args[2]);
    }
    if (args.length >= 2) {
      base = Integer.parseInt(args[0]);
      n = Integer.parseInt(args[1]);
    }

    DeBruijn debruijn = new DeBruijn();
    debruijn.base = base;
    debruijn.n = n;
    debruijn.m = m;

    debruijn.model();

    boolean result = debruijn.searchAllAtOnce();

    if (result) {

      // prints then de Bruijn sequences
      IO.print("de Bruijn sequence:");

      IO.print("decimal values: ");
      for (int i = 0; i < m; i++) {
        IO.print(debruijn.x[i].value() + " ");
      }
      log.info("");

      log.info("\nbinary:");

      for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
          IO.print(debruijn.binary[i][j].value() + " ");
        }
        log.info(" : " + debruijn.x[i].value());
      }

    } else {
      log.info("No solutions.");
    } // end if result
  } // end main

  // integer power method
  static int pow(int x, int y) {
    int z = x;
    for (int i = 1; i < y; i++) {
      z *= x;
    }
    return z;
  } // end pow

  @Override
  public void model() {

    store = new Store();

    int powBaseN = pow(base, n); // base^n, the range of integers
    if (m > 0 && m > powBaseN) {
      throw new RuntimeException("m must be <= base^n (" + m + ")");
    }

    log.info("Using base: " + base + " n: " + n + " m: " + m);

    // decimal representation, ranges from 0..base^n-1
    x = new IntVar[m];
    for (int i = 0; i < m; i++) {
      x[i] = new IntVar(store, "x_" + i, 0, powBaseN - 1);
    }

    // convert between decimal number in x[i] and "base-ary" numbers
    // in binary[i][0..n-1].
    // (This corresponds to the predicate toNum in the MiniZinc model)

    // calculate the weights array
    int[] weights = new int[n];
    int w = 1;
    for (int i = 0; i < n; i++) {
      weights[n - i - 1] = w;
      w *= base;
    }

    // connect binary <-> x
    binary = new IntVar[m][n];
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        binary[i][j] = new IntVar(store, "binary_" + i + "_" + j, 0, base - 1);
      }

      store.impose(new LinearInt(binary[i], weights, "==", x[i]));
    }

    // with the end of element i-1
    for (int i = 1; i < m; i++) {
      for (int j = 1; j < n; j++) {
        store.impose(new XeqY(binary[i - 1][j], binary[i][j - 1]));
      }
    }

    // ... "around the corner": last element is connected to the first
    for (int j = 1; j < n; j++) {
      store.impose(new XeqY(binary[m - 1][j], binary[0][j - 1]));
    }

    vars = new ArrayList<>();
    // This is the de Bruijn sequence, i.e.
    // the first element of of each row in binary[i]
    binCode = new IntVar[m];
    for (int i = 0; i < m; i++) {
      binCode[i] = new IntVar(store, "bin_code_" + i, 0, base - 1);
      vars.add(binCode[i]);
      store.impose(new XeqY(binCode[i], binary[i][0]));
    }

    // All values in x should be different
    store.impose(new Alldifferent(x));

    // Symmetry breaking: the minimum value in x should be the
    // first element.
    store.impose(new Min(x, x[0]));
  } // end model
} // end class
