/*
 * DratWriter.java
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

package org.jacop.jasat.cdcl;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.UncheckedIOException;

/**
 * Writes a DRAT proof in text format: one line per added clause ({@code lits 0}) and per deleted
 * clause ({@code d lits 0}), with DIMACS literals.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class DratWriter implements ProofOutput, AutoCloseable {

  private final OutputStream out;
  private final byte[] digits = new byte[12];

  /**
   * Creates a proof writer.
   *
   * @param out where the proof goes; closed by {@link #close()}
   */
  public DratWriter(OutputStream out) {
    this.out = new BufferedOutputStream(out, 1 << 16);
  }

  @Override
  public void add(int[] lits, int from, int n) {
    line(lits, from, n);
  }

  @Override
  public void delete(int[] lits, int from, int n) {
    write('d');
    write(' ');
    line(lits, from, n);
  }

  private void line(int[] lits, int from, int n) {
    for (int i = from; i < from + n; i++) {
      number(CdclSolver.toDimacs(lits[i]));
      write(' ');
    }
    write('0');
    write('\n');
  }

  private void number(int x) {
    if (x < 0) {
      write('-');
      x = -x;
    }
    int k = 0;
    do {
      digits[k++] = (byte) ('0' + x % 10);
      x /= 10;
    } while (x > 0);
    while (k > 0) {
      write(digits[--k]);
    }
  }

  private void write(int b) {
    try {
      out.write(b);
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  /**
   * Flushes and closes the proof output.
   *
   * @throws IOException if the output fails
   */
  @Override
  public void close() throws IOException {
    out.close();
  }
}
