/*
 * DimacsReader.java
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

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.zip.GZIPInputStream;

/**
 * Reads a DIMACS CNF file (plain or gzip-compressed) into a {@link CdclSolver}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class DimacsReader {

  private final InputStream in;
  private final byte[] buf = new byte[1 << 16];
  private int len;
  private int pos;

  private DimacsReader(InputStream in) {
    this.in = in;
  }

  /**
   * Reads the clauses of a DIMACS file into the solver.
   *
   * @param path file name; a name ending in {@code .gz} is decompressed
   * @param solver the solver that receives the clauses
   * @throws IOException if the file cannot be read or is not valid DIMACS
   */
  public static void read(String path, CdclSolver solver) throws IOException {
    try (InputStream file = new FileInputStream(path);
        InputStream raw = path.endsWith(".gz") ? new GZIPInputStream(file, 1 << 16) : file;
        InputStream in = new BufferedInputStream(raw, 1 << 16)) {
      new DimacsReader(in).readInto(solver);
    }
  }

  /**
   * Reads DIMACS clauses from a stream into the solver.
   *
   * @param in the input, not closed
   * @param solver the solver that receives the clauses
   * @throws IOException if the input cannot be read or is not valid DIMACS
   */
  public static void read(InputStream in, CdclSolver solver) throws IOException {
    new DimacsReader(in).readInto(solver);
  }

  private int next() throws IOException {
    if (pos == len) {
      len = in.read(buf, 0, buf.length);
      pos = 0;
      if (len <= 0) {
        len = 0;
        return -1;
      }
    }
    return buf[pos++];
  }

  private void readInto(CdclSolver solver) throws IOException {
    int[] clause = new int[16];
    int size = 0;
    int c = next();
    while (c != -1) {
      if (c == '%') {
        break; // SATLIB end marker
      }
      if (c == 'c' || c == 'p') {
        if (c == 'p') {
          StringBuilder header = new StringBuilder();
          while (c != -1 && c != '\n') {
            header.append((char) c);
            c = next();
          }
          String[] f = header.toString().trim().split("\\s+");
          if (f.length >= 3) {
            solver.ensureVars(Integer.parseInt(f[2]));
          }
        }
        while (c != -1 && c != '\n') {
          c = next();
        }
        c = next();
        continue;
      }
      if (c == ' ' || c == '\t' || c == '\n' || c == '\r') {
        c = next();
        continue;
      }
      boolean neg = false;
      if (c == '-') {
        neg = true;
        c = next();
      }
      if (c < '0' || c > '9') {
        throw new IOException("unexpected character '" + (char) c + "' in DIMACS input");
      }
      int x = 0;
      while (c >= '0' && c <= '9') {
        x = 10 * x + (c - '0');
        c = next();
      }
      if (x == 0) {
        solver.addClause(clause, size);
        size = 0;
      } else {
        if (size == clause.length) {
          clause = Arrays.copyOf(clause, 2 * size);
        }
        clause[size++] = neg ? -x : x;
      }
    }
    if (size > 0) {
      solver.addClause(clause, size);
    }
  }
}
