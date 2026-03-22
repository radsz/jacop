/*
 * CnfParser.java
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

package org.jacop.jasat.utils;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.io.IOException;
import java.io.InputStream;
import java.util.Iterator;
import java.util.NoSuchElementException;
import org.jacop.jasat.utils.structures.IntVec;

/**
 * CNF file format (low-level) parser.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class CnfParser implements Iterable<IntVec> {

  // stream from which to read values
  private final InputStream stream;
  // memory pool
  private final MemoryPool pool;
  // data of the problem
  public int numClauses;
  public int numVars;
  // current char
  private int c;

  // next clause
  private IntVec nextClause;

  /**
   * Creates an instance of the parser for some input stream.
   *
   * @param pool the memory pool to use
   * @param stream the stream from which to read clauses
   * @throws ParseException excpetion when parsing fails
   */
  public CnfParser(MemoryPool pool, InputStream stream) throws ParseException {
    this.pool = pool;
    this.stream = stream;

    // begin parsing the problem
    try {
      c = stream.read();
      skipComments();
      readProblemDef();

      // prepare the first clause
      parseNextClause();
    } catch (IOException _) {
      System.err.println("error while reading: unable to parse problem");
      throw new ParseException("unable to parse problem");
    }
  }

  /**
   * Reads an int from the stream.
   *
   * @return the parsed int
   * @throws IOException if an I/O error occurs
   */
  private int parseInt() throws IOException {
    int answer = 0;
    if (c == -1) {
      throw new IOException();
    }
    if (ASSERTS_ENABLED && c != '-' && (c < '0' || c > '9')) {
      throw new IllegalStateException("Assertion failed");
    }

    boolean negative = c == '-';
    if (negative) {
      c = stream.read();
    }

    // read digits
    while (c >= '0' && c <= '9') {
      int i = Character.digit(c, 10);
      answer = 10 * answer + i;
      c = stream.read();
    }

    return negative ? -answer : answer;
  }

  /**
   * Skips comment lines from the current position.
   *
   * @throws IOException if an I/O error occurs
   */
  private void skipComments() throws IOException {
    if (c != 'c') {
      return;
    }

    // skip lines which begin with 'c'
    while (c == 'c') {
      skipLine();
    }
  }

  /**
   * Skip the rest of the line (\n included).
   *
   * @throws IOException if an I/O error occurs
   */
  private void skipLine() throws IOException {
    // read until \n
    while (c != '\n') {
      c = stream.read();
    }

    // skip \n
    c = stream.read();
  }

  /**
   * Skips white spaces and carriage returns.
   *
   * @throws IOException if an I/O error occurs
   */
  private void skipSpaces() throws IOException {
    while (c == ' ' || c == '\t' || c == '\n') {
      c = stream.read();
    }
  }

  /**
   * Reads number of clauses and number of vars.
   *
   * @throws IOException if an I/O error occurs
   */
  private void readProblemDef() throws IOException {

    // read "p cnf"
    if (ASSERTS_ENABLED && c != 'p') {
      throw new IllegalStateException("Assertion failed");
    }
    c = stream.read();
    skipSpaces();
    if (ASSERTS_ENABLED && c != 'c') {
      throw new IllegalStateException("Assertion failed");
    }
    c = stream.read();
    if (ASSERTS_ENABLED && c != 'n') {
      throw new IllegalStateException("Assertion failed");
    }
    c = stream.read();
    if (ASSERTS_ENABLED && c != 'f') {
      throw new IllegalStateException("Assertion failed");
    }
    c = stream.read();

    // spaces -> int -> spaces -> int
    skipSpaces();
    numVars = parseInt();
    skipSpaces();
    numClauses = parseInt();
  }

  /** Parses the next clause from the stream. */
  private void parseNextClause() {
    IntVec answer = new IntVec(pool);

    try {
      // maybe we just read a clause, so we must discard the 0
      if (c == '0') {
        c = stream.read();
      }
    } catch (IOException _) {
      return;
    }

    while (true) {
      try {
        skipSpaces();
        int curInt = parseInt();
        if (curInt == 0) {
          break;
        } else {
          answer.add(curInt);
        }
      } catch (IOException _) {
        break;
      }
    }

    // set nextClause
    if (answer.isEmpty()) {
      nextClause = null;
    } else {
      nextClause = answer;
    }
  }

  /** {@inheritDoc} */
  @Override
  public Iterator<IntVec> iterator() {
    return new Iterator<>() {
      @Override
      public boolean hasNext() {
        return nextClause != null;
      }

      @Override
      public IntVec next() {
        if (nextClause == null) {
          throw new NoSuchElementException();
        }
        IntVec answer = nextClause;
        parseNextClause();
        return answer;
      }
    };
  }

  /**
   * Exception occurring during parse.
   *
   * @author simon
   */
  @SuppressWarnings("serial")
  public static final class ParseException extends Exception {
    /**
     * Constructs a new parse exception with the specified message.
     *
     * @param msg the error message
     */
    public ParseException(String msg) {
      super(msg);
    }
  }
}
