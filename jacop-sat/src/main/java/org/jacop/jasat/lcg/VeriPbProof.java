/*
 * VeriPbProof.java
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

package org.jacop.jasat.lcg;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.UncheckedIOException;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.function.IntFunction;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.cdcl.ProofOutput;

/**
 * Writes a VeriPB 3.0 proof of an LCG search (Gocht, McCreesh and Nordström, "An Auditable
 * Constraint Programming Solver", CP 2022) against the OPB model of {@link OpbEncoder}. Every
 * clause the SAT solver adds or derives, the propagators' explanations included, is a {@code rup}
 * step: the model encodes each integer variable by its order literals {@code [x >= v]} and value
 * literals {@code [x = v]}, so unit propagation over the encoding of a constraint derives what its
 * explanations state. Each solution is logged with {@code soli}, which adds the constraint that the
 * objective improves; the conclusion states what the search proved.
 *
 * <p>Deleted clauses are deleted by their constraint id when this proof derived them; a deleted
 * clause of the model stays. A deletion is written after the next added clause, since the solver
 * frees the temporary reasons of a conflict when it backjumps, before it adds the learnt clause
 * derived from them.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class VeriPbProof implements ProofOutput, AutoCloseable {

  private final Writer out;
  // the name of each solver variable (DIMACS)
  private final IntFunction<String> names;
  // the id of the last constraint in the database
  private long lastId;
  // the ids of the clauses this proof derived and has not deleted, by their sorted literals
  private final Map<Clause, ArrayDeque<Long>> derived = new HashMap<>();
  private final StringBuilder line = new StringBuilder();
  // whether the empty clause is derived
  private boolean refuted;
  // whether the header is written, and what comes after it until then
  private boolean started;
  private final StringBuilder early = new StringBuilder();
  // deletions written after the next added clause
  private long[] deleted = new long[16];
  private int numDeleted;

  /** Statistics: rup steps written. */
  public long steps;

  /** Statistics: clauses deleted. */
  public long deletions;

  /**
   * Creates a proof writer.
   *
   * @param out where the proof goes; closed by {@link #close()}
   * @param names the variable name of each solver variable, by its DIMACS number
   */
  public VeriPbProof(OutputStream out, IntFunction<String> names) {
    this.out = new BufferedWriter(new OutputStreamWriter(out, StandardCharsets.US_ASCII), 1 << 16);
    this.names = names;
  }

  /**
   * Writes the header; the model's constraints take the first ids.
   *
   * @param modelConstraints the number of constraints VeriPB loads from the OPB file
   */
  void start(long modelConstraints) {
    started = true;
    write("pseudo-Boolean proof version 3.0\n");
    write("f " + modelConstraints + " ;\n");
    // the clauses the solver simplified while the model was being added come after the model
    write(early);
    early.setLength(0);
    for (ArrayDeque<Long> ids : derived.values()) {
      ArrayDeque<Long> shifted = new ArrayDeque<>();
      for (long id : ids) {
        shifted.addLast(id + modelConstraints);
      }
      ids.clear();
      ids.addAll(shifted);
    }
    for (int k = 0; k < numDeleted; k++) {
      deleted[k] += modelConstraints;
    }
    lastId += modelConstraints;
  }

  @Override
  public void add(int[] lits, int from, int n) {
    line.setLength(0);
    line.append("rup");
    for (int k = from; k < from + n; k++) {
      line.append(" 1 ").append(literal(CdclSolver.toDimacs(lits[k])));
    }
    line.append(" >= 1 ;\n");
    write(line);
    steps++;
    refuted |= n == 0;
    derived.computeIfAbsent(new Clause(lits, from, n), k -> new ArrayDeque<>()).push(++lastId);
    flushDeletions();
  }

  private void flushDeletions() {
    if (numDeleted == 0) {
      return;
    }
    line.setLength(0);
    line.append("del id");
    for (int k = 0; k < numDeleted; k++) {
      line.append(' ').append(deleted[k]);
    }
    line.append(" ;\n");
    write(line);
    deletions += numDeleted;
    numDeleted = 0;
  }

  @Override
  public void delete(int[] lits, int from, int n) {
    Clause key = new Clause(lits, from, n);
    ArrayDeque<Long> ids = derived.get(key);
    if (ids == null) {
      return; // a clause of the model
    }
    long id = ids.pop();
    if (ids.isEmpty()) {
      derived.remove(key);
    }
    if (numDeleted == deleted.length) {
      deleted = Arrays.copyOf(deleted, 2 * numDeleted);
    }
    deleted[numDeleted++] = id;
  }

  /**
   * Writes a {@code rup} step the solver does not derive as a clause of its own, such as the
   * explanation of an atom inside a conflict clause; it is not deleted.
   *
   * @param step the whole step, {@code rup ... ;} and a line end
   * @return its id
   */
  long lemma(CharSequence step) {
    write(step);
    steps++;
    return ++lastId;
  }

  /**
   * Writes a {@code pol} step, a sum of constraints and literal axioms in postfix order.
   *
   * @param operands the operands and operators, such as {@code "12 13 + ~x4e2 +"}
   * @return the id of the derived constraint
   */
  long pol(CharSequence operands) {
    write("pol " + operands + " ;\n");
    steps++;
    return ++lastId;
  }

  /**
   * Logs a solution, given by the literals true in it; with an objective, VeriPB adds the
   * constraint that the objective is smaller.
   *
   * @param trueLiterals the model's literals (names, {@code ~} for negated) true in the solution
   * @param improve whether to add the objective-improving constraint ({@code soli})
   */
  void solution(Iterable<String> trueLiterals, boolean improve) {
    line.setLength(0);
    line.append(improve ? "soli" : "sol");
    for (String l : trueLiterals) {
      line.append(' ').append(l);
    }
    line.append(" ;\n");
    write(line);
    if (improve) {
      lastId++;
    }
  }

  /**
   * Writes a comment line.
   *
   * @param text the comment, on one line
   */
  void comment(String text) {
    write("% " + text + "\n");
  }

  /**
   * Concludes that the model has no solution, deriving the empty clause when the solver stopped on
   * a clause false at the root without stating it.
   */
  void concludeUnsatisfiable() {
    refute();
    conclude("UNSAT");
  }

  private void refute() {
    if (!refuted) {
      write("rup >= 1 ;\n");
      steps++;
      lastId++;
      refuted = true;
    }
  }

  /** Concludes that the model has a solution, logged before. */
  void concludeSatisfiable() {
    conclude("SAT");
  }

  /**
   * Concludes bounds of the objective, of the OPB objective function.
   *
   * @param lower the lower bound, proved by the contradiction that no solution is better
   * @param upper the upper bound, the value of a logged solution; null for none
   */
  void concludeBounds(String lower, String upper) {
    refute();
    conclude("BOUNDS " + lower + " " + (upper == null ? "INF" : upper));
  }

  /** Concludes nothing, for a search stopped by a limit. */
  void concludeNothing() {
    conclude("NONE");
  }

  private void conclude(String conclusion) {
    write("output NONE ;\nconclusion " + conclusion + " ;\nend pseudo-Boolean proof ;\n");
  }

  private String literal(int dimacs) {
    String name = names.apply(Math.abs(dimacs));
    return dimacs < 0 ? "~" + name : name;
  }

  private void write(CharSequence s) {
    if (!started) {
      early.append(s);
      return;
    }
    try {
      out.append(s);
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

  /** A clause as a sorted set of literals, the key of its ids. */
  private static final class Clause {
    private final int[] lits;
    private final int hash;

    Clause(int[] a, int from, int n) {
      lits = Arrays.copyOfRange(a, from, from + n);
      Arrays.sort(lits);
      hash = Arrays.hashCode(lits);
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof Clause c && Arrays.equals(lits, c.lits);
    }

    @Override
    public int hashCode() {
      return hash;
    }
  }
}
