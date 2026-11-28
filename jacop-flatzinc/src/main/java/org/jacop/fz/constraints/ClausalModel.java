/*
 * ClausalModel.java
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
package org.jacop.fz.constraints;

import java.io.IOException;
import java.io.Writer;
import java.util.List;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;

/**
 * The CNF of a model compiled by {@link ClausalCompiler}: the clauses, and for each variable of the
 * model the literal of each of its values, which decode a model of the clauses into an assignment
 * of the variables.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ClausalModel {

  private final int numVars;
  // the clauses, each followed by a 0
  private final int[] clauses;
  private final List<IntVar> vars;
  private final List<int[]> values;
  private final List<int[]> literals;

  ClausalModel(
      int numVars, int[] clauses, List<IntVar> vars, List<int[]> values, List<int[]> literals) {
    this.numVars = numVars;
    this.clauses = clauses;
    this.vars = vars;
    this.values = values;
    this.literals = literals;
  }

  /**
   * Returns the number of variables of the CNF.
   *
   * @return the number of variables
   */
  public int numVars() {
    return numVars;
  }

  /**
   * Returns a solver with the clauses added, and with the values each variable lost since the
   * compilation excluded: root propagation, and the reductions that keep some solution (symmetry,
   * dominance, components), prune the store's domains, and a solution of the clauses must be one of
   * the store. The values of a variable whose constraints a reformulation dropped are not excluded:
   * the store keeps a solution of the reformulated model, in which such a variable is free, and a
   * value it gives such a variable (a component fixed to its first solution) need not extend to a
   * solution of the clauses.
   *
   * @param dropped the variables the reformulations of the front end left without constraints
   * @return the solver
   */
  public CdclSolver solver(Set<? extends Var> dropped) {
    CdclSolver solver = new CdclSolver();
    solver.ensureVars(numVars);
    for (int i = 0; i < vars.size(); i++) {
      IntVar x = vars.get(i);
      if (dropped.contains(x)) {
        continue;
      }
      int[] v = values.get(i);
      int[] lits = literals.get(i);
      for (int j = 0; j < v.length; j++) {
        if (!x.domain.contains(v[j]) && lits[j] != -1) {
          if (lits[j] == 1) {
            solver.addClause(new int[0], 0);
          } else {
            solver.addClause(new int[] {-lits[j]}, 1);
          }
        }
      }
    }
    int start = 0;
    for (int i = 0; i < clauses.length; i++) {
      if (clauses[i] == 0) {
        int[] c = java.util.Arrays.copyOfRange(clauses, start, i);
        solver.addClause(c, c.length);
        start = i + 1;
      }
    }
    return solver;
  }

  /**
   * Writes the clauses in DIMACS format.
   *
   * @param w the writer
   * @throws IOException when writing fails
   */
  public void writeDimacs(Writer w) throws IOException {
    int count = 0;
    for (int x : clauses) {
      if (x == 0) {
        count++;
      }
    }
    w.write("p cnf " + numVars + " " + count + "\n");
    StringBuilder line = new StringBuilder();
    for (int x : clauses) {
      line.append(x);
      if (x == 0) {
        line.append('\n');
        w.write(line.toString());
        line.setLength(0);
      } else {
        line.append(' ');
      }
    }
  }

  /**
   * Fixes the variables of the model to the values the solver's model gives them, at a new level of
   * the store.
   *
   * <p>The variables a reformulation dropped keep the values of the store, which {@link
   * #solver(Set)} does not impose on the clauses.
   *
   * @param store the store
   * @param solver the solver, after it found a model
   * @param dropped the variables the reformulations of the front end left without constraints
   * @return false when a variable has no value or a value outside its domain
   */
  public boolean fix(Store store, CdclSolver solver, Set<? extends Var> dropped) {
    store.setLevel(store.level + 1);
    for (int i = 0; i < vars.size(); i++) {
      IntVar x = vars.get(i);
      if (dropped.contains(x)) {
        continue;
      }
      int[] lits = literals.get(i);
      int value = 0;
      int found = 0;
      for (int j = 0; j < lits.length; j++) {
        if (holds(solver, lits[j])) {
          value = values.get(i)[j];
          found++;
        }
      }
      if (found != 1 || !x.domain.contains(value)) {
        return false;
      }
      if (!x.singleton()) {
        x.domain.in(store.level, x, value, value);
      }
    }
    return true;
  }

  private static boolean holds(CdclSolver solver, int lit) {
    if (lit == 1) {
      return true;
    }
    if (lit == -1) {
      return false;
    }
    boolean v = solver.modelValue(Math.abs(lit));
    return lit > 0 == v;
  }
}
