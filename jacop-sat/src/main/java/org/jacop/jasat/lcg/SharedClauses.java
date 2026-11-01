/*
 * SharedClauses.java
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

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Clauses that LCG solvers of the same model, each in its own thread, share: short learnt clauses
 * of low LBD and the bounds of their variables at the root. A clause is a set of atoms {@code [x >=
 * v]} and {@code [x = v]}, possibly negated, over variables known by name, so that each solver
 * reads it in terms of its own literals.
 *
 * <p>A solver's clauses follow from the model and its bound on the objective; that bound is the
 * cost of a solution the solver reported before, so each clause only removes solutions no better
 * than one known to all. A solver that adds constraints the model does not imply (such as symmetry
 * breaking) names them when it registers: it then reads the clauses of solvers that added none or
 * the same ones, and its own clauses go only to solvers that added the same ones.
 *
 * <p>A clause is stored as {@code [source, lbd, id1, kind1, value1, id2, ...]}, with kind {@link
 * #GE} or {@link #EQ}, plus {@link #NEGATED} for a negated atom.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class SharedClauses {

  /** The kind of an atom {@code [x >= v]}. */
  static final int GE = 0;

  /** The kind of an atom {@code [x = v]}. */
  static final int EQ = 1;

  /** Added to the kind of a negated atom. */
  static final int NEGATED = 2;

  // the most clauses kept; later ones are dropped
  private static final int CAPACITY = 1 << 20;

  private final Map<String, Integer> ids = new HashMap<>();
  // the models solvers solve: 0 is the shared model, other numbers that model with constraints
  // added
  private final Map<String, Integer> models = new HashMap<>(Map.of("", 0));
  private int[] modelOf = new int[4];
  private int[][] clauses = new int[1024][];
  private int size;
  private int sources;

  /**
   * Returns the number by which solvers know a variable of the model.
   *
   * @param name the variable's name in the model
   * @return its number
   */
  public synchronized int id(String name) {
    return ids.computeIfAbsent(name, k -> ids.size());
  }

  /**
   * Registers a solver that shares clauses.
   *
   * @param added the constraints the solver adds to the shared model, in a text that is the same
   *     for the same constraints in every solver; empty when it adds none
   * @return the number of the solver, which marks its clauses
   */
  synchronized int newSource(String added) {
    if (sources == modelOf.length) {
      modelOf = Arrays.copyOf(modelOf, 2 * sources);
    }
    modelOf[sources] = models.computeIfAbsent(added, k -> models.size());
    return sources++;
  }

  /**
   * Adds clauses of a solver.
   *
   * @param batch the clauses, in the stored form
   */
  synchronized void publish(List<int[]> batch) {
    for (int[] c : batch) {
      if (size == CAPACITY) {
        return;
      }
      if (size == clauses.length) {
        clauses = Arrays.copyOf(clauses, 2 * size);
      }
      clauses[size++] = c;
    }
  }

  /**
   * Collects the clauses added since a position by other solvers whose clauses hold for the reading
   * solver: those of solvers that added no constraints or the same ones.
   *
   * @param from the position read up to before
   * @param source the reading solver, whose own clauses are skipped
   * @param out where the clauses go
   * @return the position read up to now
   */
  synchronized int read(int from, int source, List<int[]> out) {
    int model = modelOf[source];
    for (int k = from; k < size; k++) {
      int c = clauses[k][0];
      if (c != source && (modelOf[c] == 0 || modelOf[c] == model)) {
        out.add(clauses[k]);
      }
    }
    return size;
  }

  /**
   * The number of clauses shared so far.
   *
   * @return the number of clauses
   */
  public synchronized int size() {
    return size;
  }
}
