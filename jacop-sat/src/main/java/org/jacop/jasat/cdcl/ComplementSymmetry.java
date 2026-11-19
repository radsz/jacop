/*
 * ComplementSymmetry.java
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
package org.jacop.jasat.cdcl;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The complement symmetry of a CNF formula: when the complement of every clause (each literal
 * negated) is a clause of the formula too, the complement of every model is a model, so one
 * variable can be fixed to either value without losing satisfiability. Not-all-equal constraints
 * written as a clause and its complement (NAE-SAT, 2-colourings of hypergraphs, the Boolean
 * Pythagorean triples problem) have this symmetry; Heule, Kullmann and Marek fix one variable of
 * the Pythagorean triples formula this way ("Solving and Verifying the Boolean Pythagorean Triples
 * Problem via Cube-and-Conquer", SAT 2016, LNCS 9710). On the XCSP 2023 PythagoreanTriples-7000 and
 * 7500 formulas the fixed variable turns time-outs of 600 s into 15 to 25 s.
 *
 * <p>The unit is not implied by the formula, so a DRAT proof cannot take it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ComplementSymmetry {

  private ComplementSymmetry() {}

  /**
   * Returns the variable to fix to true when the formula has the complement symmetry: the variable
   * with the most occurrences, as Heule et al. fix the most constrained number.
   *
   * @param clauses the clauses, DIMACS literals, none empty
   * @param numVars the number of variables
   * @return the variable, or 0 when some clause has no complement in the formula
   */
  public static int fixedVariable(List<int[]> clauses, int numVars) {
    if (clauses.isEmpty()) {
      return 0;
    }
    Set<Key> keys = new HashSet<>(2 * clauses.size());
    for (int[] c : clauses) {
      keys.add(new Key(c, false));
    }
    int[] occurrences = new int[numVars + 1];
    for (int[] c : clauses) {
      if (c.length == 0 || !keys.contains(new Key(c, true))) {
        return 0;
      }
      for (int l : c) {
        occurrences[Math.abs(l)]++;
      }
    }
    int best = 0;
    for (int v = 1; v <= numVars; v++) {
      if (occurrences[v] > occurrences[best]) {
        best = v;
      }
    }
    return best;
  }

  // a clause as the sorted set of its literals, complemented on request
  private static final class Key {

    private final int[] lits;

    private final int hash;

    Key(int[] clause, boolean complement) {
      int[] l = new int[clause.length];
      for (int i = 0; i < clause.length; i++) {
        l[i] = complement ? -clause[i] : clause[i];
      }
      Arrays.sort(l);
      int size = 0;
      for (int i = 0; i < l.length; i++) {
        if (size == 0 || l[size - 1] != l[i]) {
          l[size++] = l[i];
        }
      }
      lits = size == l.length ? l : Arrays.copyOf(l, size);
      hash = Arrays.hashCode(lits);
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof Key k && Arrays.equals(lits, k.lits);
    }

    @Override
    public int hashCode() {
      return hash;
    }
  }
}
