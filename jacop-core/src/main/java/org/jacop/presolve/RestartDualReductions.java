/*
 * RestartDualReductions.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Dual reductions on the root of a search in progress (inprocessing; Järvisalo, Heule and Biere,
 * Inprocessing rules, IJCAR 2012): the dual fixing and dual bound strengthening of presolve
 * (Achterberg et al., Presolve reductions in mixed integer programming, INFORMS J. Comput. 2020),
 * computed again on the root domains a search learnt, where constraints satisfied at the root no
 * longer lock their variables. The reductions are reported, not applied, so that the search can
 * assert them in its own way.
 *
 * <p>Like the presolve rule, the reductions keep an optimum (or a solution) but not every solution:
 * they are only for searches for one solution or an optimum, and they must be applied together,
 * since each of them assumes the others of the same call.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class RestartDualReductions {

  /**
   * One reduction: the variable keeps only the values from {@code min} to {@code max}.
   *
   * @param variable the variable.
   * @param min the new minimum.
   * @param max the new maximum.
   */
  public record Reduction(IntVar variable, int min, int max) {}

  private RestartDualReductions() {}

  /**
   * Computes one round of dual reductions at the current level of a store at a fixpoint.
   *
   * @param store the store.
   * @param implied the constraints of the store that are implied by the others (for example a
   *     linear relaxation), which lock nothing.
   * @param unimposed the constraints of the problem kept outside the store, for example as clauses
   *     of a SAT solver, which lock their variables whatever the domains.
   * @param objective the variable minimised, or null for a satisfaction problem.
   * @return the reductions, which hold together.
   */
  public static List<Reduction> compute(
      Store store, Predicate<Constraint> implied, List<Constraint> unimposed, IntVar objective) {
    DualReductions rule = new DualReductions(objective, true, Set.of(), false);
    List<Object[]> found = new ArrayList<>();
    rule.collectInto(found);
    Set<Constraint> outside = Collections.newSetFromMap(new IdentityHashMap<>());
    outside.addAll(unimposed);
    rule.unimposed(outside);
    List<Constraint> all = new ArrayList<>();
    for (Constraint c : Derivation.constraints(store, Derivation.variables(store))) {
      if (!implied.test(c)) {
        all.add(c);
      }
    }
    all.addAll(unimposed);
    rule.apply(store, store.level, all);
    List<Reduction> result = new ArrayList<>(found.size());
    for (Object[] r : found) {
      result.add(new Reduction((IntVar) r[0], (Integer) r[1], (Integer) r[2]));
    }
    return result;
  }
}
