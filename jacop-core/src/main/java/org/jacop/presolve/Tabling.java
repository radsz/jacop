/*
 * Tabling.java
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

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.Store;

/**
 * Automatic tabulation (Akgün et al., CP 2018; Dekker et al., Constraints 2017), a presolve rule: a
 * small group of constraints over a few variables is replaced by one table holding the solutions of
 * the group. The table propagates to domain consistency over the whole group, where the constraints
 * of the group propagate one at a time.
 *
 * <p>Two heuristics form the groups, on constraints whose variables are all integer variables and
 * that have at most {@link Limits#variables()} unfixed variables:
 *
 * <ol>
 *   <li>a constraint whose unfixed variables are a subset of those of another constraint joins it
 *       (Savile Row's identical scopes);
 *   <li>the constraints of a variable that occurs in at most {@link Limits#degree()} constraints
 *       join, so an intermediate variable of a decomposition, for example {@code t} in {@code t = x
 *       - y, z = abs(t)}, brings its definition and its use together.
 * </ol>
 *
 * A group grows only while it has at most {@link Limits#variables()} unfixed variables. Each group
 * of two or more constraints is solved on a scratch store, with a search over its unfixed variables
 * limited to {@link Limits#nodes()} nodes and {@link Limits#tuples()} solutions. A group within the
 * limits is replaced by the table of its solutions over all its unfixed variables if its own
 * propagation is weaker than the table: that search failed somewhere, or after the removal of one
 * value the group leaves a value without a solution. Otherwise a table would cost more without
 * pruning more.
 *
 * <p>The table is imposed and the constraints of the group are removed from the child; the table is
 * equivalent to the group, so every solution, and the number of solutions, is kept. A group whose
 * table holds every tuple of its domains is entailed and is only removed; one without a solution
 * makes the problem infeasible. A rule instance remembers the groups it tried, so the later rounds
 * of a derivation only try groups with a new constraint; use one instance per derivation.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class Tabling implements Rule {

  /**
   * Limits of the tabulation.
   *
   * @param variables most unfixed variables of a group, the arity of its table.
   * @param degree most constraints of a variable whose constraints are joined.
   * @param tuples most tuples of a table.
   * @param nodes most search nodes to tabulate one group.
   * @param budget most search nodes over all groups.
   * @param onlyStronger whether a group is tabulated only if its own propagation is weaker than its
   *     table.
   */
  record Limits(
      int variables, int degree, int tuples, long nodes, long budget, boolean onlyStronger) {

    /** The limits of Savile Row: 10 variables and 10,000 tuples. */
    static final Limits DEFAULT = new Limits(10, 3, 10_000, 100_000, 2_000_000, true);
  }

  /**
   * What the rule did.
   *
   * @param tables tables imposed.
   * @param replaced constraints removed because a table replaced them or their group was entailed.
   * @param tuples tuples of the tables.
   * @param nodes search nodes spent tabulating.
   */
  public record Statistics(int tables, int replaced, int tuples, long nodes) {}

  private final Limits limits;
  private final Set<Constraint> tried = Collections.newSetFromMap(new IdentityHashMap<>());
  private int tables;
  private int replaced;
  private int tuples;
  private long nodes;

  /** Creates the rule with the default limits: 10 variables and 10,000 tuples. */
  public Tabling() {
    this(Limits.DEFAULT);
  }

  Tabling(Limits limits) {
    this.limits = limits;
  }

  @Override
  public Timing timing() {
    return Timing.EXHAUSTIVE;
  }

  @Override
  public void apply(Context context) {
    if (nodes >= limits.budget()) {
      return;
    }
    TableGroups pass = new TableGroups(context.constraints(), limits, tried, nodes);
    List<TableGroups.Group> groups = pass.groups();
    nodes = pass.nodes();
    if (pass.infeasible()) {
      throw Store.failException;
    }
    for (TableGroups.Group g : groups) {
      if (g.tuples() != null) {
        HybridTable table = new HybridTable(g.scope(), g.tuples());
        tried.add(table);
        context.impose(table);
        tables++;
        tuples += g.tuples().length;
      }
      for (Constraint c : g.constraints()) {
        context.remove(c);
      }
      replaced += g.constraints().size();
    }
  }

  /**
   * Returns what the rule did so far.
   *
   * @return the statistics.
   */
  public Statistics statistics() {
    return new Statistics(tables, replaced, tuples, nodes);
  }
}
