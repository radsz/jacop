/*
 * MaxSolutionDensity.java
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

package org.jacop.search;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.SolutionDensities;
import org.jacop.core.IntVar;

/**
 * Counting-based search, the maxSD heuristic of Pesant, Quimper and Zanarini ("Counting-Based
 * Search: Branching Heuristics for Constraint Satisfaction Problems", JAIR 43, 2012): over the
 * constraints of the search variables that can count their solutions ({@link SolutionDensities}),
 * the next choice is the variable and value with the largest solution density in any of them, x = v
 * first and x &ne; v on backtracking. Ties go to the smaller domain, then to the variable given
 * first.
 *
 * <p>It returns null once no such constraint has an unfixed search variable, so that a {@link
 * SequenceSelect} can continue with another heuristic.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class MaxSolutionDensity implements SelectChoicePoint<IntVar> {

  private final IntVar[] vars;
  private final Map<IntVar, Integer> position = new IdentityHashMap<>();
  private final Constraint[] constraints;
  private final SolutionDensities densities = new SolutionDensities();

  private IntVar selected;
  private int selectedValue;
  private double best;
  private int bestPosition;

  private long calls;
  private long choices;

  /**
   * It selects among the variables of the constraints of the given variables.
   *
   * @param vars the search variables.
   */
  public MaxSolutionDensity(IntVar[] vars) {
    this(vars, true);
  }

  /**
   * It selects among the variables of the constraints of the given variables.
   *
   * @param vars the search variables.
   * @param linear false to leave out the linear constraints and count only alldifferent and
   *     layered-graph (regular) constraints, the ones Pesant et al. measured.
   */
  public MaxSolutionDensity(IntVar[] vars, boolean linear) {
    this.vars = vars.clone();
    Set<Constraint> found = new LinkedHashSet<>();
    for (int i = 0; i < vars.length; i++) {
      position.putIfAbsent(vars[i], i);
      for (Constraint c : vars[i].constraintsWithWatches()) {
        if (SolutionDensities.supports(c) && (linear || !SolutionDensities.isLinear(c))) {
          found.add(c);
        }
      }
    }
    constraints = found.toArray(new Constraint[0]);
  }

  /**
   * It gives the constraints with densities.
   *
   * @return the constraints, in the order met.
   */
  public List<Constraint> countingConstraints() {
    return new ArrayList<>(List.of(constraints));
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    calls++;
    selected = null;
    best = -1.0d;
    bestPosition = Integer.MAX_VALUE;
    for (Constraint c : constraints) {
      densities.densities(c, this::offer);
    }
    if (selected != null) {
      choices++;
    }
    return selected;
  }

  private void offer(IntVar x, int value, double density) {
    Integer p = position.get(x);
    if (p == null) {
      return;
    }
    if (density > best
        || (density == best
            && (x.getSize() < selected.getSize()
                || (x.getSize() == selected.getSize() && p < bestPosition)))) {
      best = density;
      selected = x;
      selectedValue = value;
      bestPosition = p;
    }
  }

  @Override
  public int getChoiceValue() {
    return selectedValue;
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return null;
  }

  @Override
  public Map<IntVar, Integer> getVariablesMapping() {
    Map<IntVar, Integer> mapping = new IdentityHashMap<>();
    for (int i = 0; i < vars.length; i++) {
      mapping.putIfAbsent(vars[i], i);
    }
    return mapping;
  }

  @Override
  public int getIndex() {
    return 0;
  }

  /**
   * It gives the number of selections that found a choice.
   *
   * @return the choices made.
   */
  public long choices() {
    return choices;
  }

  /**
   * It gives the number of selections.
   *
   * @return the calls of {@link #getChoiceVariable}.
   */
  public long calls() {
    return calls;
  }

  @Override
  public String toString() {
    return "MaxSolutionDensity(" + constraints.length + " counting constraints)";
  }
}
