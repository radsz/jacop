/*
 * MultiObjective.java
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
import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.function.BiConsumer;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XplusYeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Optimises several integer objectives, either lexicographically (the first objective is the most
 * important one, ties are broken by the second one, and so on) or for the Pareto front (every
 * solution whose objective values no other solution improves in one objective without worsening
 * another, one solution for each such vector of objective values).
 *
 * <p>Both run as a sequence of single-objective optimisations, the subproblems, which a {@link
 * Subsolver} solves. {@link DepthFirst} solves them with branch and bound in a store; the FlatZinc
 * front end solves them as FlatZinc models.
 *
 * <ul>
 *   <li>Lexicographic: subproblem k optimises objective k with objectives 0..k-1 fixed at the
 *       values of the best solution so far and objective k required to be strictly better than in
 *       that solution. Every solution found is lexicographically better than the one before.
 *   <li>Pareto: each point of the front is found by optimising the objectives one after the other,
 *       as above, among the solutions not dominated by (and not equal to) a point found before,
 *       with the objectives not yet optimised kept within their values in the best solution so far.
 *       No solution dominates the point found, so every point reported is on the front, and the
 *       front is complete when no solution is left.
 * </ul>
 *
 * <pre>{@code
 * MultiObjective.DepthFirst<IntVar> search =
 *     new MultiObjective.DepthFirst<>(store, select, new IntVar[] {cost, delay}, vars);
 * MultiObjective<int[]> mo = new MultiObjective<>(search, false, false);
 * if (mo.pareto() == MultiObjective.Status.OPTIMAL) {
 *   List<int[]> front = mo.front(); // the objective values, one array per point
 *   List<int[]> values = mo.frontSolutions(); // the values of vars, one array per point
 * }
 * }</pre>
 *
 * @param <S> what the subsolver reports as a solution, for example the values of variables
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class MultiObjective<S> {

  /** How a lexicographic optimisation or the computation of a Pareto front ended. */
  public enum Status {
    /** The lexicographic optimum was proven, or the Pareto front is complete. */
    OPTIMAL,
    /** The search stopped (for example at a time-out) after it found a solution. */
    FEASIBLE,
    /** There is no solution. */
    UNSATISFIABLE,
    /** The search stopped before it found a solution. */
    UNKNOWN
  }

  /**
   * One single-objective subproblem: the model with bounds on the objectives and without the
   * solutions that the excluded points dominate.
   *
   * @param objective the objective to optimise
   * @param maximize the direction of each objective
   * @param lower the least value of each objective, {@link Integer#MIN_VALUE} for no bound
   * @param upper the greatest value of each objective, {@link Integer#MAX_VALUE} for no bound
   * @param excluded points p of the objective space: a solution must be strictly better than p in
   *     at least one objective
   */
  public record Subproblem(
      int objective, boolean[] maximize, int[] lower, int[] upper, List<int[]> excluded) {

    /**
     * Whether a solution with these objective values satisfies the bounds and the exclusions.
     *
     * @param values the objective values
     * @return true when the values are allowed
     */
    public boolean allows(int[] values) {
      for (int i = 0; i < values.length; i++) {
        if (values[i] < lower[i] || values[i] > upper[i]) {
          return false;
        }
      }
      for (int[] p : excluded) {
        if (!improves(values, p, maximize)) {
          return false;
        }
      }
      return true;
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof Subproblem s
          && objective == s.objective
          && Arrays.equals(maximize, s.maximize)
          && Arrays.equals(lower, s.lower)
          && Arrays.equals(upper, s.upper)
          && excluded.size() == s.excluded.size()
          && Arrays.deepEquals(excluded.toArray(), s.excluded.toArray());
    }

    @Override
    public int hashCode() {
      return Objects.hash(
          objective,
          Arrays.hashCode(maximize),
          Arrays.hashCode(lower),
          Arrays.hashCode(upper),
          Arrays.deepHashCode(excluded.toArray()));
    }

    @Override
    public String toString() {
      StringBuilder s = new StringBuilder();
      s.append(maximize[objective] ? "maximize " : "minimize ").append(objective);
      for (int i = 0; i < lower.length; i++) {
        if (lower[i] != Integer.MIN_VALUE || upper[i] != Integer.MAX_VALUE) {
          s.append(", ").append(lower[i]).append("..").append(upper[i]).append(" on ").append(i);
        }
      }
      for (int[] p : excluded) {
        s.append(", better than ").append(Arrays.toString(p));
      }
      return s.toString();
    }
  }

  /**
   * Solves single-objective subproblems.
   *
   * @param <S> what is reported as a solution
   */
  @FunctionalInterface
  public interface Subsolver<S> {

    /**
     * Optimises the objective of a subproblem and reports every solution found, each better than
     * the one before in that objective.
     *
     * @param subproblem the subproblem
     * @param solutions takes the objective values and the solution
     * @return true when the search is complete: the last solution reported is optimal, or there is
     *     no solution; false when it stopped earlier
     */
    boolean solve(Subproblem subproblem, BiConsumer<int[], S> solutions);
  }

  private final Subsolver<S> solver;
  private final boolean[] maximize;
  private BiConsumer<int[], S> listener;

  private int[] best;
  private S bestSolution;
  private final List<int[]> front = new ArrayList<>();
  private final List<S> frontSolutions = new ArrayList<>();
  private int subproblems;

  /**
   * Creates the optimisation of objectives whose subproblems the given subsolver solves.
   *
   * @param solver the subsolver
   * @param maximize for each objective in order of importance, true to maximise and false to
   *     minimise it
   */
  public MultiObjective(Subsolver<S> solver, boolean... maximize) {
    if (maximize.length == 0) {
      throw new IllegalArgumentException("MultiObjective needs at least one objective");
    }
    this.solver = Objects.requireNonNull(solver);
    this.maximize = maximize.clone();
  }

  /**
   * Sets what is told of solutions: lexicographic optimisation tells each solution better than the
   * one before, the Pareto front each of its points when it is proven.
   *
   * @param listener takes the objective values and the solution
   */
  public void setSolutionListener(BiConsumer<int[], S> listener) {
    this.listener = listener;
  }

  /**
   * Optimises the objectives lexicographically, the first one first.
   *
   * @return OPTIMAL when the best solution, {@link #best()}, is the lexicographic optimum
   */
  public Status lexicographic() {
    clear();
    boolean complete = lexicographic(List.of(), false, true);
    return status(complete, best != null);
  }

  /**
   * Computes the Pareto front, its points in no particular order.
   *
   * @return OPTIMAL when {@link #front()} is the whole Pareto front; on FEASIBLE the solution the
   *     search stopped at, {@link #best()}, is not dominated by a point of the front but is not
   *     proven Pareto optimal (it is null when the search stopped right after a point)
   */
  public Status pareto() {
    clear();
    while (true) {
      boolean complete = lexicographic(List.copyOf(front), true, false);
      if (!complete) {
        return status(false, best != null || !front.isEmpty());
      }
      if (best == null) {
        return status(true, !front.isEmpty());
      }
      front.add(best);
      frontSolutions.add(bestSolution);
      if (listener != null) {
        listener.accept(best.clone(), bestSolution);
      }
    }
  }

  private void clear() {
    best = null;
    bestSolution = null;
    front.clear();
    frontSolutions.clear();
    subproblems = 0;
  }

  private static Status status(boolean complete, boolean found) {
    if (complete) {
      return found ? Status.OPTIMAL : Status.UNSATISFIABLE;
    }
    return found ? Status.FEASIBLE : Status.UNKNOWN;
  }

  /**
   * Finds the lexicographic optimum of the solutions that improve on each excluded point.
   *
   * @param excluded the excluded points
   * @param box whether later objectives stay within their values in the best solution so far
   * @param report whether each better solution goes to the listener
   * @return true when the search was complete; the optimum is then in best, or best is null when
   *     there is no solution
   */
  private boolean lexicographic(List<int[]> excluded, boolean box, boolean report) {
    best = null;
    bestSolution = null;
    int n = maximize.length;
    for (int k = 0; k < n; k++) {
      int[] lower = new int[n];
      int[] upper = new int[n];
      Arrays.fill(lower, Integer.MIN_VALUE);
      Arrays.fill(upper, Integer.MAX_VALUE);
      if (best != null) {
        for (int j = 0; j < n; j++) {
          if (j < k) {
            lower[j] = best[j];
            upper[j] = best[j];
          } else if (j > k && box) {
            bound(j, best[j], lower, upper);
          }
        }
        if (maximize[k] ? best[k] == Integer.MAX_VALUE : best[k] == Integer.MIN_VALUE) {
          // nothing is better
          continue;
        }
        bound(k, maximize[k] ? best[k] + 1 : best[k] - 1, lower, upper);
      }
      Subproblem p = new Subproblem(k, maximize.clone(), lower, upper, excluded);
      subproblems++;
      boolean complete =
          solver.solve(
              p,
              (values, solution) -> {
                best = values.clone();
                bestSolution = solution;
                if (report && listener != null) {
                  listener.accept(values.clone(), solution);
                }
              });
      if (!complete) {
        return false;
      }
      if (best == null) {
        return true;
      }
    }
    return true;
  }

  // keeps objective j at least as good as v
  private void bound(int j, int v, int[] lower, int[] upper) {
    if (maximize[j]) {
      lower[j] = v;
    } else {
      upper[j] = v;
    }
  }

  /**
   * Whether objective values are strictly better than a point in at least one objective.
   *
   * @param values the objective values
   * @param point the point
   * @param maximize the direction of each objective
   * @return true when some objective is strictly better
   */
  static boolean improves(int[] values, int[] point, boolean[] maximize) {
    for (int i = 0; i < values.length; i++) {
      if (maximize[i] ? values[i] > point[i] : values[i] < point[i]) {
        return true;
      }
    }
    return false;
  }

  /**
   * The objective values of the best solution: the lexicographic optimum after {@link
   * #lexicographic()}, or the solution the search stopped at after {@link #pareto()}.
   *
   * @return the values, or null when there is no such solution
   */
  public int[] best() {
    return best == null ? null : best.clone();
  }

  /**
   * The best solution, as {@link #best()}.
   *
   * @return the solution, or null
   */
  public S bestSolution() {
    return bestSolution;
  }

  /**
   * The points of the Pareto front found by {@link #pareto()}, in the order found.
   *
   * @return the objective values of each point
   */
  public List<int[]> front() {
    List<int[]> copy = new ArrayList<>(front.size());
    for (int[] p : front) {
      copy.add(p.clone());
    }
    return copy;
  }

  /**
   * The solutions of the points of {@link #front()}, in the same order.
   *
   * @return the solutions
   */
  public List<S> frontSolutions() {
    return new ArrayList<>(frontSolutions);
  }

  /**
   * The number of subproblems solved by the last optimisation.
   *
   * @return the number of subproblems
   */
  public int subproblems() {
    return subproblems;
  }

  /**
   * Solves subproblems by branch and bound with {@link DepthFirstSearch} in a store. Each
   * subproblem imposes its bounds and exclusions one level above the level of the store when it
   * starts and removes them when it ends; a maximised objective is minimised through a negated
   * variable that the first subproblem maximising it imposes at that level. A solution reports the
   * values of the recorded variables (the least value of one that is not fixed). An objective
   * should be fixed when the variables of the choice point selection are; one that is not is read
   * at its best bound, as a single-objective branch and bound reads its cost variable.
   *
   * @param <T> the type of the variables of the choice point selection
   */
  public static final class DepthFirst<T extends Var> implements Subsolver<int[]> {

    private final Store store;
    private final SelectChoicePoint<T> select;
    private final IntVar[] objectives;
    private final IntVar[] recorded;
    private final IntVar[] negated;
    private long deadline;
    private int solutions;
    private long nodes;
    private long failures;

    /**
     * Creates the subsolver.
     *
     * @param store the store of the model
     * @param select the choice point selection of every subproblem
     * @param objectives the objectives, in the order of {@link MultiObjective}
     * @param recorded the variables whose values a solution reports
     */
    public DepthFirst(
        Store store, SelectChoicePoint<T> select, IntVar[] objectives, IntVar[] recorded) {
      this.store = Objects.requireNonNull(store);
      this.select = Objects.requireNonNull(select);
      this.objectives = objectives.clone();
      this.recorded = recorded.clone();
      this.negated = new IntVar[objectives.length];
    }

    /**
     * Stops every subproblem at the given time from now on; without it the search is complete.
     *
     * @param millis the time limit in milliseconds for all subproblems together
     */
    public void setTimeOutMilliseconds(long millis) {
      deadline = System.currentTimeMillis() + millis;
    }

    @Override
    public boolean solve(Subproblem p, BiConsumer<int[], int[]> found) {
      if (p.lower().length != objectives.length) {
        throw new IllegalArgumentException(
            "the subproblem has " + p.lower().length + " objectives, not " + objectives.length);
      }
      long remaining = Long.MAX_VALUE;
      if (deadline != 0) {
        remaining = deadline - System.currentTimeMillis();
        if (remaining <= 0) {
          return false;
        }
      }
      int k = p.objective();
      IntVar cost = objectives[k];
      if (p.maximize()[k]) {
        if (negated[k] == null) {
          negated[k] = new IntVar(store, "-" + cost.id(), -cost.max(), -cost.min());
          store.impose(new XplusYeqC(negated[k], cost, 0));
        }
        cost = negated[k];
      }
      int base = store.level;
      store.setLevel(base + 1);
      try {
        imposeBounds(p);
        DepthFirstSearch<T> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        search.setAssignSolution(false);
        if (remaining != Long.MAX_VALUE) {
          search.setTimeOutMilliseconds(remaining);
        }
        search.setSolutionListener(
            new SimpleSolutionListener<>() {
              @Override
              public boolean executeAfterSolution(Search<T> s, SelectChoicePoint<T> sel) {
                boolean stop = super.executeAfterSolution(s, sel);
                DepthFirst.this.solutions++;
                found.accept(values(p.maximize()), recordedValues());
                return stop;
              }
            });
        search.getSolutionListener().recordSolutions(false);
        search.labeling(store, select, cost);
        nodes += search.getNodes();
        failures += search.getWrongDecisions();
        return !search.timeOutOccured;
      } finally {
        store.removeLevel(base + 1);
        store.setLevel(base);
      }
    }

    private void imposeBounds(Subproblem p) {
      for (int i = 0; i < objectives.length; i++) {
        if (p.lower()[i] != Integer.MIN_VALUE) {
          store.impose(new XgteqC(objectives[i], p.lower()[i]));
        }
        if (p.upper()[i] != Integer.MAX_VALUE) {
          store.impose(new XlteqC(objectives[i], p.upper()[i]));
        }
      }
      for (int[] point : p.excluded()) {
        PrimitiveConstraint[] better = new PrimitiveConstraint[objectives.length];
        for (int i = 0; i < objectives.length; i++) {
          better[i] =
              p.maximize()[i]
                  ? new XgtC(objectives[i], point[i])
                  : new XltC(objectives[i], point[i]);
        }
        store.impose(better.length == 1 ? better[0] : new Or(better));
      }
    }

    private int[] values(boolean[] maximize) {
      int[] v = new int[objectives.length];
      for (int i = 0; i < v.length; i++) {
        v[i] = maximize[i] ? objectives[i].max() : objectives[i].min();
      }
      return v;
    }

    private int[] recordedValues() {
      int[] v = new int[recorded.length];
      for (int i = 0; i < v.length; i++) {
        v[i] = recorded[i].min();
      }
      return v;
    }

    /**
     * The number of solutions found in all subproblems.
     *
     * @return the number of solutions
     */
    public int solutions() {
      return solutions;
    }

    /**
     * The number of search nodes of all subproblems.
     *
     * @return the number of nodes
     */
    public long nodes() {
      return nodes;
    }

    /**
     * The number of wrong decisions of all subproblems.
     *
     * @return the number of wrong decisions
     */
    public long failures() {
      return failures;
    }
  }
}
