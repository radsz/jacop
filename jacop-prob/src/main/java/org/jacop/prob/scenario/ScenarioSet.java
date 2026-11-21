/*
 * ScenarioSet.java
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

package org.jacop.prob.scenario;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.prob.dist.Dist;
import org.jacop.prob.num.ProbArith;

/**
 * A finite set of scenarios with exact probabilities: scenario s gives values {@code value(s, k)}
 * to k = 0 .. dimension - 1 parameters and has probability {@code weight(s) / den}. The weights are
 * positive and sum to the denominator. Equal scenarios are merged. It is immutable.
 *
 * <p>It is the input of {@link org.jacop.prob.constraints.ScenarioChance}, which keeps a solution
 * when the scenarios it satisfies have enough probability.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ScenarioSet {

  /** The largest number of scenarios {@link #independent} builds. */
  public static final int MAX_SCENARIOS = 1 << 20;

  private final int[][] values;
  private final long[] weights;
  private final long den;

  /**
   * It constructs a scenario set. Equal scenarios are merged and scenarios of weight 0 dropped.
   *
   * @param values the parameter values of each scenario, all of the same length
   * @param weights the probability numerator of each scenario, at least 0
   * @param den the denominator; the weights must sum to it
   */
  public ScenarioSet(int[][] values, long[] weights, long den) {
    if (values == null || weights == null || values.length != weights.length) {
      throw new IllegalArgumentException("ScenarioSet needs values and weights of the same length");
    }
    ProbArith.checkProbabilities(weights, den, true);
    int dim = values.length == 0 ? 0 : values[0].length;
    Map<List<Integer>, Long> merged = new LinkedHashMap<>();
    for (int s = 0; s < values.length; s++) {
      if (values[s].length != dim) {
        throw new IllegalArgumentException("Scenario " + s + " has a different dimension");
      }
      if (weights[s] > 0) {
        merged.merge(Arrays.stream(values[s]).boxed().toList(), weights[s], Math::addExact);
      }
    }
    this.values = new int[merged.size()][];
    this.weights = new long[merged.size()];
    int s = 0;
    for (Map.Entry<List<Integer>, Long> e : merged.entrySet()) {
      this.values[s] = e.getKey().stream().mapToInt(Integer::intValue).toArray();
      this.weights[s] = e.getValue();
      s++;
    }
    this.den = den;
  }

  /**
   * Returns the scenarios of independent parameters: the product of their distributions, over the
   * product of their denominators.
   *
   * @param dists the distribution of each parameter
   * @return one scenario for each combination of their values
   * @throws IllegalArgumentException when there would be more than {@link #MAX_SCENARIOS}
   */
  public static ScenarioSet independent(Dist... dists) {
    long count = 1;
    long den = 1;
    for (Dist d : dists) {
      count *= d.size();
      if (count > MAX_SCENARIOS) {
        throw new IllegalArgumentException("More than " + MAX_SCENARIOS + " scenarios");
      }
      den = Math.multiplyExact(den, d.den());
    }
    int[][] values = new int[(int) count][dists.length];
    long[] weights = new long[(int) count];
    int[] index = new int[dists.length];
    for (int s = 0; s < count; s++) {
      long w = 1;
      for (int k = 0; k < dists.length; k++) {
        values[s][k] = dists[k].value(index[k]);
        w = Math.multiplyExact(w, dists[k].weight(index[k]));
      }
      weights[s] = w;
      for (int k = dists.length - 1; k >= 0; k--) {
        if (++index[k] < dists[k].size()) {
          break;
        }
        index[k] = 0;
      }
    }
    return new ScenarioSet(values, weights, den);
  }

  /**
   * Returns the number of scenarios.
   *
   * @return the number of scenarios
   */
  public int size() {
    return values.length;
  }

  /**
   * Returns the number of parameters of each scenario.
   *
   * @return the dimension
   */
  public int dimension() {
    return values.length == 0 ? 0 : values[0].length;
  }

  /**
   * Returns a parameter's value in a scenario.
   *
   * @param s the scenario, below {@link #size()}
   * @param k the parameter, below {@link #dimension()}
   * @return its value
   */
  public int value(int s, int k) {
    return values[s][k];
  }

  /**
   * Returns a copy of a scenario's parameter values.
   *
   * @param s the scenario, below {@link #size()}
   * @return its values
   */
  public int[] values(int s) {
    return values[s].clone();
  }

  /**
   * Returns a scenario's probability numerator.
   *
   * @param s the scenario, below {@link #size()}
   * @return its weight
   */
  public long weight(int s) {
    return weights[s];
  }

  /**
   * Returns a copy of the probability numerators of all scenarios.
   *
   * @return the weights
   */
  public long[] weights() {
    return weights.clone();
  }

  /**
   * Returns the denominator.
   *
   * @return the denominator
   */
  public long den() {
    return den;
  }

  /**
   * Returns the distribution of one parameter: its marginal over the scenarios.
   *
   * @param k the parameter, below {@link #dimension()}
   * @return its distribution, over {@link #den()}
   */
  public Dist marginal(int k) {
    int[] v = new int[values.length];
    for (int s = 0; s < values.length; s++) {
      v[s] = values[s][k];
    }
    return new Dist(v, weights, den);
  }

  @Override
  public String toString() {
    StringBuilder b = new StringBuilder("ScenarioSet(");
    b.append(values.length).append(" scenarios over ").append(den);
    return b.append(')').toString();
  }
}
