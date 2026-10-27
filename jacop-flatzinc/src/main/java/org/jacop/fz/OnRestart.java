/*
 * OnRestart.java
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

package org.jacop.fz;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.restart.RestartHook;

/**
 * MiniZinc's {@code on_restart} built-ins ({@code status()}, {@code sol}, {@code last_val}, {@code
 * uniform_on_restart} and {@code complete()}). Each built-in has an output variable that the model
 * treats as a constant of the run: at the root of every run this hook fixes it to the status of the
 * last run, to the value of the input variable in the last solution or the last value it was
 * assigned, or to a new random value. As in Chuffed, the status is START until the first solution
 * is found, so the neighbourhoods of a model, which use the last solution, apply only once there is
 * one. As in Gecode, before the first solution a {@code sol} output takes the smallest value of its
 * input, and before its input is first assigned a {@code last_val} output takes the smallest value
 * the input had when the search started.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class OnRestart implements RestartHook {

  final List<IntVar> status = new ArrayList<>();

  final List<IntVar> solIn = new ArrayList<>();
  final List<IntVar> solOut = new ArrayList<>();
  int[] solValues;

  final List<FloatVar> solFloatIn = new ArrayList<>();
  final List<FloatVar> solFloatOut = new ArrayList<>();
  double[] solFloatValues;

  final List<IntVar> lastValIn = new ArrayList<>();
  final List<IntVar> lastValOut = new ArrayList<>();
  int[] lastValues;

  final List<FloatVar> lastValFloatIn = new ArrayList<>();
  final List<FloatVar> lastValFloatOut = new ArrayList<>();
  double[] lastFloatValues;

  final List<int[]> uniformRange = new ArrayList<>();
  final List<IntVar> uniformOut = new ArrayList<>();

  final List<double[]> uniformFloatRange = new ArrayList<>();
  final List<FloatVar> uniformFloatOut = new ArrayList<>();

  final List<IntVar> completeMarkers = new ArrayList<>();
  boolean completeMarked;
  boolean imposed;

  /**
   * Adds {@code status()}.
   *
   * @param s the variable fixed to the status of the last run.
   */
  public void addStatus(IntVar s) {
    status.add(s);
  }

  /**
   * Adds {@code sol(x)} for an integer or Boolean variable.
   *
   * @param x the variable of the model.
   * @param out the variable fixed to the value of x in the last solution.
   */
  public void addSol(IntVar x, IntVar out) {
    solIn.add(x);
    solOut.add(out);
  }

  /**
   * Adds {@code sol(x)} for a float variable.
   *
   * @param x the variable of the model.
   * @param out the variable fixed to the value of x in the last solution.
   */
  public void addSol(FloatVar x, FloatVar out) {
    solFloatIn.add(x);
    solFloatOut.add(out);
  }

  /**
   * Adds {@code last_val(x)} for an integer or Boolean variable.
   *
   * @param x the variable of the model.
   * @param out the variable fixed to the last value x was assigned during the search.
   */
  public void addLastVal(IntVar x, IntVar out) {
    lastValIn.add(x);
    lastValOut.add(out);
  }

  /**
   * Adds {@code last_val(x)} for a float variable.
   *
   * @param x the variable of the model.
   * @param out the variable fixed to the last value x was assigned during the search.
   */
  public void addLastVal(FloatVar x, FloatVar out) {
    lastValFloatIn.add(x);
    lastValFloatOut.add(out);
  }

  /**
   * Adds {@code uniform_on_restart(low, high)} for integers.
   *
   * @param low the smallest value.
   * @param high the largest value.
   * @param out the variable fixed to a new random value of low..high in every run.
   */
  public void addUniform(int low, int high, IntVar out) {
    uniformRange.add(new int[] {low, high});
    uniformOut.add(out);
  }

  /**
   * Adds {@code uniform_on_restart(low, high)} for floats.
   *
   * @param low the smallest value.
   * @param high the largest value.
   * @param out the variable fixed to a new random value of low..high in every run.
   */
  public void addUniform(double low, double high, FloatVar out) {
    uniformFloatRange.add(new double[] {low, high});
    uniformFloatOut.add(out);
  }

  /**
   * Adds {@code complete_reif(marker)}: once the marker is true, the search ends at the next
   * restart and is complete.
   *
   * @param marker the Boolean marker.
   */
  public void addComplete(IntVar marker) {
    completeMarkers.add(marker);
  }

  /**
   * Imposes the constraint that records the values assigned to the inputs of {@code last_val} and
   * watches the markers of {@code complete()}. It is called once, before the search.
   *
   * @param store the constraint store.
   */
  public void impose(Store store) {
    if (imposed) {
      return;
    }
    imposed = true;
    lastValues = new int[lastValIn.size()];
    for (int i = 0; i < lastValues.length; i++) {
      lastValues[i] = lastValIn.get(i).min();
    }
    lastFloatValues = new double[lastValFloatIn.size()];
    for (int i = 0; i < lastFloatValues.length; i++) {
      lastFloatValues[i] = lastValFloatIn.get(i).min();
    }
    if (!lastValIn.isEmpty() || !lastValFloatIn.isEmpty() || !completeMarkers.isEmpty()) {
      store.impose(new Recorder());
    }
  }

  @Override
  public void restart(Store store, int lastStatus) {
    int level = store.level;
    for (IntVar s : status) {
      s.domain.in(level, s, lastStatus, lastStatus);
    }
    for (int i = 0; i < solOut.size(); i++) {
      int v = solValues != null ? solValues[i] : solIn.get(i).min();
      fix(level, solOut.get(i), v);
    }
    for (int i = 0; i < solFloatOut.size(); i++) {
      double v = solFloatValues != null ? solFloatValues[i] : solFloatIn.get(i).min();
      fix(level, solFloatOut.get(i), v);
    }
    for (int i = 0; i < lastValOut.size(); i++) {
      fix(level, lastValOut.get(i), lastValues[i]);
    }
    for (int i = 0; i < lastValFloatOut.size(); i++) {
      fix(level, lastValFloatOut.get(i), lastFloatValues[i]);
    }
    for (int i = 0; i < uniformOut.size(); i++) {
      int[] r = uniformRange.get(i);
      int v = (int) (r[0] + Store.getRandom().nextLong((long) r[1] - r[0] + 1));
      fix(level, uniformOut.get(i), v);
    }
    for (int i = 0; i < uniformFloatOut.size(); i++) {
      double[] r = uniformFloatRange.get(i);
      double v = r[0] + Store.getRandom().nextDouble() * (r[1] - r[0]);
      fix(level, uniformFloatOut.get(i), v);
    }
  }

  private static void fix(int level, IntVar x, int v) {
    x.domain.in(level, x, v, v);
  }

  private static void fix(int level, FloatVar x, double v) {
    x.domain.in(level, x, v, v);
  }

  @Override
  public void solution() {
    if (!solIn.isEmpty()) {
      solValues = new int[solIn.size()];
      for (int i = 0; i < solValues.length; i++) {
        solValues[i] = solIn.get(i).value();
      }
    }
    if (!solFloatIn.isEmpty()) {
      solFloatValues = new double[solFloatIn.size()];
      for (int i = 0; i < solFloatValues.length; i++) {
        solFloatValues[i] = solFloatIn.get(i).value();
      }
    }
  }

  @Override
  public boolean completeMarked() {
    return completeMarked;
  }

  /**
   * Records the value of a {@code last_val} input whenever it is assigned and notes a {@code
   * complete()} marker that becomes true. The records are not undone on backtracking.
   */
  class Recorder extends Constraint implements UsesQueueVariable {

    static final AtomicInteger idNumber = new AtomicInteger(0);

    // positions in lastValIn (integer inputs) or lastValFloatIn (float inputs, coded as -1 - i)
    final Map<Var, List<Integer>> positions = new IdentityHashMap<>();

    Recorder() {
      numberId = idNumber.incrementAndGet();
      List<Var> scope = new ArrayList<>();
      for (int i = 0; i < lastValIn.size(); i++) {
        add(scope, lastValIn.get(i), i);
      }
      for (int i = 0; i < lastValFloatIn.size(); i++) {
        add(scope, lastValFloatIn.get(i), -1 - i);
      }
      for (IntVar marker : completeMarkers) {
        add(scope, marker, Integer.MAX_VALUE);
      }
      setScope(scope.toArray(new Var[0]));
    }

    private void add(List<Var> scope, Var v, int position) {
      List<Integer> p = positions.get(v);
      if (p == null) {
        p = new ArrayList<>();
        positions.put(v, p);
        scope.add(v);
      }
      p.add(position);
    }

    @Override
    public void impose(Store store) {
      super.impose(store);
      for (Var v : positions.keySet()) {
        record(v);
      }
    }

    @Override
    public int getDefaultConsistencyPruningEvent() {
      return IntDomain.GROUND;
    }

    @Override
    public void queueVariable(int level, Var v) {
      record(v);
    }

    private void record(Var v) {
      if (!v.singleton()) {
        return;
      }
      for (int p : positions.get(v)) {
        if (p == Integer.MAX_VALUE) {
          completeMarked |= ((IntVar) v).value() == 1;
        } else if (p >= 0) {
          lastValues[p] = ((IntVar) v).value();
        } else {
          lastFloatValues[-1 - p] = ((FloatVar) v).value();
        }
      }
    }

    @Override
    public void consistency(Store store) {
      // records values in queueVariable and prunes nothing
    }

    public boolean satisfied() {
      return true;
    }

    @Override
    public void increaseWeight() {
      // not a constraint of the model, so it takes no part in weighted heuristics
    }

    @Override
    public String toString() {
      return id() + " : OnRestartRecorder(" + positions.keySet() + ")";
    }
  }
}
