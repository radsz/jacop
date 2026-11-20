/*
 * FunctionalModel.java
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import org.jacop.api.Functional;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.cumulative.EnergyPrecedence;
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;
import org.jacop.search.ls.FunctionalTabuSearch;

/**
 * A model whose cost is a function of a few decision variables: following the definitions back from
 * the cost, every constraint of the store defines one variable, as a linear equality with a unit
 * coefficient on it, a product or another {@link Functional} constraint, and the variables no
 * constraint defines are the decision variables. Any assignment of those whose defined values lie
 * in their domains is then a solution, which {@link FunctionalTabuSearch} searches by changing one
 * decision variable at a time. Low autocorrelation binary sequences (XCSP 2025) are such a model:
 * the cost is the sum of the squares of the autocorrelations, each a sum of products of two
 * variables of the sequence.
 *
 * <p>A model with at least one definition that is not linear is taken; one that is all linear is
 * left to the solver.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class FunctionalModel {

  // the largest domain of a decision variable, whose values are all tried by a move
  static final int DOMAIN_LIMIT = 64;

  // the most variables a function other than a sum or a product reads: it is evaluated whole after
  // every trial move, so a count over 10,000 variables made each step of the walk take seconds and
  // the walk kept 90 % of the time without a solution
  static final int FUNCTION_INPUTS = 1024;

  /** The decision variables. */
  final IntVar[] vars;

  /** The variables of the search, the decision variables among them. */
  final IntVar[] all;

  // the index of each decision variable among them, and the cost
  private final int[] decisionIndex;
  private final int[] kind;
  private final int[][] inputs;
  private final long[][] coefficients;
  private final long[] constant;
  private final FunctionalTabuSearch.Definition[] functions;
  private final IntDomain[] domains;
  private final int cost;

  private FunctionalModel(
      IntVar[] all,
      int[] kind,
      int[][] inputs,
      long[][] coefficients,
      long[] constant,
      FunctionalTabuSearch.Definition[] functions,
      int cost) {
    this.all = all;
    this.kind = kind;
    this.inputs = inputs;
    this.coefficients = coefficients;
    this.constant = constant;
    this.functions = functions;
    this.cost = cost;
    domains = new IntDomain[all.length];
    List<IntVar> ds = new ArrayList<>();
    List<Integer> is = new ArrayList<>();
    for (int v = 0; v < all.length; v++) {
      domains[v] = all[v].dom().cloneLight();
      if (kind[v] == FunctionalTabuSearch.DECISION) {
        ds.add(all[v]);
        is.add(v);
      }
    }
    vars = ds.toArray(new IntVar[0]);
    decisionIndex = is.stream().mapToInt(Integer::intValue).toArray();
  }

  /** The tabu search over the model. */
  FunctionalTabuSearch search(long seed) {
    return new FunctionalTabuSearch(
        kind, inputs, coefficients, constant, functions, domains, cost, seed);
  }

  /** The values of the decision variables in an assignment of every variable of the search. */
  int[] values(int[] assignment) {
    int[] vs = new int[vars.length];
    for (int k = 0; k < vars.length; k++) {
      vs[k] = assignment[decisionIndex[k]];
    }
    return vs;
  }

  /** The assignment of the search's variables for values of the decision variables. */
  int[] assignment(int[] values) {
    int[] a = new int[all.length];
    for (int k = 0; k < vars.length; k++) {
      a[decisionIndex[k]] = values[k];
    }
    return a;
  }

  /**
   * The model of the store, or null when it is not one.
   *
   * @param store the store
   * @param clauses the clauses kept for the LCG solver, which the model may not have
   * @param cost the variable minimized
   * @param ignored constraints left out (symmetry breaking, whose solutions are mapped)
   * @param log takes the reason when the store is no such model, or null
   * @return the model, or null
   */
  static FunctionalModel detect(
      Store store,
      List<IntVar[][]> clauses,
      IntVar cost,
      Collection<Constraint> ignored,
      Consumer<String> log) {
    if (!clauses.isEmpty() || cost.singleton()) {
      return no(log, "clauses kept for the solver, or a fixed cost");
    }
    Set<Constraint> constraints = new LinkedHashSet<>();
    Set<Var> every = new LinkedHashSet<>();
    for (int i = 0; i < store.size(); i++) {
      if (store.vars[i] != null) {
        every.add(store.vars[i]);
      }
    }
    every.addAll(store.variablesHashMap.values());
    for (Var v : every) {
      constraints.addAll(v.dom().constraints());
      constraints.addAll(store.valueWatchers(v));
    }
    constraints.addAll(store.watchedLiteralConstraints());
    constraints.removeIf(
        c ->
            c instanceof LinearRelaxation
                || c instanceof EnergyPrecedence
                || store.isImplied(c)
                || ignored.contains(c));
    // the definitions each variable may have: functional constraints by their result, linear
    // equalities by every variable with a unit coefficient
    Map<IntVar, Constraint> functional = new IdentityHashMap<>();
    Map<Constraint, LinearForm> forms = new IdentityHashMap<>();
    Set<Constraint> used = Collections.newSetFromMap(new IdentityHashMap<>());
    Map<IntVar, List<Constraint>> equalities = new IdentityHashMap<>();
    for (Constraint c : constraints) {
      for (Var v : c.arguments()) {
        if (!(v instanceof IntVar)) {
          return no(log, "a variable that is not an integer variable in " + c);
        }
      }
      if (c instanceof Functional f) {
        IntVar z = f.functionalResult();
        if (z.singleton() && entailed(c, f)) {
          // a result that is the same for every value of the inputs (a square of -1..1 values)
          used.add(c);
          continue;
        }
        if (z.singleton() || functional.put(z, c) != null) {
          return no(log, "a fixed result or two definitions of " + z);
        }
        continue;
      }
      LinearForm f = LinearForms.of(c);
      if (f == null || f.relation() != LinearForm.EQ) {
        return no(log, "not a definition: " + c);
      }
      forms.put(c, f);
      for (IntVar z : f.vars()) {
        List<Constraint> on = equalities.computeIfAbsent(z, k -> new ArrayList<>());
        if (on.isEmpty() || on.get(on.size() - 1) != c) {
          on.add(c);
        }
      }
    }
    // from the cost back: each variable reached takes its definition, the others are decisions
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    List<IntVar> vs = new ArrayList<>();
    List<Constraint> definition = new ArrayList<>();
    ArrayDeque<IntVar> wide = new ArrayDeque<>();
    index.put(cost, 0);
    vs.add(cost);
    definition.add(null);
    wide.add(cost);
    while (true) {
      if (wide.isEmpty()) {
        // a definition the cost does not read (the product under a square of -1..1 values) still
        // gives its variable a value
        IntVar root = root(constraints, used, index, forms);
        if (root == null) {
          break;
        }
        index.put(root, vs.size());
        vs.add(root);
        definition.add(null);
        wide.add(root);
      }
      IntVar y = wide.poll();
      Constraint def = functional.get(y);
      if (def != null && used.contains(def)) {
        return no(log, "a variable defined twice: " + y);
      }
      if (def == null) {
        for (Constraint c : equalities.getOrDefault(y, List.of())) {
          if (!used.contains(c) && Math.abs(weight(forms.get(c), y)) == 1) {
            def = c;
            break;
          }
        }
      }
      if (def == null) {
        // a decision variable
        continue;
      }
      used.add(def);
      definition.set(index.get(y), def);
      for (Var v : def.arguments()) {
        IntVar z = (IntVar) v;
        if (z != y && !z.singleton() && !index.containsKey(z)) {
          index.put(z, vs.size());
          vs.add(z);
          definition.add(null);
          wide.add(z);
        }
      }
    }
    if (used.size() != constraints.size()) {
      // a constraint that defines nothing
      return no(log, "constraints that define nothing: " + (constraints.size() - used.size()));
    }
    int n = vs.size();
    int[] kind = new int[n];
    int[][] inputs = new int[n][];
    long[][] coefficients = new long[n][];
    long[] constant = new long[n];
    FunctionalTabuSearch.Definition[] functions = new FunctionalTabuSearch.Definition[n];
    int decisions = 0;
    boolean nonlinear = false;
    for (int v = 0; v < n; v++) {
      IntVar y = vs.get(v);
      Constraint def = definition.get(v);
      if (def == null) {
        if (y.getSize() > DOMAIN_LIMIT) {
          return no(log, "a decision variable of " + y.getSize() + " values: " + y);
        }
        kind[v] = FunctionalTabuSearch.DECISION;
        inputs[v] = new int[0];
        decisions++;
      } else if (def instanceof XmulYeqZ m && m.x() != y && m.y() != y) {
        nonlinear = true;
        kind[v] = FunctionalTabuSearch.PRODUCT;
        if (m.x().singleton() || m.y().singleton()) {
          // a product by a constant is linear
          IntVar w = m.x().singleton() ? m.y() : m.x();
          int c = m.x().singleton() ? m.x().value() : m.y().value();
          kind[v] = FunctionalTabuSearch.LINEAR;
          inputs[v] = new int[] {index.get(w)};
          coefficients[v] = new long[] {c};
        } else {
          inputs[v] = new int[] {index.get(m.x()), index.get(m.y())};
        }
      } else if (def instanceof Functional f) {
        nonlinear = true;
        kind[v] = FunctionalTabuSearch.FUNCTION;
        List<Integer> in = new ArrayList<>();
        for (Var u : def.arguments()) {
          if (u != y && !((IntVar) u).singleton()) {
            in.add(index.get((IntVar) u));
          }
        }
        inputs[v] = in.stream().mapToInt(Integer::intValue).toArray();
        Map<IntVar, Integer> at = index;
        functions[v] =
            of ->
                f.functionalValue(
                    x ->
                        x.singleton() && !at.containsKey(x) ? x.value() : of.applyAsInt(at.get(x)));
      } else {
        // y = a (c - sum of the other terms), with a = +-1 the weight of y
        LinearForm f = forms.get(def);
        long a = weight(f, y);
        Map<Integer, Long> terms = new java.util.LinkedHashMap<>();
        long c = a * f.c();
        for (int k = 0; k < f.vars().length; k++) {
          IntVar z = f.vars()[k];
          if (z == y) {
            continue;
          }
          if (z.singleton()) {
            c -= a * f.weights()[k] * z.value();
          } else {
            terms.merge(index.get(z), -a * f.weights()[k], Long::sum);
          }
        }
        kind[v] = FunctionalTabuSearch.LINEAR;
        inputs[v] = terms.keySet().stream().mapToInt(Integer::intValue).toArray();
        coefficients[v] = terms.values().stream().mapToLong(Long::longValue).toArray();
        constant[v] = c;
      }
    }
    if (!nonlinear || decisions < 2) {
      return no(log, nonlinear ? decisions + " decision variables" : "only linear definitions");
    }
    for (int v = 0; v < n; v++) {
      if (kind[v] == FunctionalTabuSearch.FUNCTION && inputs[v].length > FUNCTION_INPUTS) {
        return no(log, "a function of " + inputs[v].length + " variables: " + definition.get(v));
      }
    }
    try {
      FunctionalModel model =
          new FunctionalModel(
              vs.toArray(new IntVar[0]), kind, inputs, coefficients, constant, functions, 0);
      // a cycle of definitions throws
      model.search(0);
      return model;
    } catch (IllegalArgumentException e) {
      return no(log, "a cycle of definitions");
    }
  }

  // a variable that an unused constraint defines and the search has no variable for, or null
  private static IntVar root(
      Set<Constraint> constraints,
      Set<Constraint> used,
      Map<IntVar, Integer> index,
      Map<Constraint, LinearForm> forms) {
    for (Constraint c : constraints) {
      if (used.contains(c)) {
        continue;
      }
      if (c instanceof Functional f) {
        IntVar z = f.functionalResult();
        if (!index.containsKey(z)) {
          return z;
        }
      } else {
        LinearForm f = forms.get(c);
        for (IntVar z : f.vars()) {
          if (!z.singleton() && !index.containsKey(z) && Math.abs(weight(f, z)) == 1) {
            return z;
          }
        }
      }
    }
    return null;
  }

  // the largest number of assignments of the inputs enumerated to check a constant result
  private static final int ENTAILED_LIMIT = 4096;

  // true when the function gives the value of its fixed result for every assignment of the inputs
  private static boolean entailed(Constraint c, Functional f) {
    IntVar z = f.functionalResult();
    List<IntVar> in = new ArrayList<>();
    long box = 1;
    for (Var v : c.arguments()) {
      IntVar x = (IntVar) v;
      if (x != z && !x.singleton()) {
        in.add(x);
        box *= x.getSize();
        if (box > ENTAILED_LIMIT) {
          return false;
        }
      }
    }
    int[][] values = new int[in.size()][];
    for (int k = 0; k < values.length; k++) {
      values[k] = new int[in.get(k).getSize()];
      int i = 0;
      for (var e = in.get(k).dom().valueEnumeration(); e.hasMoreElements(); ) {
        values[k][i++] = e.nextElement();
      }
    }
    int[] at = new int[values.length];
    Map<IntVar, Integer> position = new IdentityHashMap<>();
    for (int k = 0; k < values.length; k++) {
      position.put(in.get(k), k);
    }
    while (true) {
      int r =
          f.functionalValue(
              x -> {
                Integer k = position.get(x);
                return k == null ? x.value() : values[k][at[k]];
              });
      if (r != z.value()) {
        return false;
      }
      int k = 0;
      while (k < at.length && ++at[k] == values[k].length) {
        at[k] = 0;
        k++;
      }
      if (k == at.length) {
        return true;
      }
    }
  }

  private static FunctionalModel no(Consumer<String> log, String why) {
    if (log != null) {
      log.accept(why);
    }
    return null;
  }

  // the weight of y in a linear form
  private static long weight(LinearForm f, IntVar y) {
    long w = 0;
    for (int k = 0; k < f.vars().length; k++) {
      if (f.vars()[k] == y) {
        w += f.weights()[k];
      }
    }
    return w;
  }
}
