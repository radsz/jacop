/*
 * AdaptiveLns.java
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

package org.jacop.search.lns;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;

/**
 * Adaptive large neighbourhood search: chooses which variables a run of a search fixes to their
 * values in the best solution, so that the run searches the neighbourhood made of the other
 * variables. The neighbourhoods come from the model:
 *
 * <ul>
 *   <li>{@link Kind#RANDOM}: variables chosen at random;
 *   <li>{@link Kind#GRAPH}: variables close to each other in the graph of the constraints, grown
 *       from a random variable;
 *   <li>{@link Kind#PROPAGATION}: propagation-guided (Perron, Shaw and Furnon, CP 2004): variables
 *       are fixed one batch at a time, each batch among those whose domains the last one reduced
 *       most, until few enough are left free;
 *   <li>{@link Kind#OBJECTIVE}: grown in the graph from the terms of a linear objective that cost
 *       most in the best solution.
 * </ul>
 *
 * <p>Each kind has its own share of free variables, raised after a run that explored its whole
 * neighbourhood and lowered after a run cut by its limit, so that about half of the runs finish (as
 * in CP-SAT). The kinds are chosen by roulette on a moving average of how often their runs improved
 * the best solution (adaptive LNS, Ropke and Pisinger 2006).
 *
 * <p>The engine calls {@link #solution()} at each improving solution, while the store holds it,
 * {@link #neighbourhood()} before a run and {@link #outcome(Outcome)} after it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class AdaptiveLns {

  /** The kinds of neighbourhood. */
  public enum Kind {
    /** Variables chosen at random. */
    RANDOM,
    /** Variables close in the constraint graph. */
    GRAPH,
    /** Propagation-guided. */
    PROPAGATION,
    /** Grown from the costly terms of the objective. */
    OBJECTIVE
  }

  /** How a run in a neighbourhood ended. */
  public enum Outcome {
    /** The run found a better solution. */
    IMPROVED,
    /** The run explored the whole neighbourhood without a better solution. */
    EXHAUSTED,
    /** The run reached its limit without a better solution. */
    LIMIT
  }

  /** Constraints with more variables than this do not connect variables in the graph. */
  static final int MAX_ARITY = 128;

  /** The failed batches after which a propagation-guided neighbourhood stops fixing variables. */
  static final int MAX_FAILURES = 32;

  private static final double FIRST_SHARE = 0.2;
  private static final double MAX_SHARE = 0.95;
  private static final double SHARE_STEP = 1.15;
  private static final double DECAY = 0.2;
  private static final double FLOOR = 0.1;

  private final Store store;
  private final IntVar[] vars;
  private final IntVar cost;
  private final Random random;
  private final Kind[] kinds;

  // values of the variables and of the objective's terms in the best solution
  private final int[] incumbent;
  private boolean hasIncumbent;

  // the graph: variable nodes (the first vars.length are the variables of the neighbourhoods) and
  // constraint nodes
  private IntVar[] nodes;
  private int[][] varCons;
  private int[][] conVars;
  private int[] seenVar;
  private int[] seenCon;
  private int stamp;
  // the objective's linear terms, as nodes, their weights and values in the best solution
  private int[] terms = new int[0];
  private long[] termWeights = new long[0];
  private int[] termValues = new int[0];

  private final double[] share;
  private final double[] score;
  private final long[] runs;
  private final long[] improvements;
  private Kind last;
  private final boolean[] disabled;

  private long totalRuns;
  private long totalImproved;

  /**
   * Creates the neighbourhoods over the given variables. The graph of the constraints is read now,
   * so it is created at the root, before the search.
   *
   * @param store the store with the model.
   * @param vars the variables that runs fix; usually the decision variables of the model.
   * @param cost the variable minimised, or null; its linear definition guides {@link
   *     Kind#OBJECTIVE}.
   * @param random the source of randomness.
   */
  public AdaptiveLns(Store store, IntVar[] vars, IntVar cost, Random random) {
    this.store = store;
    // each variable once, so that the first nodes of the graph are the variables
    this.vars = new LinkedHashSet<>(Arrays.asList(vars)).toArray(new IntVar[0]);
    this.cost = cost;
    this.random = random;
    this.kinds = Kind.values();
    incumbent = new int[this.vars.length];
    share = new double[kinds.length];
    score = new double[kinds.length];
    runs = new long[kinds.length];
    improvements = new long[kinds.length];
    disabled = new boolean[kinds.length];
    Arrays.fill(share, FIRST_SHARE);
    Arrays.fill(score, 1.0);
    buildGraph();
  }

  /**
   * Stops using a kind of neighbourhood. {@link Kind#PROPAGATION} propagates the store between
   * runs, which a search that keeps its own view of the root (lazy clause generation) may not
   * allow. {@link Kind#RANDOM} cannot be turned off, so at least one kind stays.
   *
   * @param kind the kind.
   * @return this object.
   */
  public AdaptiveLns disable(Kind kind) {
    if (kind != Kind.RANDOM) {
      disabled[kind.ordinal()] = true;
    }
    return this;
  }

  /** Records the best solution; called while the store holds it, with every variable fixed. */
  public void solution() {
    for (int i = 0; i < vars.length; i++) {
      incumbent[i] = vars[i].value();
    }
    for (int k = 0; k < terms.length; k++) {
      termValues[k] = nodes[terms[k]].value();
    }
    hasIncumbent = true;
  }

  /**
   * Returns whether a solution was recorded, so that neighbourhoods can be built.
   *
   * @return true after the first {@link #solution()}.
   */
  public boolean ready() {
    return hasIncumbent && vars.length > 0;
  }

  /**
   * Chooses the next neighbourhood. It is called at the root of the search, between runs; the
   * propagation-guided kind propagates in a level of its own, removed before it returns.
   *
   * @return the indices of the variables to fix to their values in the best solution, which {@link
   *     #value(int)} gives.
   */
  public int[] neighbourhood() {
    Kind kind = choose();
    last = kind;
    runs[kind.ordinal()]++;
    totalRuns++;
    int free = 0;
    for (IntVar x : vars) {
      if (!x.singleton()) {
        free++;
      }
    }
    int relaxed = Math.max(2, (int) Math.round(share[kind.ordinal()] * free));
    if (relaxed >= free) {
      return new int[0];
    }
    boolean[] relax =
        switch (kind) {
          case RANDOM -> randomRelax(relaxed);
          case GRAPH -> graphRelax(relaxed, false);
          case OBJECTIVE -> graphRelax(relaxed, true);
          case PROPAGATION -> null;
        };
    if (relax == null) {
      return propagationGuided(relaxed);
    }
    return fixedOutside(relax);
  }

  /**
   * Returns the value that a variable is fixed to: its value in the best solution.
   *
   * @param i the index of the variable.
   * @return its value in the best solution.
   */
  public int value(int i) {
    return incumbent[i];
  }

  /**
   * Returns the variables of the neighbourhoods.
   *
   * @return the variables, in the order of the indices.
   */
  public IntVar[] variables() {
    return vars.clone();
  }

  /**
   * Reports how the run in the last neighbourhood ended.
   *
   * @param outcome the outcome.
   */
  public void outcome(Outcome outcome) {
    if (last == null) {
      return;
    }
    int k = last.ordinal();
    double reward = outcome == Outcome.IMPROVED ? 1.0 : 0.0;
    score[k] = (1 - DECAY) * score[k] + DECAY * (reward + FLOOR);
    switch (outcome) {
      case IMPROVED -> {
        improvements[k]++;
        totalImproved++;
      }
      case EXHAUSTED -> share[k] = Math.min(MAX_SHARE, share[k] * SHARE_STEP);
      case LIMIT -> share[k] = Math.max(1e-4, share[k] / SHARE_STEP);
    }
    last = null;
  }

  /**
   * Returns the number of runs in neighbourhoods so far.
   *
   * @return the number of runs.
   */
  public long runs() {
    return totalRuns;
  }

  /**
   * Returns the number of runs that improved the best solution.
   *
   * @return the number of improving runs.
   */
  public long improved() {
    return totalImproved;
  }

  /**
   * Returns the runs and improvements of each kind, for statistics.
   *
   * @return text such as {@code RANDOM 10/2 0.21}: runs, improving runs and share of free
   *     variables.
   */
  public String statistics() {
    StringBuilder b = new StringBuilder();
    for (Kind k : kinds) {
      if (!b.isEmpty()) {
        b.append(", ");
      }
      int i = k.ordinal();
      b.append(k)
          .append(' ')
          .append(runs[i])
          .append('/')
          .append(improvements[i])
          .append(' ')
          .append(String.format("%.3f", share[i]));
    }
    return b.toString();
  }

  private Kind choose() {
    double total = 0;
    for (Kind k : kinds) {
      if (enabled(k)) {
        total += score[k.ordinal()];
      }
    }
    double r = random.nextDouble() * total;
    Kind chosen = Kind.RANDOM;
    for (Kind k : kinds) {
      if (enabled(k)) {
        chosen = k;
        r -= score[k.ordinal()];
        if (r < 0) {
          break;
        }
      }
    }
    return chosen;
  }

  private boolean enabled(Kind k) {
    if (disabled[k.ordinal()]) {
      return false;
    }
    return k != Kind.OBJECTIVE || terms.length > 0;
  }

  private boolean[] randomRelax(int relaxed) {
    boolean[] relax = new boolean[vars.length];
    int[] order = freeOrder();
    for (int i = 0; i < relaxed && i < order.length; i++) {
      relax[order[i]] = true;
    }
    return relax;
  }

  /** The variables not fixed at the root, in random order. */
  private int[] freeOrder() {
    int[] order = new int[vars.length];
    int n = 0;
    for (int i = 0; i < vars.length; i++) {
      if (!vars[i].singleton()) {
        order[n++] = i;
      }
    }
    order = Arrays.copyOf(order, n);
    for (int i = n - 1; i > 0; i--) {
      int j = random.nextInt(i + 1);
      int t = order[i];
      order[i] = order[j];
      order[j] = t;
    }
    return order;
  }

  /**
   * Relaxes the variables met first by a breadth-first walk of the constraint graph, from a random
   * variable or from a costly term of the objective. A walk that runs out of nodes starts again
   * from a new seed.
   */
  private boolean[] graphRelax(int relaxed, boolean objective) {
    boolean[] relax = new boolean[vars.length];
    stamp++;
    int[] queue = new int[nodes.length];
    int head = 0;
    int tail = 0;
    int count = 0;
    int[] order = freeOrder();
    int nextSeed = 0;
    while (count < relaxed) {
      if (head == tail) {
        int seed = objective ? costlyTerm() : -1;
        if (seed < 0 || seenVar[seed] == stamp) {
          while (nextSeed < order.length && seenVar[order[nextSeed]] == stamp) {
            nextSeed++;
          }
          if (nextSeed == order.length) {
            break;
          }
          seed = order[nextSeed];
        }
        seenVar[seed] = stamp;
        queue[tail++] = seed;
      }
      int v = queue[head++];
      if (v < vars.length && !vars[v].singleton() && !relax[v]) {
        relax[v] = true;
        count++;
      }
      int[] cs = varCons[v];
      // the constraints are visited from a random one, so that equal walks differ
      int start = cs.length == 0 ? 0 : random.nextInt(cs.length);
      for (int j = 0; j < cs.length; j++) {
        int c = cs[(start + j) % cs.length];
        if (seenCon[c] == stamp) {
          continue;
        }
        seenCon[c] = stamp;
        for (int u : conVars[c]) {
          if (seenVar[u] != stamp) {
            seenVar[u] = stamp;
            queue[tail++] = u;
          }
        }
      }
    }
    return relax;
  }

  /**
   * A term of the objective, chosen with a probability proportional to what it costs in the best
   * solution; -1 when no term costs anything.
   */
  private int costlyTerm() {
    double total = 0;
    for (int k = 0; k < terms.length; k++) {
      total += Math.max(0, (double) termWeights[k] * termValues[k]);
    }
    if (total <= 0) {
      return terms.length == 0 ? -1 : terms[random.nextInt(terms.length)];
    }
    double r = random.nextDouble() * total;
    for (int k = 0; k < terms.length; k++) {
      r -= Math.max(0, (double) termWeights[k] * termValues[k]);
      if (r < 0) {
        return terms[k];
      }
    }
    return terms[terms.length - 1];
  }

  /**
   * Propagation-guided neighbourhood: fixes batches of variables to their values in the best
   * solution and propagates, until at most the given number of variables is left free. Each batch
   * is a quarter of the variables still to fix, taken first among those whose domains the last
   * batch reduced most and then at random. A batch that fails is not fixed and ends the
   * neighbourhood.
   */
  private int[] propagationGuided(int relaxed) {
    int level = store.level;
    int[] order = freeOrder();
    int nextRandom = 0;
    int[] size = new int[vars.length];
    double[] reduction = new double[vars.length];
    boolean[] chosen = new boolean[vars.length];
    List<Integer> fixed = new ArrayList<>();
    Integer[] candidates = new Integer[vars.length];
    // batches that fail are halved; their variables stay free when a single one fails
    int maxBatch = Integer.MAX_VALUE;
    int failures = 0;
    store.setLevel(level + 1);
    try {
      int free = order.length;
      while (free > relaxed && failures < MAX_FAILURES) {
        for (int i = 0; i < vars.length; i++) {
          size[i] = vars[i].getSize();
        }
        int batch = Math.max(1, Math.min(maxBatch, (free - relaxed) / 4));
        int nc = 0;
        for (int i = 0; i < vars.length; i++) {
          if (reduction[i] > 0 && !vars[i].singleton() && !chosen[i]) {
            candidates[nc++] = i;
          }
        }
        Arrays.sort(candidates, 0, nc, (a, b) -> Double.compare(reduction[b], reduction[a]));
        List<Integer> step = new ArrayList<>(batch);
        for (int j = 0; j < nc && step.size() < batch; j++) {
          step.add(candidates[j]);
        }
        while (step.size() < batch && nextRandom < order.length) {
          int i = order[nextRandom++];
          if (!vars[i].singleton() && !chosen[i] && !step.contains(i)) {
            step.add(i);
          }
        }
        if (step.size() < batch) {
          // the random order is used up: start it again over the variables not chosen yet
          for (int i : order) {
            if (step.size() >= batch) {
              break;
            }
            if (!vars[i].singleton() && !chosen[i] && !step.contains(i)) {
              step.add(i);
            }
          }
        }
        if (step.isEmpty()) {
          break;
        }
        store.setLevel(store.level + 1);
        boolean consistent = true;
        try {
          for (int i : step) {
            if (vars[i].domain.contains(incumbent[i])) {
              vars[i].domain.inValue(store.level, vars[i], incumbent[i]);
            }
          }
          consistent = store.consistency();
        } catch (FailException _) {
          consistent = false;
        }
        if (!consistent) {
          // nogoods learned under the bound on the objective may exclude the best solution
          store.recentlyFailedConstraint = null;
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
          failures++;
          if (step.size() == 1) {
            chosen[step.get(0)] = true;
          }
          maxBatch = Math.max(1, step.size() / 2);
          continue;
        }
        if (maxBatch < Integer.MAX_VALUE / 2) {
          maxBatch *= 2;
        }
        for (int i : step) {
          chosen[i] = true;
        }
        for (int i : step) {
          if (vars[i].singleton() && vars[i].value() == incumbent[i]) {
            fixed.add(i);
          }
        }
        free = 0;
        for (int i = 0; i < vars.length; i++) {
          if (!vars[i].singleton()) {
            free++;
            reduction[i] = size[i] > 0 ? 1.0 - (double) vars[i].getSize() / size[i] : 0;
          } else {
            reduction[i] = 0;
          }
        }
      }
    } finally {
      while (store.level > level) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
    }
    int[] result = new int[fixed.size()];
    for (int j = 0; j < result.length; j++) {
      result[j] = fixed.get(j);
    }
    return result;
  }

  /** The variables outside the relaxed ones that can take their values in the best solution. */
  private int[] fixedOutside(boolean[] relax) {
    int[] fixed = new int[vars.length];
    int n = 0;
    for (int i = 0; i < vars.length; i++) {
      if (!relax[i] && !vars[i].singleton() && vars[i].domain.contains(incumbent[i])) {
        fixed[n++] = i;
      }
    }
    return Arrays.copyOf(fixed, n);
  }

  /**
   * Builds the graph of the variables and constraints of the store. Constraints with more than
   * {@link #MAX_ARITY} variables, and those on the objective, link too much to describe closeness,
   * so they are left out; the linear definition of the objective gives its terms.
   */
  private void buildGraph() {
    Map<Var, Integer> nodeOf = new IdentityHashMap<>();
    List<IntVar> nodeList = new ArrayList<>();
    for (IntVar x : vars) {
      nodeOf.put(x, nodeList.size());
      nodeList.add(x);
    }
    List<IntVar> others = new ArrayList<>();
    for (int i = 0; i < store.size(); i++) {
      if (store.vars[i] instanceof IntVar x) {
        others.add(x);
      }
    }
    store.variablesHashMap.values().stream()
        .filter(BooleanVar.class::isInstance)
        .map(BooleanVar.class::cast)
        .sorted((a, b) -> a.id().compareTo(b.id()))
        .forEach(others::add);
    for (IntVar x : others) {
      if (!nodeOf.containsKey(x)) {
        nodeOf.put(x, nodeList.size());
        nodeList.add(x);
      }
    }
    nodes = nodeList.toArray(new IntVar[0]);
    Map<Constraint, Integer> conOf = new IdentityHashMap<>();
    List<int[]> conList = new ArrayList<>();
    List<List<Integer>> adjacency = new ArrayList<>();
    for (int i = 0; i < nodes.length; i++) {
      adjacency.add(new ArrayList<>());
    }
    for (IntVar x : nodes) {
      for (Constraint c : x.dom().constraints()) {
        if (conOf.containsKey(c)) {
          continue;
        }
        conOf.put(c, -1);
        if (cost != null && c.arguments().contains(cost)) {
          readObjective(c, nodeOf);
          continue;
        }
        if (c.arguments().size() > MAX_ARITY) {
          continue;
        }
        int[] members =
            c.arguments().stream()
                .map(nodeOf::get)
                .filter(java.util.Objects::nonNull)
                .mapToInt(Integer::intValue)
                .sorted()
                .toArray();
        if (members.length < 2) {
          continue;
        }
        int id = conList.size();
        conOf.put(c, id);
        conList.add(members);
        for (int v : members) {
          adjacency.get(v).add(id);
        }
      }
    }
    conVars = conList.toArray(new int[0][]);
    varCons = new int[nodes.length][];
    for (int i = 0; i < nodes.length; i++) {
      varCons[i] = adjacency.get(i).stream().mapToInt(Integer::intValue).toArray();
    }
    seenVar = new int[nodes.length];
    seenCon = new int[conVars.length];
  }

  /**
   * Reads the terms of the objective from its linear definition {@code sum(w * t) + a * cost = c}:
   * cost = (c - sum(w * t)) / a, so a term costs -w / a times its value. The terms that are fixed
   * at the root cost the same in every solution and are left out.
   */
  private void readObjective(Constraint c, Map<Var, Integer> nodeOf) {
    if (terms.length > 0) {
      return;
    }
    LinearForm f = LinearForms.of(c);
    if (f == null || f.relation() != LinearForm.EQ) {
      return;
    }
    long a = 0;
    for (int i = 0; i < f.vars().length; i++) {
      if (f.vars()[i] == cost) {
        a += f.weights()[i];
      }
    }
    if (a == 0) {
      return;
    }
    List<Integer> ts = new ArrayList<>();
    List<Long> ws = new ArrayList<>();
    for (int i = 0; i < f.vars().length; i++) {
      IntVar t = f.vars()[i];
      Integer node = nodeOf.get(t);
      if (t == cost || t.singleton() || node == null) {
        continue;
      }
      ts.add(node);
      // the sign of -w / a; its size relative to other terms is what matters
      ws.add(a > 0 ? -f.weights()[i] : f.weights()[i]);
    }
    terms = ts.stream().mapToInt(Integer::intValue).toArray();
    termWeights = ws.stream().mapToLong(Long::longValue).toArray();
    termValues = new int[terms.length];
  }
}
