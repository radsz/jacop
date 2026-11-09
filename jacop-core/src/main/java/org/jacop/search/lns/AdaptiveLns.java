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
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.AbstractElement;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.Routes;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.diffn.Nooverlap;
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
 *       most in the best solution;
 *   <li>{@link Kind#CONSTRAINTS}: all the variables of constraints chosen at random (CP-SAT's
 *       random constraints neighbourhood);
 *   <li>{@link Kind#SCHEDULING}: the tasks of the cumulative and unary resources that start in a
 *       window of time of the best solution, the window placed at random;
 *   <li>{@link Kind#PACKING}: the rectangles of a non-overlap constraint placed nearest to one
 *       chosen at random in the best solution (CP-SAT's packing neighbourhoods);
 *   <li>{@link Kind#ROUTES} and {@link Kind#RELATED}: with vehicle routes ({@link Routes}, imposed
 *       or given by {@link #addRoutes(Routes)}, or the successors of a {@link Circuit} or {@link
 *       Subcircuit}, a giant tour), the customers of whole routes, or customers near each other,
 *       removed from the best solution and reinserted by the run (see {@link RouteNeighbourhoods}
 *       and {@link SuccessorRoutes}).
 * </ul>
 *
 * <p>A neighbourhood made of variables that the runs do not fix (a task's start defined by the
 * model, a successor that is not a decision) relaxes the decision variables nearest to them in the
 * graph of the constraints.
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
    OBJECTIVE,
    /** The variables of random constraints. */
    CONSTRAINTS,
    /** The tasks that start in a window of time. */
    SCHEDULING,
    /** Rectangles near each other. */
    PACKING,
    /** The customers of whole vehicle routes, near each other. */
    ROUTES,
    /** Customers related by the cost of the arcs between them (Shaw removal). */
    RELATED,
    /**
     * The tasks that start in a window of time, with the tasks after it free to start earlier: a
     * shift to the left of the schedule after the window.
     */
    SHIFT
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

  /**
   * Constraints with more variables than this do not lead from a variable that runs do not fix to
   * the decision variables near it.
   */
  static final int NEAR_ARITY = 8;

  /** Constraints of at most this many variables tie a task's companions to it. */
  static final int COMPANION_ARITY = 3;

  /** The most decision variables that a variable runs do not fix stands for. */
  static final int MAX_NEAR = 16;

  /** The failed batches after which a propagation-guided neighbourhood stops fixing variables. */
  static final int MAX_FAILURES = 32;

  /** The nearest customers each node of a circuit keeps for Shaw removal. */
  static final int NEAR_COUNT = 32;

  /** The fewest nodes of a circuit worth routes. */
  static final int MIN_CIRCUIT = 4;

  /** Circuits with more nodes than this get no costs, so Shaw removal follows the routes. */
  static final int MAX_COST_NODES = 4096;

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
  private int[] termMin = new int[0];
  private int[] termMax = new int[0];
  // the tasks of the resources (nodes of their start, duration and resource)
  private int[][] tasks = new int[0][];
  // the rectangles of non-overlap constraints, as nodes of x, y, width and height (-1 - value for a
  // constant), one array per constraint
  private int[][][] packings = new int[0][][];
  // the nodes whose values in the best solution the neighbourhoods read, and those values
  private int[] watched = new int[0];
  private int[] nodeValue;
  // the decision variables each node stands for, computed when first needed
  private int[][] near;
  private Map<Var, Integer> nodeOf;
  // the vehicle routes of the model
  private final List<RouteStructure> routings = new ArrayList<>();
  private final List<Routes> imposedRoutes = new ArrayList<>();
  private final List<Constraint> imposedCircuits = new ArrayList<>();
  // the variables that are successors of a circuit among the routings
  private final boolean[] successorVar;

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
    for (Routes r : imposedRoutes) {
      addRoutes(r);
    }
    imposedRoutes.clear();
    successorVar = new boolean[this.vars.length];
    for (Constraint c : imposedCircuits) {
      if (c instanceof Circuit k) {
        addCircuit(k.successors(), k.offset());
      } else if (c instanceof Subcircuit k) {
        addCircuit(k.successors(), 1);
      }
    }
    imposedCircuits.clear();
  }

  /**
   * The routes of a circuit's successors; their costs come from element constraints over a
   * successor and a list of integers (the distance from the node to each next node), preferring the
   * one whose value is a term of the objective.
   */
  private void addCircuit(IntVar[] x, int offset) {
    int n = x.length;
    if (n < MIN_CIRCUIT) {
      return;
    }
    int[] varIndex = new int[n];
    boolean any = false;
    for (int v = 0; v < n; v++) {
      Integer node = nodeOf.get(x[v]);
      varIndex[v] = node != null && node < vars.length ? node : -1;
      any |= varIndex[v] >= 0 && !x[v].singleton();
    }
    if (!any) {
      return;
    }
    Set<Integer> objectiveTerms = new HashSet<>();
    for (int t : terms) {
      objectiveTerms.add(t);
    }
    long[][] localCost = new long[n][];
    boolean found = false;
    for (int v = 0; v < n && n <= MAX_COST_NODES; v++) {
      int[] list = null;
      int listOffset = 0;
      for (Constraint c : x[v].constraintsWithWatches()) {
        if (!(c instanceof AbstractElement e) || e.index() != x[v]) {
          continue;
        }
        int[] values;
        IntVar value;
        if (c instanceof ElementInteger ei) {
          values = ei.values();
          value = ei.value();
        } else if (c instanceof ElementIntegerFast ef) {
          values = ef.values();
          value = ef.value();
        } else {
          continue;
        }
        Integer valueNode = nodeOf.get(value);
        boolean objective = valueNode != null && objectiveTerms.contains(valueNode);
        if (list == null || objective) {
          list = values;
          listOffset = e.indexOffset();
          if (objective) {
            break;
          }
        }
      }
      if (list != null) {
        localCost[v] = new long[n];
        for (int w = 0; w < n; w++) {
          // node w is the value w + offset, read at w + offset - listOffset - 1
          int k = w + offset - listOffset - 1;
          localCost[v][w] = k >= 0 && k < list.length ? list[k] : Long.MAX_VALUE;
        }
        found = true;
      }
    }
    SuccessorRoutes r =
        new SuccessorRoutes(x, offset, varIndex, found ? localCost : null, NEAR_COUNT);
    if (r.customerCount() > 1) {
      routings.add(r);
      for (int i : varIndex) {
        if (i >= 0) {
          successorVar[i] = true;
        }
      }
    }
  }

  /**
   * Adds vehicle routes for the {@link Kind#ROUTES} and {@link Kind#RELATED} neighbourhoods, from a
   * {@link Routes} that need not be imposed (its literals are variables of the store). Routes
   * imposed in the store are added by the constructor. It is called before the first solution.
   *
   * @param routes the routes.
   * @return this object.
   */
  public AdaptiveLns addRoutes(Routes routes) {
    for (RouteStructure known : routings) {
      if (known instanceof RouteNeighbourhoods arcs && arcs.sameAs(routes)) {
        return this;
      }
    }
    int[] literalNode = new int[routes.literals.length];
    boolean searched = false;
    for (int k = 0; k < literalNode.length; k++) {
      Integer node = nodeOf.get(routes.literals[k]);
      literalNode[k] = node == null ? -1 : node;
      searched |= node != null && node < vars.length;
    }
    if (!searched) {
      // arcs that are none of the variables, such as the Booleans the FlatZinc front end adds over
      // the successors of a giant tour: the circuit itself gives the routes
      return this;
    }
    long[] termCost = new long[nodes.length];
    for (int k = 0; k < terms.length; k++) {
      termCost[terms[k]] += termWeights[k];
    }
    RouteNeighbourhoods r =
        new RouteNeighbourhoods(routes, literalNode, termCost, conVars, varCons, vars.length);
    if (r.customerCount() > 1) {
      routings.add(r);
    }
    return this;
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

  /** The routing structures, for tests. */
  List<RouteStructure> routings() {
    return routings;
  }

  /** Records the best solution; called while the store holds it, with every variable fixed. */
  public void solution() {
    for (int i = 0; i < vars.length; i++) {
      incumbent[i] = vars[i].value();
    }
    for (int k = 0; k < terms.length; k++) {
      termValues[k] = nodes[terms[k]].value();
    }
    for (int u : watched) {
      // a variable that no constraint of the solver uses may be left unfixed
      nodeValue[u] = nodes[u].singleton() ? nodes[u].value() : nodes[u].min();
    }
    for (RouteStructure r : routings) {
      r.solution();
    }
    hasIncumbent = true;
  }

  /**
   * Records as the best solution one given by values rather than held by the store: the solution
   * that another search found before this one, which the store no longer admits once the search
   * must improve on it. Nothing is recorded when a variable of the neighbourhoods, a node they
   * read, has no value given and is not fixed, or when the neighbourhoods follow vehicle routes,
   * which read their solution from the store.
   *
   * @param xs variables of the store
   * @param values their values in the solution
   * @return true when the solution was recorded
   */
  public boolean solution(IntVar[] xs, int[] values) {
    if (!routings.isEmpty()) {
      return false;
    }
    Map<IntVar, Integer> valueOf = new IdentityHashMap<>();
    for (int k = 0; k < xs.length; k++) {
      valueOf.put(xs[k], values[k]);
    }
    int[] given = new int[nodes.length];
    boolean[] known = new boolean[nodes.length];
    for (int u = 0; u < nodes.length; u++) {
      Integer v = valueOf.get(nodes[u]);
      if (v != null) {
        given[u] = v;
        known[u] = true;
      } else if (nodes[u].singleton()) {
        given[u] = nodes[u].value();
        known[u] = true;
      }
    }
    for (int i = 0; i < vars.length; i++) {
      if (!known[i]) {
        return false;
      }
    }
    for (int k = 0; k < terms.length; k++) {
      if (!known[terms[k]]) {
        return false;
      }
    }
    System.arraycopy(given, 0, incumbent, 0, vars.length);
    for (int k = 0; k < terms.length; k++) {
      termValues[k] = given[terms[k]];
    }
    for (int u : watched) {
      nodeValue[u] = known[u] ? given[u] : nodes[u].min();
    }
    hasIncumbent = true;
    return true;
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
    return neighbourhood(choose());
  }

  private static final boolean SHIFT_ON = Boolean.getBoolean("org.jacop.lns.shift");

  // the variables that the last neighbourhood bounds from above by their values instead of fixing
  private int[] bounded = new int[0];

  /**
   * Returns the variables that the last {@link #neighbourhood()} neither fixes nor relaxes but
   * bounds from above by their values in the best solution, {@link #value(int)}: the tasks after
   * the window of a {@link Kind#SHIFT} neighbourhood, which may start earlier.
   *
   * @return their indices, empty for the other kinds
   */
  public int[] upperBounded() {
    return bounded;
  }

  /** The next neighbourhood of the given kind, which the tests choose. */
  int[] neighbourhood(Kind kind) {
    last = kind;
    bounded = new int[0];
    runs[kind.ordinal()]++;
    totalRuns++;
    int free = 0;
    for (IntVar x : vars) {
      if (!x.singleton()) {
        free++;
      }
    }
    if (kind == Kind.ROUTES || kind == Kind.RELATED) {
      return fixedOutside(routeRelax(kind));
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
          case CONSTRAINTS -> constraintsRelax(relaxed);
          case SCHEDULING -> schedulingRelax(relaxed);
          case SHIFT -> shiftRelax(relaxed);
          case PACKING -> packingRelax(relaxed);
          default -> null;
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
    return switch (k) {
      case OBJECTIVE -> terms.length > 0;
      case CONSTRAINTS -> conVars.length > 0;
      case SCHEDULING -> tasks.length > 1;
      case SHIFT -> SHIFT_ON && tasks.length > 1;
      case PACKING -> packings.length > 0;
      case ROUTES, RELATED -> !routings.isEmpty();
      default -> true;
    };
  }

  /**
   * Returns whether a kind of neighbourhood can be used: it is not turned off and the model has
   * what it needs (a linear objective, constraints, resources or rectangles).
   *
   * @param kind the kind.
   * @return true when {@link #neighbourhood()} may choose it.
   */
  public boolean usable(Kind kind) {
    return enabled(kind);
  }

  /** Relaxes the decision variables that a node stands for; returns how many it relaxed. */
  private int relaxNode(int u, boolean[] relax) {
    int n = 0;
    for (int d : near(u)) {
      if (!relax[d] && !vars[d].singleton()) {
        relax[d] = true;
        n++;
      }
    }
    return n;
  }

  /**
   * The decision variables a node stands for: itself when it is one; otherwise those met first by a
   * breadth-first walk from it over constraints of at most {@link #NEAR_ARITY} variables, or, when
   * that walk meets none, over the other constraints of the graph, at most {@link #MAX_NEAR}.
   */
  private int[] near(int u) {
    if (u < vars.length) {
      return new int[] {u};
    }
    if (near[u] != null) {
      return near[u];
    }
    if (nodes[u].singleton()) {
      // a constant stands for nothing; walking from it would reach unrelated variables
      return new int[0];
    }
    int[] found = nearWalk(u, NEAR_ARITY);
    if (found.length == 0) {
      found = nearWalk(u, Integer.MAX_VALUE);
    }
    near[u] = found;
    return found;
  }

  private int[] nearWalk(int u, int arity) {
    stamp++;
    List<Integer> found = new ArrayList<>();
    List<Integer> level = new ArrayList<>();
    level.add(u);
    seenVar[u] = stamp;
    while (!level.isEmpty() && found.isEmpty()) {
      List<Integer> next = new ArrayList<>();
      for (int v : level) {
        for (int c : varCons[v]) {
          if (seenCon[c] == stamp || conVars[c].length > arity) {
            continue;
          }
          seenCon[c] = stamp;
          for (int w : conVars[c]) {
            if (seenVar[w] != stamp) {
              seenVar[w] = stamp;
              if (w < vars.length) {
                found.add(w);
              } else {
                next.add(w);
              }
            }
          }
        }
      }
      level = next;
    }
    if (found.size() > MAX_NEAR) {
      // a deterministic choice of the nearest ones, spread over the list
      List<Integer> some = new ArrayList<>(MAX_NEAR);
      for (int k = 0; k < MAX_NEAR; k++) {
        some.add(found.get(k * found.size() / MAX_NEAR));
      }
      found = some;
    }
    return found.stream().mapToInt(Integer::intValue).toArray();
  }

  /** Relaxes all the variables of constraints chosen at random until enough are relaxed. */
  private boolean[] constraintsRelax(int relaxed) {
    boolean[] relax = new boolean[vars.length];
    int count = 0;
    int[] order = shuffled(conVars.length);
    for (int k = 0; k < order.length && count < relaxed; k++) {
      for (int u : conVars[order[k]]) {
        count += relaxNode(u, relax);
      }
    }
    return relax;
  }

  /**
   * Relaxes the tasks that start in a window of time of the best solution: the tasks in the order
   * of their starts from one chosen at random, and then those before it, until enough decision
   * variables are relaxed. Tasks on any resource count, so that work can move between resources.
   */
  private boolean[] schedulingRelax(int relaxed) {
    boolean[] relax = new boolean[vars.length];
    Integer[] order = new Integer[tasks.length];
    for (int t = 0; t < tasks.length; t++) {
      order[t] = t;
    }
    Arrays.sort(order, (a, b) -> Integer.compare(nodeValue[tasks[a][0]], nodeValue[tasks[b][0]]));
    int first = random.nextInt(order.length);
    int count = 0;
    for (int k = first; k < order.length && count < relaxed; k++) {
      count += relaxTask(tasks[order[k]], relax);
    }
    for (int k = first - 1; k >= 0 && count < relaxed; k--) {
      count += relaxTask(tasks[order[k]], relax);
    }
    return relax;
  }

  /**
   * Relaxes the tasks that start from a time chosen at random in the best solution on, in order of
   * start, until enough decision variables are relaxed; the decision variables of the tasks after
   * them (their starts and durations) are bounded by their values from above, so that the schedule
   * after the window can move to the left as a block of the same order or better.
   */
  private boolean[] shiftRelax(int relaxed) {
    boolean[] relax = new boolean[vars.length];
    Integer[] order = new Integer[tasks.length];
    for (int t = 0; t < tasks.length; t++) {
      order[t] = t;
    }
    Arrays.sort(order, (a, b) -> Integer.compare(nodeValue[tasks[a][0]], nodeValue[tasks[b][0]]));
    int first = random.nextInt(order.length);
    int count = 0;
    int k = first;
    for (; k < order.length && count < relaxed; k++) {
      count += relaxTask(tasks[order[k]], relax);
    }
    boolean[] after = new boolean[vars.length];
    int n = 0;
    for (; k < order.length; k++) {
      for (int u : tasks[order[k]]) {
        if (u >= 0 && u < vars.length && !relax[u] && !after[u] && !vars[u].singleton()) {
          after[u] = true;
          n++;
        }
      }
    }
    int[] b = new int[n];
    n = 0;
    for (int i = 0; i < vars.length; i++) {
      if (after[i]) {
        relax[i] = true;
        b[n++] = i;
      }
    }
    bounded = b;
    return relax;
  }

  private int relaxTask(int[] task, boolean[] relax) {
    int n = 0;
    for (int u : task) {
      if (u >= 0) {
        n += relaxNode(u, relax);
        n += relaxCompanions(u, relax);
      }
    }
    return n;
  }

  /**
   * Relaxes the decision variables that share a constraint of at most {@link #COMPANION_ARITY}
   * variables with a node of a task or rectangle: what the schedule ties to it, such as a due time
   * that the objective counts. Without them every cargo run of the structural kinds was exhausted
   * at once: the rows end + c &lt;= reclaim stayed fixed (found by the cargo thread).
   */
  private int relaxCompanions(int u, boolean[] relax) {
    int n = 0;
    for (int c : varCons[u]) {
      if (conVars[c].length > COMPANION_ARITY) {
        continue;
      }
      for (int w : conVars[c]) {
        if (w != u) {
          n += w < vars.length ? relaxNode(w, relax) : 0;
        }
      }
    }
    return n;
  }

  /**
   * Relaxes the rectangles of a non-overlap constraint nearest, in the best solution, to one chosen
   * at random, nearest first, until enough decision variables are relaxed.
   */
  private boolean[] packingRelax(int relaxed) {
    boolean[] relax = new boolean[vars.length];
    int[][] rects = packings[random.nextInt(packings.length)];
    int n = rects.length;
    long[] cx = new long[n];
    long[] cy = new long[n];
    for (int i = 0; i < n; i++) {
      cx[i] = 2L * valueOf(rects[i][0]) + valueOf(rects[i][2]);
      cy[i] = 2L * valueOf(rects[i][1]) + valueOf(rects[i][3]);
    }
    int seed = random.nextInt(n);
    Integer[] order = new Integer[n];
    double[] dist = new double[n];
    for (int i = 0; i < n; i++) {
      order[i] = i;
      // the Chebyshev distance of the centres, so that the region is a square
      dist[i] = Math.max(Math.abs(cx[i] - cx[seed]), Math.abs(cy[i] - cy[seed]));
    }
    Arrays.sort(order, (a, b) -> Double.compare(dist[a], dist[b]));
    int count = 0;
    for (int k = 0; k < n && count < relaxed; k++) {
      count += relaxTask(rects[order[k]], relax);
    }
    return relax;
  }

  /** The value of a node in the best solution, or the constant coded as -1 - value. */
  private int valueOf(int u) {
    return u >= 0 ? nodeValue[u] : -1 - u;
  }

  /** The numbers 0 to n - 1 in random order. */
  private int[] shuffled(int n) {
    int[] order = new int[n];
    for (int i = 0; i < n; i++) {
      order[i] = i;
    }
    for (int i = n - 1; i > 0; i--) {
      int j = random.nextInt(i + 1);
      int t = order[i];
      order[i] = order[j];
      order[j] = t;
    }
    return order;
  }

  /**
   * Removes customers from the routes of one routing structure, its share of the customers; all
   * variables are relaxed when that removes every customer.
   */
  private boolean[] routeRelax(Kind kind) {
    boolean[] relax = new boolean[vars.length];
    RouteStructure r = routings.get(random.nextInt(routings.size()));
    double s = share[kind.ordinal()];
    boolean[] removed =
        kind == Kind.ROUTES ? r.routeRemoval(s, random) : r.relatedRemoval(s, random);
    int count = 0;
    for (boolean b : removed) {
      if (b) {
        count++;
      }
    }
    if (count >= r.customerCount()) {
      Arrays.fill(relax, true);
      return relax;
    }
    if (r instanceof SuccessorRoutes successors) {
      // the other variables follow from the successors; the circuits over the same nodes (the
      // predecessors, the tours of other scenarios) lose the same customers
      for (int i = 0; i < vars.length; i++) {
        relax[i] = !successorVar[i];
      }
      for (RouteStructure other : routings) {
        if (other instanceof SuccessorRoutes tour) {
          if (tour.size() == successors.size()) {
            tour.relax(removed, relax);
          } else {
            for (IntVar x : tour.successors()) {
              Integer node = nodeOf.get(x);
              if (node != null && node < vars.length) {
                relax[node] = true;
              }
            }
          }
        }
      }
      return relax;
    }
    r.relax(removed, relax);
    return relax;
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
   * solution above its cheapest value at the root; -1 when no term costs anything. Measured from
   * the cheapest value, a request left unmet in a maximised sum costs its weight, which it would
   * not from 0 (team-assignment).
   */
  private int costlyTerm() {
    double total = 0;
    for (int k = 0; k < terms.length; k++) {
      total += excess(k);
    }
    if (total <= 0) {
      return terms.length == 0 ? -1 : terms[random.nextInt(terms.length)];
    }
    double r = random.nextDouble() * total;
    for (int k = 0; k < terms.length; k++) {
      r -= excess(k);
      if (r < 0) {
        return terms[k];
      }
    }
    return terms[terms.length - 1];
  }

  /** What term k costs in the best solution above its cheapest value at the root. */
  private double excess(int k) {
    double w = termWeights[k];
    return Math.max(0, w * termValues[k] - Math.min(w * termMin[k], w * termMax[k]));
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
    nodeOf = new IdentityHashMap<>();
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
    List<int[]> taskList = new ArrayList<>();
    Map<Var, Boolean> taskStarts = new IdentityHashMap<>();
    List<int[][]> packingList = new ArrayList<>();
    for (IntVar x : nodes) {
      for (Constraint c : x.constraintsWithWatches()) {
        if (conOf.containsKey(c)) {
          continue;
        }
        conOf.put(c, -1);
        readStructure(c, nodeOf, taskList, taskStarts);
        if (c instanceof Nooverlap packing) {
          readPacking(packing, nodeOf, packingList);
        }
        if (c instanceof Routes r) {
          imposedRoutes.add(r);
        } else if (c instanceof Circuit || c instanceof Subcircuit) {
          imposedCircuits.add(c);
        }
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
    tasks = taskList.toArray(new int[0][]);
    packings = packingList.toArray(new int[0][][]);
    nodeValue = new int[nodes.length];
    near = new int[nodes.length][];
    java.util.BitSet w = new java.util.BitSet(nodes.length);
    for (int[] t : tasks) {
      w.set(t[0]);
    }
    for (int[][] p : packings) {
      for (int[] r : p) {
        for (int u : r) {
          if (u >= 0) {
            w.set(u);
          }
        }
      }
    }
    watched = w.stream().toArray();
    varCons = new int[nodes.length][];
    for (int i = 0; i < nodes.length; i++) {
      varCons[i] = adjacency.get(i).stream().mapToInt(Integer::intValue).toArray();
    }
    seenVar = new int[nodes.length];
    seenCon = new int[conVars.length];
  }

  /**
   * Records the tasks of a cumulative or unary resource (each start once, as nodes of its start,
   * duration and resource use, -1 for a constant).
   */
  private static void readStructure(
      Constraint c, Map<Var, Integer> nodeOf, List<int[]> taskList, Map<Var, Boolean> taskStarts) {
    if (c instanceof CumulativeBasic resource) {
      IntVar[][] t = resource.tasks();
      for (int i = 0; i < t[0].length; i++) {
        Integer start = nodeOf.get(t[0][i]);
        if (start == null || t[0][i].singleton() || taskStarts.put(t[0][i], true) != null) {
          continue;
        }
        taskList.add(new int[] {start, nodeOrNone(nodeOf, t[1][i]), nodeOrNone(nodeOf, t[2][i])});
      }
    }
  }

  /**
   * Records the rectangles of a non-overlap constraint as nodes, a constant as -1 - its value; a
   * constraint with a variable that is neither is left out.
   */
  private static void readPacking(
      Nooverlap c, Map<Var, Integer> nodeOf, List<int[][]> packingList) {
    IntVar[][] r = c.rectangles();
    int[][] rects = new int[r.length][4];
    for (int i = 0; i < r.length; i++) {
      for (int j = 0; j < 4; j++) {
        Integer node = r[i][j].singleton() ? null : nodeOf.get(r[i][j]);
        if (node != null) {
          rects[i][j] = node;
        } else if (r[i][j].singleton() && r[i][j].value() >= 0) {
          rects[i][j] = -1 - r[i][j].value();
        } else {
          return;
        }
      }
    }
    if (rects.length > 1) {
      packingList.add(rects);
    }
  }

  private static int nodeOrNone(Map<Var, Integer> nodeOf, IntVar x) {
    Integer node = x.singleton() ? null : nodeOf.get(x);
    return node == null ? -1 : node;
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
    termMin = new int[terms.length];
    termMax = new int[terms.length];
    for (int k = 0; k < terms.length; k++) {
      termMin[k] = nodes[terms[k]].min();
      termMax[k] = nodes[terms[k]].max();
    }
  }
}
