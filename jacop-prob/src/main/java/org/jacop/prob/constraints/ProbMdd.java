/*
 * ProbMdd.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.prob.constraints;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * The probability that a layered decision diagram reaches its true sink: {@code p = floor(scale *
 * Pr(T))}. Each level of the diagram is a decision level, whose edges are labelled by values of one
 * decision variable, or a chance level, whose edges carry probability numerators over the level's
 * denominator (the outcomes of an independent random variable). Fixing the decisions leaves a
 * Markov chain from the root, and Pr(T) is the probability that it ends in the true sink; an edge
 * that is missing leads to the false sink. It is the compiled form of a probabilistic logic program
 * or of a stochastic constraint problem (Babaki, Guns and De Raedt, "Stochastic constraint
 * optimization using propagation on ordered binary decision diagrams", StarAI 2017; Latour et al.,
 * "Combining stochastic constraint optimization and probabilistic programming", CP 2017), the
 * probabilistic twin of a cost MDD.
 *
 * <p>Propagation is two passes over the diagram in the (+, max) semiring: up(n) is the largest
 * probability of reaching T from node n, the maximum over the values left at a decision level and
 * the weighted sum at a chance level, and down(n) bounds the probability of reaching n. A value v
 * of a decision variable is removed when the mass through its edges, the sum of down(n) * up(child)
 * over them, is below the lower bound of p, and p is bounded by up(root) and by the same pass with
 * minima at decision levels. A maximum below a chance level lets a decision see the outcome above
 * it, so the bounds are relaxations, sound but not complete unless the decision levels come first;
 * when every decision is fixed, Pr(T) is computed exactly on big integers and fixes p. The passes
 * use doubles rounded outward. Each decision variable labels at most one level.
 *
 * <p>Lazy clause generation gets the removed labels of the other decision levels and the bound of p
 * that the pruning needed; a lower bound of p, or a value fixed when all decisions are, gets the
 * domains of the decision variables.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ProbMdd extends Constraint
    implements SatisfiedPresent, Copyable<ProbMdd>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The decision variables. */
  final IntVar[] x;

  /** The scaled probability of reaching the true sink. */
  final IntVar p;

  /** The scale of p, at least 1. */
  final long scale;

  // the diagram as given, for copies
  private final int[] levelVar;
  private final int[] levelDen;
  private final int[] levelSize;
  private final int[] nodeEdges;
  private final int[] edgeLabel;
  private final int[] edgeTarget;

  // level l: its nodes levelStart[l]..levelStart[l + 1] - 1; node n: its edges
  // edgeStart[n]..edgeStart[n + 1] - 1, each to the node target[e], or -1 for the true sink
  private final int levels;
  private final int[] levelStart;
  private final int[] edgeStart;
  private final int[] target;
  private final int[] source;
  // the level of each decision variable, or -1
  private final int[] levelOf;
  // level l: its edges grouped by label (decision levels only)
  private final int[][] byLabel;
  // a chance edge: its probability rounded down and up
  private final double[] probLo;
  private final double[] probHi;

  // scratch of the passes
  private final double[] upHi;
  private final double[] lowLo;
  private final double[] downHi;
  private final double[] acc;
  private final boolean[] edgeIn;
  private final boolean[] full;

  /**
   * It constructs the constraint.
   *
   * @param x the decision variables
   * @param levelVar for each level, the index into x of its decision variable, or -1 for a chance
   *     level
   * @param levelDen for each level, the denominator of its probabilities (any value for a decision
   *     level)
   * @param levelSize for each level, its number of nodes; the first level has one, the root
   * @param nodeEdges for each node, level by level, its number of edges
   * @param edgeLabel for each edge, node by node, its value (decision level) or probability
   *     numerator (chance level); the labels of a node's decision edges differ
   * @param edgeTarget for each edge, the index of its node in the next level, or -1 for the true
   *     sink, which only the edges of the last level reach
   * @param scale the scale of p, at least 1 and at most Integer.MAX_VALUE
   * @param p floor(scale * Pr(T))
   */
  public ProbMdd(
      IntVar[] x,
      int[] levelVar,
      int[] levelDen,
      int[] levelSize,
      int[] nodeEdges,
      int[] edgeLabel,
      int[] edgeTarget,
      long scale,
      IntVar p) {
    this.x = x.clone();
    this.p = p;
    this.scale = scale;
    this.levelVar = levelVar.clone();
    this.levelDen = levelDen.clone();
    this.levelSize = levelSize.clone();
    this.nodeEdges = nodeEdges.clone();
    this.edgeLabel = edgeLabel.clone();
    this.edgeTarget = edgeTarget.clone();
    levels = levelVar.length;
    if (levelDen.length != levels || levelSize.length != levels || levels == 0) {
      throw new IllegalArgumentException("ProbMdd: levels of different lengths, or none");
    }
    if (levelSize[0] != 1) {
      throw new IllegalArgumentException("ProbMdd: the first level must have one node");
    }
    if (scale < 1 || scale > Integer.MAX_VALUE) {
      throw new IllegalArgumentException("ProbMdd: scale out of range");
    }
    for (IntVar v : x) {
      if (v == p) {
        throw new IllegalArgumentException("ProbMdd: p must not be a decision variable");
      }
    }
    levelStart = new int[levels + 1];
    for (int l = 0; l < levels; l++) {
      if (levelSize[l] < 1) {
        throw new IllegalArgumentException("ProbMdd: level " + l + " has no node");
      }
      levelStart[l + 1] = levelStart[l] + levelSize[l];
    }
    int nodes = levelStart[levels];
    if (nodeEdges.length != nodes) {
      throw new IllegalArgumentException("ProbMdd: nodeEdges needs one count per node");
    }
    edgeStart = new int[nodes + 1];
    for (int n = 0; n < nodes; n++) {
      if (nodeEdges[n] < 0) {
        throw new IllegalArgumentException("ProbMdd: negative edge count");
      }
      edgeStart[n + 1] = edgeStart[n] + nodeEdges[n];
    }
    int edges = edgeStart[nodes];
    if (edgeLabel.length != edges || edgeTarget.length != edges) {
      throw new IllegalArgumentException(
          "ProbMdd: edgeLabel and edgeTarget need one entry per edge");
    }
    levelOf = new int[x.length];
    Arrays.fill(levelOf, -1);
    target = new int[edges];
    source = new int[edges];
    probLo = new double[edges];
    probHi = new double[edges];
    byLabel = new int[levels][];
    for (int l = 0; l < levels; l++) {
      checkLevel(l);
    }
    upHi = new double[nodes];
    lowLo = new double[nodes];
    downHi = new double[nodes];
    acc = new double[nodes];
    edgeIn = new boolean[edges];
    full = new boolean[nodes];

    numberId = idNumber.incrementAndGet();
    queueIndex = 2;
    setScope(Stream.concat(Arrays.stream(this.x), Stream.of(p)));
  }

  private void checkLevel(int l) {
    boolean last = l == levels - 1;
    int v = levelVar[l];
    if (v >= x.length || v < -1) {
      throw new IllegalArgumentException("ProbMdd: level " + l + " has no variable " + v);
    }
    if (v >= 0) {
      if (levelOf[v] >= 0) {
        throw new IllegalArgumentException("ProbMdd: variable " + v + " labels two levels");
      }
      levelOf[v] = l;
    } else if (levelDen[l] <= 0) {
      throw new IllegalArgumentException("ProbMdd: chance level " + l + " needs a denominator");
    }
    for (int n = levelStart[l]; n < levelStart[l + 1]; n++) {
      long sum = 0;
      for (int e = edgeStart[n]; e < edgeStart[n + 1]; e++) {
        int t = edgeTarget[e];
        if (last ? t != -1 : t < 0 || t >= levelSize[l + 1]) {
          throw new IllegalArgumentException("ProbMdd: edge " + e + " has a wrong target " + t);
        }
        target[e] = last ? -1 : levelStart[l + 1] + t;
        source[e] = n;
        if (v >= 0) {
          for (int f = edgeStart[n]; f < e; f++) {
            if (edgeLabel[f] == edgeLabel[e]) {
              throw new IllegalArgumentException("ProbMdd: node " + n + " repeats a label");
            }
          }
        } else {
          if (edgeLabel[e] < 0) {
            throw new IllegalArgumentException("ProbMdd: negative probability");
          }
          sum += edgeLabel[e];
          probLo[e] = LoadDistribution.down((double) edgeLabel[e] / levelDen[l]);
          probHi[e] = Math.min(1, LoadDistribution.up((double) edgeLabel[e] / levelDen[l]));
        }
      }
      if (sum > levelDen[l]) {
        throw new IllegalArgumentException("ProbMdd: the probabilities of node " + n + " pass 1");
      }
    }
    if (v >= 0) {
      byLabel[l] =
          IntStream.range(edgeStart[levelStart[l]], edgeStart[levelStart[l + 1]])
              .boxed()
              .sorted((a, b) -> Integer.compare(edgeLabel[a], edgeLabel[b]))
              .mapToInt(Integer::intValue)
              .toArray();
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getConsistencyPruningEvent(Var var) {
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(var);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    return var == p ? IntDomain.BOUND : IntDomain.ANY;
  }

  // ---------------------------------------------------------------------------------------------
  // the passes over a state: which decision edges are in the domains, and which decision nodes
  // have an edge for every value of the domain (none leads to the false sink)

  private void readDomains() {
    for (int l = 0; l < levels; l++) {
      int v = levelVar[l];
      if (v < 0) {
        continue;
      }
      IntDomain d = x[v].dom();
      int size = d.getSize();
      for (int n = levelStart[l]; n < levelStart[l + 1]; n++) {
        int count = 0;
        for (int e = edgeStart[n]; e < edgeStart[n + 1]; e++) {
          edgeIn[e] = d.contains(edgeLabel[e]);
          if (edgeIn[e]) {
            count++;
          }
        }
        full[n] = count == size;
      }
    }
  }

  private void readTrail(AtomicTrail trail, int pos) {
    EntryList scratch = new EntryList();
    for (int l = 0; l < levels; l++) {
      int v = levelVar[l];
      if (v < 0) {
        continue;
      }
      int size = 0;
      for (ValueEnumeration en = trail.rootDomain(x[v]).valueEnumeration();
          en.hasMoreElements(); ) {
        scratch.clear();
        if (!trail.excludedBefore(x[v], en.nextElement(), pos, scratch)) {
          size++;
        }
      }
      for (int n = levelStart[l]; n < levelStart[l + 1]; n++) {
        int count = 0;
        for (int e = edgeStart[n]; e < edgeStart[n + 1]; e++) {
          scratch.clear();
          edgeIn[e] = !trail.excludedBefore(x[v], edgeLabel[e], pos, scratch);
          if (edgeIn[e]) {
            count++;
          }
        }
        full[n] = count == size;
      }
    }
  }

  // up (largest) and low (smallest) probabilities of reaching T from each node
  private void upPass() {
    for (int l = levels - 1; l >= 0; l--) {
      boolean decision = levelVar[l] >= 0;
      for (int n = levelStart[l]; n < levelStart[l + 1]; n++) {
        double hi = 0;
        double lo = decision && edgeStart[n + 1] > edgeStart[n] ? 1 : 0;
        for (int e = edgeStart[n]; e < edgeStart[n + 1]; e++) {
          double childHi = target[e] < 0 ? 1 : upHi[target[e]];
          double childLo = target[e] < 0 ? 1 : lowLo[target[e]];
          if (decision) {
            if (edgeIn[e]) {
              hi = Math.max(hi, childHi);
              lo = Math.min(lo, childLo);
            }
          } else {
            hi = LoadDistribution.up(hi + LoadDistribution.up(probHi[e] * childHi));
            lo = LoadDistribution.down(lo + LoadDistribution.down(probLo[e] * childLo));
          }
        }
        if (decision && !full[n]) {
          lo = 0;
        }
        upHi[n] = Math.min(1, hi);
        lowLo[n] = Math.max(0, lo);
      }
    }
  }

  // an upper bound of the probability of reaching each node under any decisions in the domains
  private void downPass() {
    Arrays.fill(downHi, 0);
    downHi[0] = 1;
    for (int l = 0; l < levels - 1; l++) {
      if (levelVar[l] < 0) {
        for (int n = levelStart[l]; n < levelStart[l + 1]; n++) {
          for (int e = edgeStart[n]; e < edgeStart[n + 1]; e++) {
            int m = target[e];
            downHi[m] = LoadDistribution.up(downHi[m] + LoadDistribution.up(downHi[n] * probHi[e]));
          }
        }
        continue;
      }
      // the decision takes one value: the largest mass into a child over the values
      int[] group = byLabel[l];
      int from = 0;
      while (from < group.length) {
        int to = from;
        while (to < group.length && edgeLabel[group[to]] == edgeLabel[group[from]]) {
          to++;
        }
        if (edgeIn[group[from]]) {
          for (int k = from; k < to; k++) {
            int m = target[group[k]];
            acc[m] = LoadDistribution.up(acc[m] + downHi[source[group[k]]]);
          }
          for (int k = from; k < to; k++) {
            int m = target[group[k]];
            downHi[m] = Math.min(1, Math.max(downHi[m], acc[m]));
          }
          for (int k = from; k < to; k++) {
            acc[target[group[k]]] = 0;
          }
        }
        from = to;
      }
    }
  }

  // an upper bound of Pr(T) with the decision of level l taking the label of edges[from..to)
  private double massThrough(int[] group, int from, int to) {
    double sum = 0;
    for (int k = from; k < to; k++) {
      int e = group[k];
      double child = target[e] < 0 ? 1 : upHi[target[e]];
      sum = LoadDistribution.up(sum + LoadDistribution.up(downHi[source[e]] * child));
    }
    return sum;
  }

  // floor(scale * d) rounded up as the bound of a scaled probability of at most d
  private long scaledHi(double d) {
    return Math.min(scale, (long) Math.floor(LoadDistribution.up(scale * d)));
  }

  private long scaledLo(double d) {
    return Math.max(0, (long) Math.floor(LoadDistribution.down(scale * d)));
  }

  private boolean allGround() {
    for (int l = 0; l < levels; l++) {
      if (levelVar[l] >= 0 && !x[levelVar[l]].singleton()) {
        return false;
      }
    }
    return true;
  }

  /**
   * Returns floor(scale * Pr(T)) for the given decisions, exactly.
   *
   * @param values the value of each decision variable (those of no level are ignored)
   * @return the scaled probability
   */
  long exact(int[] values) {
    BigInteger[] num = new BigInteger[levelStart[levels]];
    BigInteger[] childDen = new BigInteger[levels + 1];
    childDen[levels] = BigInteger.ONE;
    for (int l = levels - 1; l >= 0; l--) {
      childDen[l] =
          levelVar[l] >= 0
              ? childDen[l + 1]
              : childDen[l + 1].multiply(BigInteger.valueOf(levelDen[l]));
    }
    for (int l = levels - 1; l >= 0; l--) {
      int v = levelVar[l];
      for (int n = levelStart[l]; n < levelStart[l + 1]; n++) {
        BigInteger sum = BigInteger.ZERO;
        for (int e = edgeStart[n]; e < edgeStart[n + 1]; e++) {
          BigInteger child = target[e] < 0 ? BigInteger.ONE : num[target[e]];
          if (v >= 0) {
            if (edgeLabel[e] == values[v]) {
              sum = child;
            }
          } else {
            sum = sum.add(child.multiply(BigInteger.valueOf(edgeLabel[e])));
          }
        }
        num[n] = sum;
      }
    }
    return num[0].multiply(BigInteger.valueOf(scale)).divide(childDen[0]).longValueExact();
  }

  private int[] groundValues() {
    int[] values = new int[x.length];
    for (int i = 0; i < x.length; i++) {
      if (levelOf[i] >= 0) {
        values[i] = x[i].value();
      }
    }
    return values;
  }

  @Override
  public void consistency(Store store) {
    boolean changed = true;
    while (changed) {
      changed = false;
      if (allGround()) {
        long v = exact(groundValues());
        p.domain.in(store.level, p, (int) v, (int) v);
        return;
      }
      readDomains();
      upPass();
      downPass();
      p.domain.in(store.level, p, (int) scaledLo(lowLo[0]), (int) scaledHi(upHi[0]));
      long limit = p.min();
      for (int l = 0; l < levels && limit > 0; l++) {
        if (levelVar[l] >= 0) {
          changed |= pruneLevel(store, l, limit);
        }
      }
    }
  }

  // removes the values of level l's variable whose mass is below limit; true when one is removed
  private boolean pruneLevel(Store store, int l, long limit) {
    IntVar var = x[levelVar[l]];
    int[] group = byLabel[l];
    boolean changed = false;
    // a value with no edge at all leads to the false sink
    for (ValueEnumeration en = var.dom().valueEnumeration(); en.hasMoreElements(); ) {
      int v = en.nextElement();
      int from = firstOf(group, v);
      double mass = from < 0 ? 0 : massThrough(group, from, endOf(group, from));
      if (scaledHi(mass) < limit) {
        var.domain.inComplement(store.level, var, v);
        changed = true;
      }
    }
    return changed;
  }

  private int firstOf(int[] group, int v) {
    int lo = 0;
    int hi = group.length;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (edgeLabel[group[mid]] < v) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return lo < group.length && edgeLabel[group[lo]] == v ? lo : -1;
  }

  private int endOf(int[] group, int from) {
    int to = from;
    while (to < group.length && edgeLabel[group[to]] == edgeLabel[group[from]]) {
      to++;
    }
    return to;
  }

  @Override
  public boolean satisfied() {
    return p.singleton() && allGround() && exact(groundValues()) == p.value();
  }

  // ---------------------------------------------------------------------------------------------
  // explanations

  // the removed labels of the decision levels other than skip
  private void removedLabels(AtomicTrail trail, int pos, int skip, EntryList out) {
    for (int l = 0; l < levels; l++) {
      int v = levelVar[l];
      if (v < 0 || l == skip) {
        continue;
      }
      for (int e = edgeStart[levelStart[l]]; e < edgeStart[levelStart[l + 1]]; e++) {
        if (!edgeIn[e]) {
          trail.excludedBefore(x[v], edgeLabel[e], pos, out);
        }
      }
    }
  }

  private void allDomains(AtomicTrail trail, int pos, EntryList out) {
    for (int l = 0; l < levels; l++) {
      if (levelVar[l] >= 0) {
        trail.atomsBefore(x[levelVar[l]], pos, out);
      }
    }
  }

  private boolean groundAt(AtomicTrail trail, int pos, int[] values) {
    for (int l = 0; l < levels; l++) {
      int v = levelVar[l];
      if (v >= 0) {
        int lo = trail.minBefore(x[v], pos);
        if (lo != trail.maxBefore(x[v], pos)) {
          return false;
        }
        values[v] = lo;
      }
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int mark = out.size();
    readTrail(trail, entry);
    upPass();
    downPass();
    IntVar var = trail.variable(entry);
    boolean ok = var == p ? explainBound(trail, entry, out) : explainValues(trail, entry, var, out);
    if (!ok) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  private boolean explainBound(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return false;
    }
    int bound = trail.skippedBound(entry);
    boolean ge = kind == AtomicTrail.GE;
    if (ge ? scaledLo(lowLo[0]) >= bound : scaledHi(upHi[0]) <= bound) {
      if (ge) {
        allDomains(trail, entry, out);
      } else {
        removedLabels(trail, entry, -1, out);
      }
    } else {
      int[] values = new int[x.length];
      if (!groundAt(trail, entry, values)) {
        return false;
      }
      long v = exact(values);
      if (ge ? v < bound : v > bound) {
        return false;
      }
      allDomains(trail, entry, out);
    }
    if (bound != trail.value(entry)) {
      trail.addSkippedHoles(entry, bound, out);
    }
    return true;
  }

  private boolean explainValues(AtomicTrail trail, int entry, IntVar var, EntryList out) {
    int i = -1;
    for (int k = 0; k < x.length && i < 0; k++) {
      if (x[k] == var && levelOf[k] >= 0) {
        i = k;
      }
    }
    if (i < 0) {
      return false;
    }
    int kind = trail.kind(entry);
    long lo;
    long hi;
    if (kind == AtomicTrail.NE) {
      lo = trail.value(entry);
      hi = lo;
    } else if (kind == AtomicTrail.GE) {
      lo = trail.minBefore(var, entry);
      hi = trail.value(entry) - 1L;
      trail.addLowerBound(var, entry, out);
    } else {
      lo = trail.value(entry) + 1L;
      hi = trail.maxBefore(var, entry);
      trail.addUpperBound(var, entry, out);
    }
    int l = levelOf[i];
    int[] group = byLabel[l];
    long need = Long.MIN_VALUE;
    for (long u = lo; u <= hi; u++) {
      if (trail.excludedBefore(var, (int) u, entry, out)) {
        continue;
      }
      int from = firstOf(group, (int) u);
      double mass = from < 0 ? 0 : massThrough(group, from, endOf(group, from));
      need = Math.max(need, scaledHi(mass) + 1);
    }
    if (need > trail.minBefore(p, entry)) {
      // the values were removed when all decisions were fixed
      return false;
    }
    removedLabels(trail, entry, l, out);
    if (need > Long.MIN_VALUE) {
      trail.addBoundReaching(p, entry, true, need, out);
    }
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int mark = out.size();
    int pos = trail.size();
    allDomains(trail, pos, out);
    trail.atomsBefore(p, pos, out);
    out.sortUnique(mark);
    return true;
  }

  @Override
  public ProbMdd copy(VarMap map) {
    return new ProbMdd(
        map.get(x),
        levelVar,
        levelDen,
        levelSize,
        nodeEdges,
        edgeLabel,
        edgeTarget,
        scale,
        map.get(p));
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder();
    result.append(id()).append(" : ProbMdd([");
    for (int i = 0; i < x.length; i++) {
      result.append(i == 0 ? "" : ", ").append(x[i]);
    }
    result.append("], ").append(levels).append(" levels, ").append(levelStart[levels]);
    result.append(" nodes, scale ").append(scale).append(", ").append(p).append(")");
    return result.toString();
  }
}
