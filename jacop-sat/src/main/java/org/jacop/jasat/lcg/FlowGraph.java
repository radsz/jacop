/*
 * FlowGraph.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in material form as in https://www.gnu.org/licenses/agpl-3.0.en.html#section7.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import java.util.Arrays;

/**
 * Experimental: a bounded graph of how often integer variables meet in conflict analysis. Each
 * variable keeps its {@code k} strongest neighbours in two flat arrays; a new neighbour of a full
 * list replaces the weakest one and takes over its weight (Space-Saving, Metwally, Agrawal and El
 * Abbadi, ICDT 2005), so weights are overestimates by at most the replaced weight and memory is
 * {@code n * k}. Weights decay as activity does: by a growing increment, rescaled rarely.
 *
 * <p>Labels: label propagation (Raghavan, Albert and Kumara, Phys. Rev. E 2007) over the lists, for
 * a fixed number of sweeps, gives clusters of variables that meet in conflicts.
 */
final class FlowGraph {

  private final int k;
  private int n;
  private int[] nbr; // n * k, -1 when empty
  private double[] w;
  private double inc = 1;
  private final double decay;
  int[] label = new int[0];

  FlowGraph(int k, double decay) {
    this.k = k;
    this.decay = decay;
    nbr = new int[0];
    w = new double[0];
  }

  void grow(int size) {
    if (size <= n) {
      return;
    }
    nbr = Arrays.copyOf(nbr, size * k);
    Arrays.fill(nbr, n * k, size * k, -1);
    w = Arrays.copyOf(w, size * k);
    label = Arrays.copyOf(label, size);
    for (int i = n; i < size; i++) {
      label[i] = i;
    }
    n = size;
  }

  /** Adds the pairs of the first {@code size} variables of {@code vs}, then decays. */
  void addConflict(int[] vs, int size) {
    for (int i = 0; i < size; i++) {
      for (int j = i + 1; j < size; j++) {
        add(vs[i], vs[j]);
        add(vs[j], vs[i]);
      }
    }
    inc /= decay;
    if (inc > 1e100) {
      for (int i = 0; i < w.length; i++) {
        w[i] *= 1e-100;
      }
      inc *= 1e-100;
    }
  }

  private void add(int a, int b) {
    if (a >= n || b >= n) {
      return;
    }
    int base = a * k;
    int weakest = base;
    for (int s = base; s < base + k; s++) {
      if (nbr[s] == b) {
        w[s] += inc;
        return;
      }
      if (nbr[s] < 0) {
        nbr[s] = b;
        w[s] = inc;
        return;
      }
      if (w[s] < w[weakest]) {
        weakest = s;
      }
    }
    nbr[weakest] = b;
    w[weakest] += inc;
  }

  /** Neighbour i of variable a, or -1. */
  int neighbour(int a, int i) {
    return a < n ? nbr[a * k + i] : -1;
  }

  /** Weight of neighbour i of variable a. */
  double weight(int a, int i) {
    return w[a * k + i];
  }

  int k() {
    return k;
  }

  /**
   * Modularity of {@link #label} on the graph's own (symmetrised) weights: the share of weight
   * inside clusters minus the share expected from the clusters' total degrees (Newman and Girvan
   * 2004).
   */
  double modularity() {
    double total = 0;
    double inside = 0;
    double[] degree = new double[n];
    for (int a = 0; a < n; a++) {
      for (int i = 0; i < k; i++) {
        int b = nbr[a * k + i];
        if (b < 0) {
          continue;
        }
        double x = w[a * k + i];
        total += x;
        degree[label[a]] += x;
        if (label[a] == label[b]) {
          inside += x;
        }
      }
    }
    if (total <= 0) {
      return 0;
    }
    double expected = 0;
    for (int c = 0; c < n; c++) {
      expected += (degree[c] / total) * (degree[c] / total);
    }
    return inside / total - expected;
  }

  /** Recomputes {@link #label} by {@code sweeps} rounds of weighted label propagation. */
  void propagateLabels(int sweeps) {
    for (int i = 0; i < n; i++) {
      label[i] = i;
    }
    int[] cand = new int[k];
    double[] score = new double[k];
    for (int s = 0; s < sweeps; s++) {
      boolean changed = false;
      for (int a = 0; a < n; a++) {
        int m = 0;
        for (int i = 0; i < k; i++) {
          int b = nbr[a * k + i];
          if (b < 0) {
            continue;
          }
          int l = label[b];
          int j = 0;
          while (j < m && cand[j] != l) {
            j++;
          }
          if (j == m) {
            cand[m] = l;
            score[m++] = 0;
          }
          score[j] += w[a * k + i];
        }
        if (m == 0) {
          continue;
        }
        int best = 0;
        for (int j = 1; j < m; j++) {
          if (score[j] > score[best] || (score[j] == score[best] && cand[j] < cand[best])) {
            best = j;
          }
        }
        if (label[a] != cand[best]) {
          label[a] = cand[best];
          changed = true;
        }
      }
      if (!changed) {
        break;
      }
    }
  }
}
