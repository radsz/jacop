/*
 * SplitSums.java
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
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;

/**
 * The linear constraints that lazy clause generation split into blocks (the block sums of {@code
 * LinearSplit}), or that the flattening wrote over a named sum, read back as the rows they were. A
 * block sum s is in its block, an equality with s at weight 1 or -1, in the constraint that sums
 * the blocks, and in the orderings of block sums that symmetry breaking may add. The block is the
 * definition of s; s is replaced by it in the other constraints, and the block is left out. The row
 * "at least 24 of 169" of the peaceable armies of queens (army13 of the Pseudo-Boolean Competition
 * 2016) is 13 blocks of 13 terms and the sum of the 13 block sums.
 */
final class SplitSums {

  // the blocks, which the rows read back stand for
  final Set<Constraint> definitions = Collections.newSetFromMap(new IdentityHashMap<>());
  // the constraints that sum blocks, as the rows over the terms of their blocks
  final Map<Constraint, LinearForm> rows = new IdentityHashMap<>();
  // the domain of the sum of each block left out, as rows over the terms of the block (none when a
  // row overflows, which leaves the model to lazy clause generation)
  final Map<Constraint, List<LinearForm>> bounds = new IdentityHashMap<>();

  private SplitSums() {}

  /**
   * Reads back the rows of a store whose sums were split or named. An integer variable not within
   * 0..1 is a sum when the only linear equality over it at weight 1 or -1 has 0/1 variables or
   * other sums otherwise (its definition; sums of sums are a tree); each other linear constraint
   * over sums is read back with them replaced by their definitions. A definition is left out when
   * every constraint over its sum is read back or left out and the domain of the sum is an
   * interval: the sum is then no variable of the model, its bounds become two rows over the terms
   * of its definition, and the store computes it from a solution.
   *
   * @param store the store
   * @return the definitions and the rows read back
   */
  static SplitSums of(Store store) {
    List<IntVar> sums = new ArrayList<>();
    for (Var x : store.variablesHashMap.values()) {
      if (x instanceof IntVar v && !v.singleton() && (v.min() < 0 || v.max() > 1)) {
        sums.add(v);
      }
    }
    SplitSums s = new SplitSums();
    Map<IntVar, LinearForm> definition = new IdentityHashMap<>();
    Map<IntVar, Constraint> block = new IdentityHashMap<>();
    Map<IntVar, List<Constraint>> users = new IdentityHashMap<>();
    Map<IntVar, List<Constraint>> over = new IdentityHashMap<>();
    for (IntVar v : sums) {
      over.put(v, constraints(v));
    }
    // bottom up: a sum is defined over 0/1 variables and sums defined before
    Set<Constraint> used = Collections.newSetFromMap(new IdentityHashMap<>());
    for (boolean changed = true; changed; ) {
      changed = false;
      for (IntVar v : sums) {
        List<Constraint> cs = over.get(v);
        int d = definition.containsKey(v) ? -1 : definitionIndex(cs, v, definition, used);
        if (d >= 0) {
          definition.put(v, LinearForms.of(cs.get(d)));
          used.add(cs.get(d));
          List<Constraint> others = new ArrayList<>(cs);
          block.put(v, others.remove(d));
          users.put(v, others);
          changed = true;
        }
      }
    }
    // a definition of a sum of block sums is a block of the level above, not a row
    Set<Constraint> blocks = Collections.newSetFromMap(new IdentityHashMap<>());
    blocks.addAll(block.values());
    for (List<Constraint> cs : users.values()) {
      for (Constraint u : cs) {
        LinearForm g = blocks.contains(u) || s.rows.containsKey(u) ? null : LinearForms.of(u);
        if (g != null) {
          LinearForm f = substituted(g, definition);
          if (f != null) {
            s.rows.put(u, f);
          }
        }
      }
    }
    // a block stands for its sum when each other constraint over the sum is a row read back or a
    // block that stands for its own sum; otherwise the sum stays a variable of the model
    s.definitions.addAll(blocks);
    for (boolean changed = true; changed; ) {
      changed = false;
      for (Map.Entry<IntVar, List<Constraint>> e : users.entrySet()) {
        Constraint b = block.get(e.getKey());
        IntVar v = e.getKey();
        boolean interval = v.dom().getSize() == (long) v.max() - v.min() + 1;
        if (s.definitions.contains(b) && (!interval || !standsFor(e.getValue(), s))) {
          s.definitions.remove(b);
          changed = true;
        }
      }
    }
    // the domain of a sum left out holds as two rows over the terms of its definition: a split row
    // may keep its right-hand side as the bound of its sum
    for (Map.Entry<IntVar, Constraint> e : block.entrySet()) {
      if (s.definitions.contains(e.getValue())) {
        IntVar v = e.getKey();
        LinearForm min =
            substituted(
                new LinearForm(new IntVar[] {v}, new long[] {1}, v.min(), LinearForm.GE),
                definition);
        LinearForm max =
            substituted(
                new LinearForm(new IntVar[] {v}, new long[] {1}, v.max(), LinearForm.LE),
                definition);
        s.bounds.put(e.getValue(), min == null || max == null ? List.of() : List.of(min, max));
      }
    }
    return s;
  }

  private static boolean standsFor(List<Constraint> users, SplitSums s) {
    for (Constraint u : users) {
      if (!s.rows.containsKey(u) && !s.definitions.contains(u)) {
        return false;
      }
    }
    return true;
  }

  // the distinct constraints over v
  private static List<Constraint> constraints(IntVar v) {
    Set<Constraint> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    List<Constraint> out = new ArrayList<>();
    for (Constraint c : v.dom().constraints()) {
      if (seen.add(c)) {
        out.add(c);
      }
    }
    return out;
  }

  // the index of a definition of v among the constraints not used as definitions, or -1: any
  // equality that gives v in the other variables is one (the others are read back as rows), and
  // the one over the fewest sums is taken, so a block goes before the row that sums blocks
  private static int definitionIndex(
      List<Constraint> cs, IntVar v, Map<IntVar, LinearForm> definition, Set<Constraint> used) {
    int found = -1;
    int fewest = Integer.MAX_VALUE;
    for (int i = 0; i < cs.size(); i++) {
      LinearForm f = used.contains(cs.get(i)) ? null : LinearForms.of(cs.get(i));
      int sums = f == null ? -1 : sumsIn(f, v, definition);
      if (sums >= 0 && sums < fewest) {
        found = i;
        fewest = sums;
      }
    }
    return found;
  }

  // the defined sums of an equality with v at weight 1 or -1 and 0/1 variables or defined sums
  // otherwise, or -1 when f is no such equality
  private static int sumsIn(LinearForm f, IntVar v, Map<IntVar, LinearForm> definition) {
    if (f.relation() != LinearForm.EQ) {
      return -1;
    }
    boolean found = false;
    int sums = 0;
    for (int i = 0; i < f.vars().length; i++) {
      IntVar x = f.vars()[i];
      if (x == v) {
        found |= Math.abs(f.weights()[i]) == 1;
      } else if (definition.containsKey(x)) {
        sums++;
      } else if (!x.singleton() && (x.min() < 0 || x.max() > 1)) {
        return -1;
      }
    }
    return found ? sums : -1;
  }

  // f with each variable that has a definition replaced by it, down to the variables that have
  // none, or null when the weights overflow or the definitions nest deeper than MAX_DEPTH
  private static LinearForm substituted(LinearForm f, Map<IntVar, LinearForm> definition) {
    Map<IntVar, Long> terms = new LinkedHashMap<>();
    long[] c = {f.c()};
    try {
      for (int i = 0; i < f.vars().length; i++) {
        if (!expand(f.vars()[i], f.weights()[i], definition, terms, c, 0)) {
          return null;
        }
      }
    } catch (ArithmeticException e) {
      return null;
    }
    terms.values().removeIf(w -> w == 0);
    IntVar[] vars = terms.keySet().toArray(new IntVar[0]);
    long[] weights = new long[vars.length];
    for (int i = 0; i < vars.length; i++) {
      weights[i] = terms.get(vars[i]);
    }
    return new LinearForm(vars, weights, c[0], f.relation());
  }

  private static final int MAX_DEPTH = 32;

  // adds u x to terms, with x replaced by its definition; the constant goes to c[0]
  private static boolean expand(
      IntVar x,
      long u,
      Map<IntVar, LinearForm> definition,
      Map<IntVar, Long> terms,
      long[] c,
      int depth) {
    LinearForm d = definition.get(x);
    if (d == null) {
      terms.merge(x, u, Math::addExact);
      return true;
    }
    if (depth >= MAX_DEPTH) {
      return false;
    }
    // d: sum a y + w x = e with w = 1 or -1, so u x = u w e - u w sum a y
    int at = indexOf(d, x);
    long uw = Math.multiplyExact(u, d.weights()[at]);
    c[0] = Math.subtractExact(c[0], Math.multiplyExact(uw, d.c()));
    for (int k = 0; k < d.vars().length; k++) {
      if (k != at
          && !expand(
              d.vars()[k],
              Math.negateExact(Math.multiplyExact(uw, d.weights()[k])),
              definition,
              terms,
              c,
              depth + 1)) {
        return false;
      }
    }
    return true;
  }

  private static int indexOf(LinearForm d, IntVar v) {
    for (int k = 0; k < d.vars().length; k++) {
      if (d.vars()[k] == v) {
        return k;
      }
    }
    return -1;
  }
}
