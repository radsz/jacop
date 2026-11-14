/*
 * DfsSplit.java
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

import java.util.Arrays;
import java.util.Map;
import org.jacop.constraints.AbstractXcompC;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XneqC;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.lcg.SharedTree;
import org.jacop.search.ExitChildListener;
import org.jacop.search.SelectChoicePoint;

/**
 * Work stealing for depth-first search in a portfolio (Schulte, Parallel search made simple, TRICS
 * 2000; Chu, Schulte and Stuckey, CP 2009): threads with the same search divide its tree through a
 * {@link SharedTree}. A thread solves the part of the tree given by a cube (decisions imposed at a
 * level above the root); when another thread waits, it gives away the right branch of its
 * shallowest open decision, as the cube of the decisions above it plus the negation of that
 * decision, and does not explore that branch itself. The decisions above are replayed by the thief
 * (recomputation), which needs no copy of the store.
 *
 * <p>The selection is wrapped to record the decisions of the search, and the search's exit child
 * listener skips the right branches given away. Decisions on an integer variable by value and by
 * comparison with a constant can be given away; others are passed over.
 *
 * @param <T> the type of the search's variables
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class DfsSplit<T extends Var> implements SelectChoicePoint<T>, ExitChildListener<T> {

  private static final int GE = 0;
  private static final int EQ = 1;
  private static final int NEGATED = 2;

  private final SharedTree tree;
  private final SelectChoicePoint<T> select;
  private final Store store;
  // the atom ids of the model's variables, by variable, and the variables by id
  private final Map<IntVar, Integer> ids;
  private final IntVar[] byId;
  // the cube being solved
  private int[] cube;
  // per depth (store level) of the search: the decision as an atom (id, kind, value), or id -1
  private int[][] atoms = new int[64][];
  private boolean[] right = new boolean[64];
  private boolean[] givenAway = new boolean[64];
  private int baseLevel;
  private int top = -1;
  // the depth of the first decision of the search under the cube
  private int first = Integer.MAX_VALUE;
  private T lastVar;

  /** Statistics: the right branches given away. */
  long splits;

  DfsSplit(
      SharedTree tree,
      SelectChoicePoint<T> select,
      Store store,
      Map<IntVar, Integer> ids,
      IntVar[] byId) {
    this.tree = tree;
    this.select = select;
    this.store = store;
    this.ids = ids;
    this.byId = byId;
  }

  /**
   * Imposes a cube taken from the tree at a new level of the store and makes it the part this
   * thread searches.
   *
   * @param c the cube
   * @return false when the cube fails at once
   */
  boolean impose(int[] c) {
    cube = c;
    top = -1;
    first = Integer.MAX_VALUE;
    store.setLevel(store.level + 1);
    baseLevel = store.level;
    // as domain changes, which the level holds, and not as constraints, which stay imposed in the
    // store after the level is removed and would cut the parts of the tree taken later
    try {
      for (int k = 0; k < c.length; k += 3) {
        IntVar x = byId[c[k]];
        int v = c[k + 2];
        switch (c[k + 1]) {
          case GE -> x.domain.inMin(store.level, x, v);
          case EQ -> x.domain.in(store.level, x, v, v);
          case GE + NEGATED -> x.domain.inMax(store.level, x, v - 1);
          default -> x.domain.inComplement(store.level, x, v);
        }
      }
    } catch (FailException _) {
      return false;
    }
    return store.consistency();
  }

  /** Takes back the cube's level. */
  void retract() {
    store.removeLevel(store.level);
    store.setLevel(store.level - 1);
  }

  @Override
  public T getChoiceVariable(int index) {
    T v = select.getChoiceVariable(index);
    lastVar = v;
    if (v == null) {
      return null;
    }
    giveAway();
    return v;
  }

  @Override
  public int getChoiceValue() {
    int value = select.getChoiceValue();
    int[] atom = null;
    if (lastVar instanceof IntVar x && ids.containsKey(x)) {
      atom = new int[] {ids.get(x), EQ, value};
    }
    record(atom);
    return value;
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    PrimitiveConstraint choice = select.getChoiceConstraint(index);
    if (choice != null) {
      giveAway();
      record(atom(choice));
    }
    return choice;
  }

  private int[] atom(PrimitiveConstraint choice) {
    if (!(choice instanceof AbstractXcompC p) || !ids.containsKey(p.variable())) {
      return null;
    }
    int id = ids.get(p.variable());
    int c = p.constant();
    return switch (choice) {
      case XeqC _ -> new int[] {id, EQ, c};
      case XneqC _ -> new int[] {id, EQ + NEGATED, c};
      case XgteqC _ -> new int[] {id, GE, c};
      case XgtC _ -> new int[] {id, GE, c + 1};
      case XlteqC _ -> new int[] {id, GE + NEGATED, c + 1};
      case XltC _ -> new int[] {id, GE + NEGATED, c};
      default -> null;
    };
  }

  // the decision of the node at the store's current level (the search raised it before choosing)
  private void record(int[] atom) {
    int d = store.level - baseLevel;
    if (d < 0) {
      return;
    }
    if (d >= atoms.length) {
      int n = Math.max(d + 1, 2 * atoms.length);
      atoms = Arrays.copyOf(atoms, n);
      right = Arrays.copyOf(right, n);
      givenAway = Arrays.copyOf(givenAway, n);
    }
    first = Math.min(first, d);
    atoms[d] = atom;
    right[d] = false;
    givenAway[d] = false;
    top = d;
  }

  // when a thread waits, gives away the right branch of the shallowest open decision
  private void giveAway() {
    if (cube == null || !tree.wantsSplit()) {
      return;
    }
    int[] c = cube;
    for (int d = first; d <= top; d++) {
      int[] a = atoms[d];
      if (a == null) {
        return; // a decision that cannot be given away: the branches below depend on it
      }
      if (!right[d] && !givenAway[d]) {
        givenAway[d] = true;
        int[] gift = SharedTree.extend(c, a[0], a[1] ^ NEGATED, a[2]);
        tree.split(gift);
        splits++;
        return;
      }
      int kind = right[d] ? a[1] ^ NEGATED : a[1];
      c = SharedTree.extend(c, a[0], kind, a[2]);
    }
  }

  private boolean exitLeft() {
    int d = store.level - baseLevel;
    if (d < 0 || d > top) {
      return true;
    }
    top = d;
    if (givenAway[d]) {
      return false;
    }
    right[d] = true;
    return true;
  }

  @Override
  public boolean leftChild(T v, int value, boolean status) {
    return exitLeft();
  }

  @Override
  public boolean leftChild(PrimitiveConstraint choice, boolean status) {
    return exitLeft();
  }

  @Override
  public void rightChild(T v, int value, boolean status) {
    // nothing to record: the node's entry is replaced by the next decision at its level
  }

  @Override
  public void rightChild(PrimitiveConstraint choice, boolean status) {
    // as above
  }

  @Override
  public void setChildrenListeners(ExitChildListener<T>[] children) {
    throw new UnsupportedOperationException("split search takes no child listeners");
  }

  @Override
  public void setChildrenListeners(ExitChildListener<T> child) {
    throw new UnsupportedOperationException("split search takes no child listeners");
  }

  @Override
  public Map<T, Integer> getVariablesMapping() {
    return select.getVariablesMapping();
  }

  @Override
  public int getIndex() {
    return select.getIndex();
  }
}
