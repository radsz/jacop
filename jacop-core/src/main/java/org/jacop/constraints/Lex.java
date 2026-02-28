/*
 * Lex.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2010 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;

/**
 * It constructs a Lex (lexicographical order) constraint.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Lex extends DecomposedConstraint<Constraint> {

  /** Indicates if the lex enforces a lower-than relationship. */
  private final boolean lexLt;

  /** A two dimensional array containing arrays which have to be lexicographically ordered. */
  private IntVar[][] x;

  /** It contains constraints of the lex constraint decomposition. */
  List<Constraint> constraints;

  /**
   * It creates a lexicographical order for vectors x[i], i.e. forall i, exists j : x[i][k] =
   * x[i+1][k] for k {@literal <} j and x[i][k] {@literal <=} x[i+1][k] for k {@literal >=} j
   *
   * <p>vectors x[i] does not need to be of the same size. boolea lt defines if we require
   * Lex_{{@literal <}} (lt = false) or Lex_{{@literal =<}} (lt = true)
   *
   * @param x vector of vectors which assignment is constrained by Lex constraint.
   */
  public Lex(IntVar[][] x) {

    this(x, false);
  }

  /**
   * It creates a lexicographical order constraint for vectors x with the specified ordering type.
   *
   * @param x vector of vectors whose assignment is constrained by the Lex constraint.
   * @param lt if true, strict less-than ordering is enforced; otherwise, less-than-or-equal.
   */
  public Lex(IntVar[][] x, boolean lt) {

    if (x == null) {
      throw new IllegalArgumentException("x list is null.");
    }
    this.x = new IntVar[x.length][];

    lexLt = lt;

    for (int i = 0; i < x.length; i++) {

      if (x[i] == null) {
        throw new IllegalArgumentException(i + "-th vector in x is null");
      }
      this.x[i] = new IntVar[x[i].length];

      for (int j = 0; j < x[i].length; j++) {
        if (x[i][j] == null) {
          throw new IllegalArgumentException(j + "-th element of " + i + "-th vector in x is null");
        }
        this.x[i][j] = x[i][j];
      }
    }
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }

  @Override
  public List<Constraint> decompose(Store store) {

    if (constraints != null) {
      return constraints;
    }

    if (x.length == 2) {
      if (lexLt) {
        return decomposeLt(store);
      } else {
        return decomposeLe(store);
      }
    }

    // smaller Lex with several lists can be decompose with Regular
    if (lexLt) {
      return decomposeLtRegular(store);
    } else {
      return decomposeLeRegular(store);
    }
  }

  /**
   * Helper class to build FSM for lexicographic constraints. Encapsulates common FSM construction
   * logic for both LE and LT variants.
   */
  private class RegularFsmBuilder {

    private final Store store;
    private final boolean isLe;
    private int numberVar;
    private BooleanVar[][] lt;
    private BooleanVar[][] eq;
    private FsmState[][][] state;
    private FsmState[][] addState;
    private IntVar[] vars;
    private Fsm fsm;

    RegularFsmBuilder(Store store, boolean isLe) {
      this.store = store;
      this.isLe = isLe;
    }

    void buildFsm() {
      numberVar = 0;
      lt = new BooleanVar[x.length - 1][];
      eq = new BooleanVar[x.length - 1][];
      state = new FsmState[x.length - 1][][];
      addState = new FsmState[x.length - 2][];

      buildVariablesAndStates();
      buildVarsArray();
      initializeFsm();
      buildTransitions();
    }

    private void buildVariablesAndStates() {
      for (int i = 0; i < x.length - 1; i++) {
        int sizeToCompare = Math.min(x[i].length, x[i + 1].length);

        if (isLe) {
          lt[i] = new BooleanVar[sizeToCompare];
          eq[i] = new BooleanVar[sizeToCompare];
        } else {
          lt[i] = new BooleanVar[sizeToCompare];
          eq[i] = new BooleanVar[sizeToCompare - 1];
        }
        state[i] = new FsmState[sizeToCompare][];

        for (int j = 0; j < sizeToCompare; j++) {
          buildLtVariable(i, j, sizeToCompare);
          buildEqVariable(i, j, sizeToCompare);
          buildStates(i, j, sizeToCompare);
          buildAddStates(i, j, sizeToCompare);
        }
      }
    }

    private void buildLtVariable(int i, int j, int sizeToCompare) {
      if (isLe) {
        lt[i][j] = new BooleanVar(store, "lt_" + i + "_" + j);
        constraints.add(new Reified(new XltY(x[i][j], x[i + 1][j]), lt[i][j]));
      } else {
        if (x[i].length < x[i + 1].length) {
          if (j < sizeToCompare - 1) {
            lt[i][j] = new BooleanVar(store, "lt_" + i + "_" + j);
            constraints.add(new Reified(new XltY(x[i][j], x[i + 1][j]), lt[i][j]));
            numberVar++;
          } else {
            lt[i][j] = new BooleanVar(store, "le_" + i + "_" + j);
            constraints.add(new Reified(new XlteqY(x[i][j], x[i + 1][j]), lt[i][j]));
            numberVar++;
          }
        } else {
          lt[i][j] = new BooleanVar(store, "lt_" + i + "_" + j);
          constraints.add(new Reified(new XltY(x[i][j], x[i + 1][j]), lt[i][j]));
          numberVar++;
        }
      }
    }

    private void buildEqVariable(int i, int j, int sizeToCompare) {
      if (isLe) {
        eq[i][j] = new BooleanVar(store, "eq_" + i + "_" + j);
        constraints.add(new Reified(new XeqY(x[i][j], x[i + 1][j]), eq[i][j]));

        if (x[i].length > x[i + 1].length && j == sizeToCompare - 1) {
          constraints.add(new XeqC(eq[i][j], 0));
        }
      } else {
        if (j < sizeToCompare - 1) {
          eq[i][j] = new BooleanVar(store, "eq_" + i + "_" + j);
          constraints.add(new Reified(new XeqY(x[i][j], x[i + 1][j]), eq[i][j]));
          numberVar++;
        }
      }
    }

    private void buildStates(int i, int j, int sizeToCompare) {
      state[i][j] = new FsmState[2];
      state[i][j][0] = new FsmState();
      if (isLe) {
        state[i][j][1] = new FsmState();
        numberVar += 2;
      } else {
        if (j < sizeToCompare - 1) {
          state[i][j][1] = new FsmState();
        }
      }
    }

    private void buildAddStates(int i, int j, int sizeToCompare) {
      if (i < x.length - 2 && j == 0) {
        int addStateSize = isLe ? 2 * (sizeToCompare - j) - 1 : 2 * (sizeToCompare - j) - 2;
        addState[i] = new FsmState[addStateSize];

        for (int k = 0; k < addState[i].length; k++) {
          addState[i][k] = new FsmState();
        }
      }
    }

    private void buildVarsArray() {
      vars = new IntVar[numberVar];
      fsm = new Fsm();
      int k = 0;
      for (int i = 0; i < lt.length; i++) {
        for (int j = 0; j < lt[i].length; j++) {
          k = addVarsAndStatesFor(i, j, k);
        }
      }
      for (FsmState[] fsmStates : addState) {
        fsm.allStates.addAll(Arrays.asList(fsmStates));
      }
    }

    private int addVarsAndStatesFor(int i, int j, int k) {
      vars[k++] = lt[i][j];
      if (isLe) {
        vars[k++] = eq[i][j];
        fsm.allStates.add(state[i][j][0]);
        fsm.allStates.add(state[i][j][1]);
      } else {
        if (j < eq[i].length) {
          vars[k++] = eq[i][j];
        }
        fsm.allStates.add(state[i][j][0]);
        if (j < eq[i].length) {
          fsm.allStates.add(state[i][j][1]);
        }
      }
      return k;
    }

    private void initializeFsm() {
      fsm.initState = state[0][0][0];
      FsmState terminate = new FsmState();
      fsm.allStates.add(terminate);
      fsm.finalStates.add(terminate);
    }

    private void buildTransitions() {
      FsmState terminate = fsm.finalStates.iterator().next();

      for (int i = 0; i < state.length; i++) {
        for (int j = 0; j < state[i].length; j++) {
          buildState0Transitions(i, j, terminate);
          buildState1Transitions(i, j, terminate);
        }
      }

      terminate.transitions.add(new FsmTransition(new IntervalDomain(0, 1), terminate));
    }

    private void buildState0Transitions(int i, int j, FsmState terminate) {
      if (i != state.length - 1) {
        state0TransitionsNonLastRow(i, j, terminate);
      } else {
        state0TransitionsLastRow(i, j, terminate);
      }
    }

    private void state0TransitionsNonLastRow(int i, int j, FsmState terminate) {
      if (addState[i].length != 0) {
        state0TransitionsAddStateNonEmpty(i, j, terminate);
      } else {
        state0TransitionsAddStateEmpty(i, j);
      }
    }

    private void state0TransitionsAddStateNonEmpty(int i, int j, FsmState terminate) {
      if (j == 0) {
        state0TransitionsJZero(i);
      } else {
        state0TransitionsJNonZero(i, j);
      }
      state0AddZeroTransitionToState1(i, j);
    }

    private void state0TransitionsJZero(int i) {
      state[i][0][0].transitions.add(new FsmTransition(new IntervalDomain(1, 1), addState[i][0]));
      for (int s = 1; s < addState[i].length; s++) {
        addState[i][s - 1].transitions.add(
            new FsmTransition(new IntervalDomain(0, 1), addState[i][s]));
      }
      addState[i][addState[i].length - 1].transitions.add(
          new FsmTransition(new IntervalDomain(0, 1), state[i + 1][0][0]));
    }

    private void state0TransitionsJNonZero(int i, int j) {
      if (isLe) {
        state[i][j][0].transitions.add(
            new FsmTransition(new IntervalDomain(1, 1), addState[i][2 * j]));
      } else if (j != state[i].length - 1) {
        state[i][j][0].transitions.add(
            new FsmTransition(new IntervalDomain(1, 1), addState[i][2 * j]));
      } else {
        state[i][j][0].transitions.add(
            new FsmTransition(new IntervalDomain(1, 1), state[i + 1][0][0]));
      }
    }

    private void state0AddZeroTransitionToState1(int i, int j) {
      if (isLe || j != state[i].length - 1) {
        state[i][j][0].transitions.add(new FsmTransition(new IntervalDomain(0, 0), state[i][j][1]));
      }
    }

    private void state0TransitionsAddStateEmpty(int i, int j) {
      if (!isLe) {
        state[i][j][0].transitions.add(
            new FsmTransition(new IntervalDomain(1, 1), state[i + 1][0][0]));
      }
    }

    private void state0TransitionsLastRow(int i, int j, FsmState terminate) {
      state[i][j][0].transitions.add(new FsmTransition(new IntervalDomain(1, 1), terminate));
      if (isLe) {
        state[i][j][0].transitions.add(new FsmTransition(new IntervalDomain(0, 0), state[i][j][1]));
      }
    }

    private void buildState1Transitions(int i, int j, FsmState terminate) {
      if (isLe) {
        if (i != state.length - 1) {
          if (j != state[i].length - 1) {
            state[i][j][1].transitions.add(
                new FsmTransition(new IntervalDomain(1, 1), state[i][j + 1][0]));
          } else {
            state[i][j][1].transitions.add(
                new FsmTransition(new IntervalDomain(1, 1), state[i + 1][0][0]));
          }
        } else {
          if (j != state[i].length - 1) {
            state[i][j][1].transitions.add(
                new FsmTransition(new IntervalDomain(1, 1), state[i][j + 1][0]));
          } else {
            state[i][j][1].transitions.add(new FsmTransition(new IntervalDomain(1, 1), terminate));
          }
        }
      } else {
        if (j != state[i].length - 1) {
          state[i][j][1].transitions.add(
              new FsmTransition(new IntervalDomain(1, 1), state[i][j + 1][0]));
        }
      }
    }
  }

  /**
   * Decomposes the less-than-or-equal lexicographic constraint using a Regular automaton.
   *
   * @param store the constraint store used for decomposition.
   * @return the list of constraints forming the decomposition.
   */
  public List<Constraint> decomposeLeRegular(Store store) {

    if (constraints == null) {
      constraints = new ArrayList<>();
    } else {
      return constraints;
    }

    RegularFsmBuilder builder = new RegularFsmBuilder(store, true);
    builder.buildFsm();
    constraints.add(new Regular(builder.fsm, builder.vars));

    return constraints;
  }

  /**
   * Decomposes the strict less-than lexicographic constraint using a Regular automaton.
   *
   * @param store the constraint store used for decomposition.
   * @return the list of constraints forming the decomposition.
   */
  public List<Constraint> decomposeLtRegular(Store store) {

    if (constraints == null) {
      constraints = new ArrayList<>();
    } else {
      return constraints;
    }

    RegularFsmBuilder builder = new RegularFsmBuilder(store, false);
    builder.buildFsm();
    constraints.add(new Regular(builder.fsm, builder.vars));

    return constraints;
  }

  /**
   * Decomposes the strict less-than lexicographic constraint for exactly two vectors.
   *
   * @param store the constraint store used for decomposition.
   * @return the list of constraints forming the decomposition.
   */
  public List<Constraint> decomposeLt(Store store) {

    if (constraints == null) {
      constraints = new ArrayList<>();
    } else {
      return constraints;
    }

    int sizeToCompare = Math.min(x[0].length, x[1].length);

    BooleanVar[] b = new BooleanVar[sizeToCompare + 1];
    for (int i = 0; i < b.length; i++) {
      b[i] = new BooleanVar(store);
    }

    constraints.add(new XeqC(b[0], 1));

    for (int i = 0; i < sizeToCompare; i++) {
      Constraint c =
          new Reified(
              new And(
                  new XlteqY(x[0][i], x[1][i]),
                  new Or(new XltY(x[0][i], x[1][i]), new XeqC(b[i + 1], 1))),
              b[i]);

      constraints.add(c);
    }
    if (x[0].length < x[1].length) {
      constraints.add(new XeqC(b[sizeToCompare], 1));
    } else {
      constraints.add(new XeqC(b[sizeToCompare], 0));
    }

    return constraints;
  }

  /**
   * Decomposes the less-than-or-equal lexicographic constraint for exactly two vectors.
   *
   * @param store the constraint store used for decomposition.
   * @return the list of constraints forming the decomposition.
   */
  public List<Constraint> decomposeLe(Store store) {

    if (constraints == null) {
      constraints = new ArrayList<>();
    } else {
      return constraints;
    }

    int sizeToCompare = Math.min(x[0].length, x[1].length);

    BooleanVar[] b = new BooleanVar[sizeToCompare];
    for (int i = 0; i < b.length; i++) {
      b[i] = new BooleanVar(store);
    }

    constraints.add(new XeqC(b[0], 1));

    for (int i = 0; i < sizeToCompare; i++) {
      if (i == sizeToCompare - 1) {
        constraints.add(new Reified(new XlteqY(x[0][i], x[1][i]), b[i]));
      } else {
        constraints.add(
            new Reified(
                new And(
                    new XlteqY(x[0][i], x[1][i]),
                    new Or(new XltY(x[0][i], x[1][i]), new XeqC(b[i + 1], 1))),
                b[i]));
      }
    }

    return constraints;
  }
}
