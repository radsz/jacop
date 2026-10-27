/*
 * ReificationCleanup.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.Copyable;
import org.jacop.api.Monotone;
import org.jacop.api.Monotone.Direction;
import org.jacop.api.VarMap;
import org.jacop.constraints.AbstractReifiedConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * Presolve rule 6, reification cleanup (design section 6). It decides how each {@link Reified} and
 * {@link Implies} of the parent goes into the child:
 *
 * <ul>
 *   <li>with its Boolean fixed, {@code b <-> c} becomes {@code c} or {@code not c}, and {@code b ->
 *       c} becomes {@code c} or disappears. This keeps every solution.
 *   <li>{@code b <-> c} where every other constraint on {@code b} is satisfied at least as well
 *       with {@code b} true (each is {@link Monotone} upwards in {@code b}) becomes the
 *       half-reification {@code b -> c}; when they all prefer {@code b} false, it becomes {@code c
 *       -> b}; when no other constraint uses {@code b}, it disappears, and so does {@code b -> c}.
 *       This is the enforcement-literal cleanup of CP-SAT and MiniZinc's half-reification (Feydy,
 *       Somogyi and Stuckey, CP 2011).
 * </ul>
 *
 * <p>The second kind keeps satisfiability and optima, but not every solution: the child may give
 * {@code b} a value that the reification forbids, as long as {@code b} is not frozen. Such a {@code
 * b} is <em>relaxed</em>: postsolve writes the child's value back only when it is the value that
 * enforces the half-reification ({@link #relaxed()}), and otherwise leaves {@code b} to the parent,
 * where the reification, still checked in checking mode, gives it its value. The rule runs only
 * when the frozen variables are known and all-solution search or counting is off, and only on
 * reifications of integer constraints: a float constraint whose negation is no longer enforced
 * prunes less, and a float search then splits far more (the golden {@code voltage_divider} model
 * went from 0.1 s to a time-out).
 *
 * <p>The rule weakens the child's problem, so it does not belong among the rules that narrow the
 * parent; the derivation applies it to the constraints it copies, after the parent's fixpoint.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class ReificationCleanup {

  /** How a constraint goes into the child. */
  private enum Form {
    /** Copied as it is. */
    COPY,
    /** The nested constraint alone. */
    PLAIN,
    /** The negation of the nested constraint. */
    NOT,
    /** {@code b -> c}. */
    IMPLIES,
    /** {@code c -> b}. */
    CONVERSE,
    /** Left out. */
    DROP
  }

  /** At most this many passes; each pass can expose new half-reifications to the next. */
  private static final int PASSES = 4;

  private final List<Constraint> constraints;
  private final Set<Var> frozen;
  private final boolean relax;
  private final Map<Constraint, Form> forms = new IdentityHashMap<>();
  private final Map<Var, List<Constraint>> occurrences = new IdentityHashMap<>();
  private final Map<Var, Integer> relaxed = new IdentityHashMap<>();
  private int simplified;
  private int halfReified;
  private int dropped;

  /**
   * Prepares the rule.
   *
   * @param constraints the constraints the child would receive, in a deterministic order.
   * @param frozen the variables whose values must stay those of a parent solution, or null if every
   *     variable is frozen.
   * @param relax true if the rule may give up solutions that differ only in non-frozen variables.
   */
  ReificationCleanup(List<Constraint> constraints, Set<Var> frozen, boolean relax) {
    this.constraints = constraints;
    this.frozen = frozen;
    this.relax = relax && frozen != null;
  }

  /** Decides the form of every constraint. */
  void run() {
    for (Constraint c : constraints) {
      if (c.getClass() == Reified.class || c.getClass() == Implies.class) {
        simplifyFixed((AbstractReifiedConstraint) c);
      }
    }
    if (!relax) {
      return;
    }
    for (Constraint c : constraints) {
      if (form(c) == Form.DROP) {
        continue;
      }
      for (Var v : c.arguments()) {
        if (candidate(v)) {
          occurrences.computeIfAbsent(v, k -> new ArrayList<>()).add(c);
        }
      }
    }
    boolean changed = true;
    for (int pass = 0; changed && pass < PASSES; pass++) {
      changed = false;
      for (Constraint c : constraints) {
        if (form(c) == Form.COPY
            && (c.getClass() == Reified.class || c.getClass() == Implies.class)) {
          changed |= relax((AbstractReifiedConstraint) c);
        }
      }
    }
  }

  private void simplifyFixed(AbstractReifiedConstraint r) {
    if (!r.b.singleton() || r.c.arguments().contains(r.b)) {
      return;
    }
    boolean holds = r.b.value() == 1;
    if (r instanceof Reified) {
      forms.put(r, holds ? Form.PLAIN : Form.NOT);
    } else {
      forms.put(r, holds ? Form.PLAIN : Form.DROP);
    }
    simplified++;
  }

  private boolean candidate(Var v) {
    return v instanceof IntVar x
        && !x.singleton()
        && x.min() >= 0
        && x.max() <= 1
        && !frozen.contains(v);
  }

  private boolean relax(AbstractReifiedConstraint r) {
    IntVar b = r.b;
    if (!candidate(b) || r.c.arguments().contains(b) || !overIntegers(r.c)) {
      return false;
    }
    Direction wanted = null;
    for (Constraint o : occurrences.get(b)) {
      if (o == r) {
        continue;
      }
      Direction d = direction(o, b);
      if (d != null) {
        wanted = wanted == null ? d : wanted.and(d);
        if (wanted == Direction.NONE) {
          return false;
        }
      }
    }
    Form form;
    if (wanted == null) {
      form = Form.DROP;
      dropped++;
    } else if (r instanceof Implies) {
      return false;
    } else if (wanted == Direction.UP) {
      form = Form.IMPLIES;
      relaxed.put(b, 1);
      halfReified++;
    } else {
      form = Form.CONVERSE;
      relaxed.put(b, 0);
      halfReified++;
    }
    forms.put(r, form);
    return true;
  }

  /**
   * Whether a constraint has integer variables only. A float or set constraint loses pruning when
   * its negation is no longer enforced, which a float search pays for with many more splits.
   */
  private static boolean overIntegers(Constraint c) {
    for (Var v : c.arguments()) {
      if (!(v instanceof IntVar)) {
        return false;
      }
    }
    return true;
  }

  /**
   * The direction in which {@code v} may move without breaking a constraint in its current form, or
   * null if the form no longer uses {@code v}.
   */
  private Direction direction(Constraint c, Var v) {
    Form form = form(c);
    if (form == Form.COPY) {
      return c instanceof Monotone m ? m.monotonicity(v) : Direction.NONE;
    }
    if (form == Form.DROP) {
      return null;
    }
    AbstractReifiedConstraint r = (AbstractReifiedConstraint) c;
    if (v == r.b) {
      return switch (form) {
        case IMPLIES -> Direction.DOWN;
        case CONVERSE -> Direction.UP;
        default -> null;
      };
    }
    Direction inner = r.c instanceof Monotone m ? m.monotonicity(v) : Direction.NONE;
    return form == Form.NOT || form == Form.CONVERSE ? inner.negate() : inner;
  }

  private Form form(Constraint c) {
    return forms.getOrDefault(c, Form.COPY);
  }

  /**
   * Tells whether a constraint is left out of the child.
   *
   * @param c a constraint given to the rule.
   * @return true if it is left out.
   */
  boolean dropped(Constraint c) {
    return form(c) == Form.DROP;
  }

  /**
   * Tells whether a constraint goes into the child in another form than its copy.
   *
   * @param c a constraint given to the rule.
   * @return true if {@link #rewrite} builds it.
   */
  boolean rewritten(Constraint c) {
    Form form = form(c);
    return form != Form.COPY && form != Form.DROP;
  }

  /**
   * The variables the child's counterpart of a constraint uses, in the parent.
   *
   * @param c a constraint given to the rule, not dropped.
   * @return its variables.
   */
  Set<Var> arguments(Constraint c) {
    Form form = form(c);
    if (form == Form.PLAIN || form == Form.NOT) {
      return ((AbstractReifiedConstraint) c).c.arguments();
    }
    return c.arguments();
  }

  /**
   * Builds the child's counterpart of a rewritten constraint.
   *
   * @param c a constraint for which {@link #rewritten} holds.
   * @param map the derivation's map to the child.
   * @return the new constraint over the child's variables.
   */
  Constraint rewrite(Constraint c, VarMap map) {
    AbstractReifiedConstraint r = (AbstractReifiedConstraint) c;
    PrimitiveConstraint inner = Copyable.copyOf(r.c, map);
    return switch (form(c)) {
      case PLAIN -> inner;
      case NOT -> new Not(inner);
      case IMPLIES -> new Implies(map.get(r.b), inner);
      case CONVERSE -> new IfThen(inner, new XeqC(map.get(r.b), 1));
      default -> throw new IllegalStateException("Constraint " + c.id() + " is not rewritten");
    };
  }

  /**
   * Returns the relaxed variables, each with the value that postsolve writes back; for any other
   * value of the child the parent decides.
   *
   * @return the relaxed variables.
   */
  Map<Var, Integer> relaxed() {
    return relaxed;
  }

  /**
   * Returns the number of reifications whose Boolean was fixed.
   *
   * @return the number.
   */
  int simplified() {
    return simplified;
  }

  /**
   * Returns the number of reifications turned into half-reifications.
   *
   * @return the number.
   */
  int halfReified() {
    return halfReified;
  }

  /**
   * Returns the number of reifications and implications dropped because nothing else uses their
   * Boolean.
   *
   * @return the number.
   */
  int dropped() {
    return dropped;
  }
}
