/*
 * VariableElimination.java
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.AbstractReifiedConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Reified;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * Presolve rule 8, variable elimination: a variable that is not kept and that occurs in one or two
 * constraints is removed from the child, and postsolve computes its value from the others.
 *
 * <ul>
 *   <li><em>Singleton column.</em> The variable occurs in one constraint, which every assignment of
 *       its other variables leaves satisfiable by some value of the variable: a definition {@code z
 *       = x + y} whose sum always lies in the domain of {@code z}, an inequality {@code x + y <= z}
 *       where {@code z} can always be large enough, a reification whose Boolean occurs nowhere
 *       else, or any small constraint checked to be so by enumeration. The constraint is left out
 *       of the child with the variable.
 *   <li><em>Doubleton.</em> The variable occurs in two linear constraints, one of which is an
 *       equality with a unit coefficient for it whose other terms always give a value in its
 *       domain. The variable is substituted by those terms in the other constraint, and both are
 *       replaced by the result.
 * </ul>
 *
 * <p>Both keep the solutions projected on the other variables exactly, so the rule is also sound
 * for all-solutions search and counting over the kept variables. Since a later elimination can only
 * make a variable occur in fewer constraints, the rule runs to a fixpoint over a work list, which
 * removes chains of defined variables.
 *
 * <p>The eliminated variables and their constraints (their <em>definitions</em>) are remembered in
 * elimination order. Postsolve copies the definitions into a small store of their own and gives the
 * eliminated variables values in the reverse order, each one once the variables it depends on have
 * theirs; see {@link Reconstruction}.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class VariableElimination {

  /** The most assignments of the other variables enumerated to check a constraint. */
  static final int TUPLE_LIMIT = 256;

  /** The largest domain of the eliminated variable tried value by value in an enumeration. */
  static final int VALUE_LIMIT = 64;

  /** The enumeration budget of one derivation, in propagations of the probe stores. */
  static final int PROBE_BUDGET = 200_000;

  /** The most terms besides the variable a substituted equality may have. */
  static final int SUBSTITUTION_TERMS = 10;

  private final Set<Var> frozen;
  private final boolean defined;
  private final Map<Var, Var> aliases;
  private final Map<Var, List<Constraint>> occurrences = new IdentityHashMap<>();
  private final Map<Constraint, List<Var>> scope = new IdentityHashMap<>();
  private final Map<Constraint, Boolean> live = new IdentityHashMap<>();
  private final List<Constraint> order = new ArrayList<>();
  private final Map<Constraint, Constraint> replacedBy = new IdentityHashMap<>();
  private final List<IntVar> eliminated = new ArrayList<>();
  private final List<Constraint> definitions = new ArrayList<>();
  private final Set<Var> done = Collections.newSetFromMap(new IdentityHashMap<>());
  private int substitutions;
  private int probes;

  /**
   * Creates the rule.
   *
   * @param frozen the variables that must keep a counterpart in the child.
   * @param defined true to eliminate only variables whose value the others determine, so every
   *     solution of the parent keeps one solution of the child; false to eliminate also those that
   *     some value completes, which keeps the solutions projected on the frozen variables only.
   * @param aliases each merged variable mapped to the variable of its class that stays in the
   *     child.
   */
  VariableElimination(Set<Var> frozen, boolean defined, Map<Var, Var> aliases) {
    this.frozen = frozen;
    this.defined = defined;
    this.aliases = aliases;
  }

  /** The variable of the class of a merged variable that stays, or the variable itself. */
  private IntVar stays(IntVar v) {
    return (IntVar) aliases.getOrDefault(v, v);
  }

  /**
   * Eliminates variables from the constraints the child would receive.
   *
   * @param constraints the constraints, attached in the parent and at its fixpoint.
   * @return the constraints for the child, in the order given, with the substituted ones in place
   *     of the constraint they were substituted into.
   */
  List<Constraint> apply(List<Constraint> constraints) {
    Deque<Var> work = new ArrayDeque<>();
    for (Constraint c : constraints) {
      add(c, null, work);
    }
    while (!work.isEmpty()) {
      Var v = work.poll();
      if (done.contains(v)) {
        continue;
      }
      List<Constraint> in = occurrences.get(v);
      if (in.size() == 1) {
        singleton((IntVar) v, in.get(0), work);
      } else if (in.size() == 2) {
        doubleton((IntVar) v, in.get(0), in.get(1), work);
      }
    }
    List<Constraint> result = new ArrayList<>();
    for (Constraint c : order) {
      // a substituted constraint takes the place of the one it replaces
      for (Constraint r = c; r != null; r = replacedBy.get(r)) {
        if (live.containsKey(r)) {
          result.add(r);
        }
      }
    }
    return result;
  }

  /**
   * Returns the eliminated variables, in elimination order.
   *
   * @return the variables.
   */
  List<IntVar> eliminated() {
    return eliminated;
  }

  /**
   * Returns the number of constraints made by substituting a variable.
   *
   * @return the number of substitutions.
   */
  int substitutions() {
    return substitutions;
  }

  /**
   * Returns the postsolve of the eliminated variables.
   *
   * @return the reconstruction, or null when nothing was eliminated.
   */
  Reconstruction reconstruction() {
    return eliminated.isEmpty() ? null : new Reconstruction(eliminated, definitions);
  }

  private boolean candidate(Var v) {
    return v instanceof IntVar && !v.singleton() && !frozen.contains(v) && !done.contains(v);
  }

  /** Adds a constraint, placed where {@code replaced} is in the result order, or at the end. */
  private void add(Constraint c, Constraint replaced, Deque<Var> work) {
    // the scope is a hash set; sorted by name, so the work list order is deterministic
    List<Var> args = new ArrayList<>(c.arguments());
    args.sort(Comparator.comparing(Var::id));
    scope.put(c, args);
    live.put(c, Boolean.TRUE);
    if (replaced == null) {
      order.add(c);
    } else {
      replacedBy.put(replaced, c);
    }
    for (Var v : args) {
      if (candidate(v)) {
        List<Constraint> in = occurrences.computeIfAbsent(v, k -> new ArrayList<>(2));
        in.add(c);
        if (in.size() <= 2) {
          work.add(v);
        }
      }
    }
  }

  private void remove(Constraint c, Deque<Var> work) {
    live.remove(c);
    for (Var v : scope.get(c)) {
      List<Constraint> in = occurrences.get(v);
      if (in != null && in.remove(c) && in.size() <= 2 && !done.contains(v)) {
        work.add(v);
      }
    }
  }

  private void eliminate(IntVar v, Constraint definition, Deque<Var> work) {
    done.add(v);
    eliminated.add(v);
    definitions.add(definition);
    remove(definition, work);
    occurrences.remove(v);
  }

  // ---------------------------------------------------------------------------------------------
  // Singleton column

  private void singleton(IntVar v, Constraint c, Deque<Var> work) {
    if (projectable(v, c)) {
      eliminate(v, c, work);
    }
  }

  /** Whether every assignment of the other variables of c leaves a value of v that satisfies c. */
  private boolean projectable(IntVar v, Constraint c) {
    LinearForm f = linear(c);
    if (f != null) {
      int at = position(f, v);
      if (at >= 0) {
        return defined
            ? f.relation() == LinearForm.EQ && implied(v, f, at) != null
            : projectable(v, f, at);
      }
    }
    if ((c.getClass() == Reified.class || c.getClass() == Implies.class && !defined)
        && v.min() >= 0
        && v.max() <= 1
        && ((AbstractReifiedConstraint) c).b == v
        && !((AbstractReifiedConstraint) c).c.arguments().contains(v)) {
      // v is 0..1 and not fixed: it can take the truth value of the inner constraint, which the
      // others determine, and an implication holds with 0
      return true;
    }
    return enumerated(v, c);
  }

  /** The linear-form test of {@link #projectable(IntVar, Constraint)}. */
  private static boolean projectable(IntVar v, LinearForm f, int at) {
    long a = f.weights()[at];
    long[] rest = restBounds(f, at);
    if (rest == null) {
      return false;
    }
    return switch (f.relation()) {
      case LinearForm.EQ -> implied(v, f, at) != null;
      case LinearForm.LE -> rest[1] + a * (a > 0 ? v.min() : v.max()) <= f.c();
      case LinearForm.GE -> rest[0] + a * (a > 0 ? v.max() : v.min()) >= f.c();
      default -> v.getSize() >= 2;
    };
  }

  /**
   * For an equality {@code a*v + rest = c} with a unit coefficient, the interval of the values the
   * other terms give v, if v's domain holds every value of it.
   *
   * @return the interval, or null when the coefficient is not a unit or v's domain misses a value.
   */
  private static long[] implied(IntVar v, LinearForm f, int at) {
    long a = f.weights()[at];
    long[] rest = restBounds(f, at);
    if (rest == null || (a != 1 && a != -1)) {
      return null;
    }
    long lo = a == 1 ? f.c() - rest[1] : rest[0] - f.c();
    long hi = a == 1 ? f.c() - rest[0] : rest[1] - f.c();
    if (lo < Integer.MIN_VALUE || hi > Integer.MAX_VALUE) {
      return null;
    }
    return v.dom().contains((int) lo, (int) hi) ? new long[] {lo, hi} : null;
  }

  /** The bounds of the sum of the terms other than the one at position at, or null on overflow. */
  private static long[] restBounds(LinearForm f, int at) {
    long min = 0;
    long max = 0;
    try {
      for (int i = 0; i < f.vars().length; i++) {
        if (i != at) {
          long w = f.weights()[i];
          long lo = Math.multiplyExact(w, (long) f.vars()[i].min());
          long hi = Math.multiplyExact(w, (long) f.vars()[i].max());
          min = Math.addExact(min, Math.min(lo, hi));
          max = Math.addExact(max, Math.max(lo, hi));
        }
      }
    } catch (ArithmeticException e) {
      return null;
    }
    return new long[] {min, max};
  }

  /**
   * Checks by enumeration that every assignment of the other variables of a small constraint leaves
   * a value of v that satisfies it (exactly one with {@code defined}), on a copy of the constraint
   * in a store of its own.
   */
  private boolean enumerated(IntVar v, Constraint c) {
    if (probes >= PROBE_BUDGET || v.getSize() > VALUE_LIMIT || !Copyable.canCopy(c)) {
      return false;
    }
    List<IntVar> others = new ArrayList<>();
    long tuples = 1;
    for (Var x : scope.get(c)) {
      if (!(x instanceof IntVar ix)) {
        return false;
      }
      if (x != v && !x.singleton()) {
        others.add(ix);
        tuples *= ix.getSize();
        if (tuples > TUPLE_LIMIT) {
          return false;
        }
      }
    }
    Probe probe = new Probe(scope.get(c), c);
    if (!probe.consistent()) {
      return false;
    }
    return everyTuple(probe, others, 0, probe.copy(v));
  }

  private boolean everyTuple(Probe probe, List<IntVar> others, int i, IntVar v) {
    if (probes++ >= PROBE_BUDGET) {
      return false;
    }
    if (i == others.size()) {
      int supports = 0;
      for (ValueEnumeration e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
        int value = e.nextElement();
        if (probe.tryValue(v, value)) {
          probe.pop();
          supports++;
          if (!defined) {
            break;
          }
        }
      }
      // with defined, the others must leave v exactly one value
      return defined ? supports == 1 : supports > 0;
    }
    // every value of the parent's domain, including those the values of the earlier variables
    // removed here: such a value has no value of v either
    IntVar x = probe.copy(others.get(i));
    for (ValueEnumeration e = others.get(i).dom().valueEnumeration(); e.hasMoreElements(); ) {
      int value = e.nextElement();
      if (!probe.tryValue(x, value)) {
        return false;
      }
      boolean ok = everyTuple(probe, others, i + 1, v);
      probe.pop();
      if (!ok) {
        return false;
      }
    }
    return true;
  }

  /** A copy of one constraint in a store of its own, searched value by value. */
  private static final class Probe implements VarMap {
    private final Store store = new Store();
    private final Map<Var, Var> copies = new IdentityHashMap<>();
    private final boolean consistent;

    Probe(List<Var> args, Constraint c) {
      for (Var x : args) {
        copies.put(x, x.copyTo(store));
      }
      store.impose(((Copyable<?>) c).copy(this));
      consistent = consistency();
    }

    boolean consistent() {
      return consistent;
    }

    IntVar copy(IntVar x) {
      return (IntVar) copies.get(x);
    }

    @Override
    public Store target() {
      return store;
    }

    @Override
    @SuppressWarnings("unchecked")
    public <V extends Var> V get(V v) {
      return (V) copies.get(v);
    }

    /** Assigns a value one level up and propagates; on failure the level is removed again. */
    boolean tryValue(IntVar x, int value) {
      store.setLevel(store.level + 1);
      try {
        x.domain.in(store.level, x, value, value);
        if (consistency()) {
          return true;
        }
      } catch (FailException f) {
        // fall through
      }
      pop();
      return false;
    }

    void pop() {
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }

    private boolean consistency() {
      try {
        return store.consistency();
      } catch (FailException f) {
        return false;
      }
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Doubleton

  private void doubleton(IntVar v, Constraint c1, Constraint c2, Deque<Var> work) {
    LinearForm f1 = linear(c1);
    LinearForm f2 = linear(c2);
    if (f1 == null || f2 == null) {
      return;
    }
    int at1 = position(f1, v);
    int at2 = position(f2, v);
    if (at1 < 0 || at2 < 0) {
      return;
    }
    // the shorter equality defines v when both can
    boolean firstDefines = definesImplied(v, f1, at1);
    boolean secondDefines = definesImplied(v, f2, at2);
    if (firstDefines && secondDefines && f2.vars().length < f1.vars().length) {
      firstDefines = false;
    }
    if (firstDefines) {
      substitute(v, c1, f1, at1, c2, f2, at2, work);
    } else if (secondDefines) {
      substitute(v, c2, f2, at2, c1, f1, at1, work);
    }
  }

  private static boolean definesImplied(IntVar v, LinearForm f, int at) {
    return f.relation() == LinearForm.EQ
        && f.vars().length - 1 <= SUBSTITUTION_TERMS
        && implied(v, f, at) != null;
  }

  /**
   * Replaces {@code l} by {@code l} with v substituted through the equality {@code e}, and
   * eliminates v with {@code e} as its definition.
   */
  private void substitute(
      IntVar v,
      Constraint e,
      LinearForm fe,
      int ate,
      Constraint l,
      LinearForm fl,
      int atl,
      Deque<Var> work) {
    // v = ae * (ce - sum of the other terms of e), since ae is 1 or -1
    long k = fl.weights()[atl] * fe.weights()[ate];
    Map<IntVar, Long> terms = new LinkedHashMap<>();
    long rhs;
    try {
      for (int i = 0; i < fl.vars().length; i++) {
        // terms of one class of merged variables become one term, since the child names the class
        // by one variable
        if (i != atl) {
          terms.merge(stays(fl.vars()[i]), fl.weights()[i], Math::addExact);
        }
      }
      for (int i = 0; i < fe.vars().length; i++) {
        if (i != ate) {
          terms.merge(stays(fe.vars()[i]), Math.multiplyExact(-k, fe.weights()[i]), Math::addExact);
        }
      }
      rhs = Math.subtractExact(fl.c(), Math.multiplyExact(k, fe.c()));
    } catch (ArithmeticException ex) {
      return;
    }
    terms.values().removeIf(w -> w == 0);
    if (terms.keySet().stream().allMatch(Var::singleton)
        || rhs < Integer.MIN_VALUE
        || rhs > Integer.MAX_VALUE) {
      return;
    }
    IntVar[] vars = new IntVar[terms.size()];
    int[] weights = new int[terms.size()];
    int n = 0;
    for (Map.Entry<IntVar, Long> t : terms.entrySet()) {
      if (t.getValue() < Integer.MIN_VALUE || t.getValue() > Integer.MAX_VALUE) {
        return;
      }
      vars[n] = t.getKey();
      weights[n++] = (int) (long) t.getValue();
    }
    String rel =
        switch (fl.relation()) {
          case LinearForm.LE -> "<=";
          case LinearForm.GE -> ">=";
          case LinearForm.EQ -> "==";
          default -> "!=";
        };
    LinearInt substituted;
    try {
      substituted =
          l.getClass() == LinearIntDom.class
              ? new LinearIntDom(vars, weights, rel, (int) rhs)
              : new LinearInt(vars, weights, rel, (int) rhs);
    } catch (ArithmeticException | IllegalArgumentException ex) {
      // the sum can overflow
      return;
    }
    substitutions++;
    add(substituted, l, work);
    remove(l, work);
    eliminate(v, e, work);
  }

  // ---------------------------------------------------------------------------------------------

  /** The constraint as a linear relation, or null. */
  private static LinearForm linear(Constraint c) {
    if (c instanceof LinearInt li) {
      // a subclass other than LinearIntDom may enforce more than its linear relation
      boolean plain = li.getClass() == LinearInt.class || li.getClass() == LinearIntDom.class;
      return plain ? li.linearRelation() : null;
    }
    return c instanceof LinearExplainable le ? le.linearForm() : null;
  }

  /** The position of v in the form if it occurs there exactly once, otherwise -1. */
  private static int position(LinearForm f, Var v) {
    int at = -1;
    for (int i = 0; i < f.vars().length; i++) {
      if (f.vars()[i] == v) {
        if (at >= 0) {
          return -1;
        }
        at = i;
      }
    }
    return at >= 0 && f.weights()[at] != 0 ? at : -1;
  }
}
