/*
 * SetPb.java
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

package org.jacop.set.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Predicate;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbModel;
import org.jacop.set.core.SetVar;

/**
 * The literals and lines of set variables in a {@link PbModel}: the membership of an element and
 * the cardinality of a set are those of its {@link SetMirror}, with the elements of its greatest
 * lower bound when the mirror was made always in and those outside its least upper bound always
 * out. A set without a mirror is a constant.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SetPb {

  private SetPb() {}

  /**
   * Tells whether the memberships and the cardinalities of sets can be stated: each has a mirror or
   * is a constant.
   *
   * @param sets the sets
   * @return true when they can
   */
  static boolean stated(SetVar... sets) {
    for (SetVar s : sets) {
      if (s.lcgMirror() == null && !s.singleton()) {
        return false;
      }
    }
    return true;
  }

  /**
   * Returns the literal of an element being in a set.
   *
   * @param model the model
   * @param s the set, which is {@link #stated}
   * @param element the element
   * @return the literal, "1" or "0" when the membership is fixed in the model
   */
  static String in(PbModel model, SetVar s, int element) {
    SetMirror m = s.lcgMirror();
    if (m == null) {
      return s.domain.glb().contains(element) ? "1" : "0";
    }
    if (m.inRootGlb(element)) {
      return "1";
    }
    IntVar b = m.member(element);
    return b == null ? "0" : model.atLeast(b, 1);
  }

  /**
   * Returns the literal of a set having at least k elements.
   *
   * @param model the model
   * @param s the set, which is {@link #stated}
   * @param k the number of elements
   * @return the literal, "1" or "0" when it is fixed in the model
   */
  static String cardinalityAtLeast(PbModel model, SetVar s, int k) {
    SetMirror m = s.lcgMirror();
    if (m == null) {
      return s.domain.glb().getSize() >= k ? "1" : "0";
    }
    return model.atLeast(m.cardinality(), k);
  }

  /**
   * Returns the elements a set may have in the model: its least upper bound when its mirror was
   * made.
   *
   * @param sets the sets, which are {@link #stated}
   * @return the union of their least upper bounds
   */
  static IntDomain lub(SetVar... sets) {
    IntDomain u = new IntervalDomain();
    for (SetVar s : sets) {
      SetMirror m = s.lcgMirror();
      u = u.union(m == null ? s.domain.lub() : m.rootLub());
    }
    return u;
  }

  /**
   * Writes {@code sum w[i] |sets[i]| + sum v[j] y[j] relation c}.
   *
   * @param model the model
   * @param sets the sets, which are {@link #stated}
   * @param w their weights
   * @param y integer variables
   * @param v their weights
   * @param relation the relation, as in {@link org.jacop.lcg.LinearForm}
   * @param c the right-hand side
   */
  static void cardinalities(
      PbModel model, SetVar[] sets, long[] w, IntVar[] y, long[] v, int relation, long c) {
    List<IntVar> x = new ArrayList<>(List.of(y));
    List<Long> weights = new ArrayList<>();
    for (long a : v) {
      weights.add(a);
    }
    long rhs = c;
    for (int i = 0; i < sets.length; i++) {
      SetMirror m = sets[i].lcgMirror();
      if (m == null) {
        rhs -= w[i] * sets[i].domain.glb().getSize();
      } else {
        x.add(m.cardinality());
        weights.add(w[i]);
      }
    }
    long[] a = new long[weights.size()];
    for (int k = 0; k < a.length; k++) {
      a[k] = weights.get(k);
    }
    if (x.isEmpty()) {
      boolean holds =
          switch (relation) {
            case LinearForm.LE -> 0 <= rhs;
            case LinearForm.GE -> 0 >= rhs;
            case LinearForm.EQ -> rhs == 0;
            default -> rhs != 0;
          };
      if (!holds) {
        model.clause();
      }
      return;
    }
    IntVar[] vars = x.toArray(new IntVar[0]);
    model.linear(new LinearForm(vars, a, rhs, relation));
    if (vars.length == 2 && Math.abs(a[0]) == 1 && a[1] == -a[0] && vars[0] != vars[1]) {
      // the bounds of one variable give those of the other through clauses, which a line over
      // order literals does not propagate (an equality is channelled by linear itself)
      if (relation == LinearForm.LE) {
        boundClauses(model, a[0] > 0 ? vars[0] : vars[1], a[0] > 0 ? vars[1] : vars[0], rhs);
      }
      if (relation == LinearForm.GE) {
        boundClauses(model, a[0] > 0 ? vars[1] : vars[0], a[0] > 0 ? vars[0] : vars[1], -rhs);
      }
    }
  }

  // y - z <= c: [y >= v] gives [z >= v - c]
  private static void boundClauses(PbModel model, IntVar y, IntVar z, long c) {
    IntDomain d = model.domain(y);
    for (int v = d.min() + 1; v <= d.max(); v++) {
      long u = v - c;
      if (u > Integer.MAX_VALUE || u < Integer.MIN_VALUE) {
        continue;
      }
      model.clause(PbModel.not(model.atLeast(y, v)), model.atLeast(z, (int) u));
    }
  }

  /**
   * Writes a relation on the memberships of every element in sets as its prime implicates, which
   * unit propagation makes arc consistent.
   *
   * @param model the model
   * @param sets the sets, which are {@link #stated}
   * @param relation the relation
   */
  static void elementwise(PbModel model, SetVar[] sets, SetExplanation.Relation relation) {
    for (ValueEnumeration en = lub(sets).valueEnumeration(); en.hasMoreElements(); ) {
      int e = en.nextElement();
      String[] lits = memberships(model, sets, e);
      for (int[] clause : primeImplicates(sets.length, in -> relation.holds(e, in))) {
        model.clause(literals(lits, clause));
      }
    }
  }

  /**
   * Writes under a literal that the relation fails on some element of the sets, with a literal for
   * the failure on each element.
   *
   * @param model the model
   * @param literal the literal
   * @param sets the sets, which are {@link #stated}
   * @param relation the relation
   * @return true
   */
  static boolean violated(
      PbModel model, String literal, SetVar[] sets, SetExplanation.Relation relation) {
    List<String> some = new ArrayList<>();
    for (ValueEnumeration en = lub(sets).valueEnumeration(); en.hasMoreElements(); ) {
      int e = en.nextElement();
      String[] lits = memberships(model, sets, e);
      List<int[]> violation = primeImplicates(sets.length, in -> !relation.holds(e, in));
      String fails = model.auxiliary();
      // fails is the violation itself, so a logged solution fixes it by unit propagation
      for (int[] clause : primeImplicates(sets.length, in -> relation.holds(e, in))) {
        String[] c = literals(lits, clause);
        String[] withFails = Arrays.copyOf(c, c.length + 1);
        withFails[c.length] = fails;
        model.clause(withFails);
      }
      model.implied(
          fails,
          () -> {
            for (int[] clause : violation) {
              model.clause(literals(lits, clause));
            }
            return true;
          });
      some.add(fails);
    }
    return model.implied(
        literal,
        () -> {
          model.clause(some.toArray(new String[0]));
          return true;
        });
  }

  private static String[] memberships(PbModel model, SetVar[] sets, int e) {
    String[] lits = new String[sets.length];
    for (int i = 0; i < sets.length; i++) {
      lits[i] = in(model, sets[i], e);
    }
    return lits;
  }

  // the literals of a clause, coded 1 for a membership and -1 for its negation
  private static String[] literals(String[] lits, int[] clause) {
    List<String> out = new ArrayList<>();
    for (int i = 0; i < clause.length; i++) {
      if (clause[i] != 0) {
        String l = clause[i] > 0 ? lits[i] : PbModel.not(lits[i]);
        if (!"0".equals(l)) {
          out.add(l);
        }
      }
    }
    return out.toArray(new String[0]);
  }

  /*
   * The prime implicates of a relation on k memberships, each a clause coded 1, -1 or 0 (absent)
   * per membership: the clauses every satisfying assignment satisfies, with no implied clause of
   * fewer literals.
   */
  private static List<int[]> primeImplicates(int k, Predicate<boolean[]> holds) {
    int clauses = 1;
    for (int i = 0; i < k; i++) {
      clauses *= 3;
    }
    boolean[] implied = new boolean[clauses];
    for (int code = 0; code < clauses; code++) {
      implied[code] = implied(decode(code, k), holds);
    }
    List<int[]> primes = new ArrayList<>();
    for (int code = 0; code < clauses; code++) {
      if (!implied[code]) {
        continue;
      }
      int[] clause = decode(code, k);
      boolean prime = true;
      for (int i = 0; i < k && prime; i++) {
        if (clause[i] != 0) {
          int[] smaller = clause.clone();
          smaller[i] = 0;
          prime = !implied[encode(smaller)];
        }
      }
      if (prime) {
        primes.add(clause);
      }
    }
    return primes;
  }

  private static boolean implied(int[] clause, Predicate<boolean[]> holds) {
    int k = clause.length;
    boolean[] in = new boolean[k];
    for (int assignment = 0; assignment < 1 << k; assignment++) {
      boolean satisfied = false;
      for (int i = 0; i < k; i++) {
        in[i] = (assignment >> i & 1) == 1;
        satisfied |= clause[i] == 1 && in[i] || clause[i] == -1 && !in[i];
      }
      if (!satisfied && holds.test(in.clone())) {
        return false;
      }
    }
    return true;
  }

  private static int[] decode(int code, int k) {
    int[] clause = new int[k];
    int c = code;
    for (int i = 0; i < k; i++) {
      clause[i] = c % 3 == 2 ? -1 : c % 3;
      c /= 3;
    }
    return clause;
  }

  private static int encode(int[] clause) {
    int code = 0;
    for (int i = clause.length - 1; i >= 0; i--) {
      code = code * 3 + (clause[i] == -1 ? 2 : clause[i]);
    }
    return code;
  }
}
