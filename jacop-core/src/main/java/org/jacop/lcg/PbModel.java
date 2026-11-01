/*
 * PbModel.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.lcg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;

/**
 * The pseudo-Boolean model that {@link PbEncodable} constraints write to. Each integer variable
 * stands for its order literals {@code [x >= v]} and value literals {@code [x = v]}, so a
 * constraint is stated over the variables themselves.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface PbModel {

  /**
   * Adds a linear relation.
   *
   * @param form the relation
   */
  void linear(LinearForm form);

  /**
   * Adds a linear relation that holds when a 0/1 variable is 1 and, for an equivalence, whose
   * negation holds when it is 0.
   *
   * @param b the 0/1 variable
   * @param form the relation
   * @param equivalence true for b = 1 if and only if the relation holds, false for an implication
   */
  void reified(IntVar b, LinearForm form, boolean equivalence);

  /**
   * Adds a linear relation that holds when a literal is true.
   *
   * @param literal a literal of {@link #equalTo}, {@link #atLeast} or {@link #auxiliary}, or "1" or
   *     "0"
   * @param form the relation, one of LE, GE and EQ
   */
  void guarded(String literal, LinearForm form);

  /**
   * Adds a clause over 0/1 variables: one of the positive ones is 1 or one of the negative ones is
   * 0.
   *
   * @param positive the variables of which one may be 1
   * @param negative the variables of which one may be 0
   */
  void clause(IntVar[] positive, IntVar[] negative);

  /**
   * Returns the domain of a variable in the model, which its literals cover.
   *
   * @param x the variable
   * @return its root domain
   */
  IntDomain domain(IntVar x);

  /**
   * Returns the literal {@code [x = v]}: its name, or "1" or "0" when the root domain of x decides
   * it.
   *
   * @param x the variable
   * @param v the value
   * @return the literal
   */
  String equalTo(IntVar x, int v);

  /**
   * Returns the literal {@code [x >= v]}: its name, or "1" or "0" when the root domain of x decides
   * it.
   *
   * @param x the variable
   * @param v the value
   * @return the literal
   */
  String atLeast(IntVar x, int v);

  /**
   * Returns a new literal of the model alone, which no variable of the store stands for.
   *
   * @return its name
   */
  String auxiliary();

  /**
   * Adds a clause over literals of {@link #equal} and {@link #atLeast}, each one negated by {@link
   * #not}; a literal "1" makes the clause true and a literal "0" is left out.
   *
   * @param literals the literals of which one is true
   */
  void clause(String... literals);

  /**
   * Adds the relation {@code sum a[k] * literal[k] + sum w[j] * x[j] relation c}, for a relation
   * {@link LinearForm#LE}, {@link LinearForm#GE} or {@link LinearForm#EQ}.
   *
   * @param literals literals of {@link #equal} and {@link #atLeast}
   * @param a their coefficients
   * @param x integer variables
   * @param w their weights
   * @param relation the relation
   * @param c the right hand side
   */
  void sum(String[] literals, long[] a, IntVar[] x, long[] w, int relation, long c);

  /**
   * Adds that the variables take different values: at most one of them takes each value. The solver
   * writes the counting steps that the explanations of such a constraint need.
   *
   * @param x the variables, all different objects
   */
  void allDifferent(IntVar[] x);

  /**
   * Adds that counters[k] of the variables take values[k] (between low[k] and up[k] when
   * counters[k] is null), and that they take counted values only when closed. The solver writes the
   * counting steps that the flow explanations of such a constraint need.
   *
   * @param x the counted variables, all different objects
   * @param values the counted values, increasing
   * @param counters the counter of each value, none of them among x, or null entries
   * @param low the lower bound of each value without a counter, or null
   * @param up the upper bound of each value without a counter, or null
   * @param closed whether the variables take counted values only
   * @param rest the number of variables taking no counted value, or null
   */
  void cardinality(
      IntVar[] x,
      int[] values,
      IntVar[] counters,
      int[] low,
      int[] up,
      boolean closed,
      IntVar rest);

  /**
   * Adds {@code (number of x[i] = value) - sum y[j] relation c}: the counting constraints.
   *
   * @param model the model
   * @param x the counted variables
   * @param value the counted value
   * @param y variables subtracted from the count
   * @param relation the relation, as in {@link #sum}
   * @param c the right hand side
   */
  static void count(PbModel model, IntVar[] x, int value, IntVar[] y, int relation, long c) {
    String[] l = new String[x.length];
    long[] a = new long[x.length];
    for (int i = 0; i < x.length; i++) {
      l[i] = model.equalTo(x[i], value);
      a[i] = 1;
    }
    long[] w = new long[y.length];
    Arrays.fill(w, -1);
    model.sum(l, a, y, w, relation, c);
  }

  /**
   * Adds that the variables take one of the tuples, by the support encoding: a literal per tuple
   * that implies its values, a clause per value of each variable that some tuple with it holds, and
   * one that some tuple holds. Unit propagation over it reaches domain consistency.
   *
   * @param model the model
   * @param x the variables
   * @param tuples the allowed tuples, each a value per variable within its root domain
   */
  static void table(PbModel model, IntVar[] x, List<int[]> tuples) {
    String[] some = new String[tuples.size()];
    List<Map<Integer, List<String>>> support = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      support.add(new HashMap<>());
    }
    for (int t = 0; t < tuples.size(); t++) {
      String lit = model.auxiliary();
      some[t] = lit;
      for (int i = 0; i < x.length; i++) {
        int v = tuples.get(t)[i];
        model.clause(not(lit), model.equalTo(x[i], v));
        support.get(i).computeIfAbsent(v, k -> new ArrayList<>()).add(lit);
      }
    }
    model.clause(some);
    for (int i = 0; i < x.length; i++) {
      IntDomain d = model.domain(x[i]);
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        List<String> s = support.get(i).getOrDefault(v, List.of());
        String[] c = new String[s.size() + 1];
        c[0] = not(model.equalTo(x[i], v));
        for (int k = 0; k < s.size(); k++) {
          c[k + 1] = s.get(k);
        }
        model.clause(c);
      }
    }
  }

  /**
   * Returns the negation of a literal.
   *
   * @param literal a literal of {@link #equal} or {@link #atLeast}, or "1" or "0"
   * @return its negation
   */
  static String not(String literal) {
    return switch (literal) {
      case "0" -> "1";
      case "1" -> "0";
      default -> literal.startsWith("~") ? literal.substring(1) : "~" + literal;
    };
  }
}
