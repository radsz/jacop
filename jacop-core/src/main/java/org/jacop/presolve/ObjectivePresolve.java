/*
 * ObjectivePresolve.java
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Objective presolve: a linear objective is rewritten so that its bounds see the exactly-one
 * structure of the model, and the rewritten objective is returned as a redundant linear equation.
 *
 * <p>Two steps, after CP-SAT's {@code ExpandObjective} and {@code ShiftObjectiveWithExactlyOnes}:
 *
 * <ol>
 *   <li><b>Expansion.</b> Starting from the equation that defines the objective variable, every
 *       variable of the expression that is defined by a linear equation with coefficient +1 or -1
 *       is replaced by its definition, so the objective becomes one sum over the variables the
 *       costs really depend on. A count {@code n = count(x, v)} defines n as the sum of the value
 *       literals {@code x[i] = v} when every x[i] that can take v has one. An element {@code y =
 *       c[x]} of constants defines y as {@code sum(c_v * (x = v))} when every value v of x has a
 *       literal, and a disjunction {@code r <-> or(b)} of literals of which at most one can be 1
 *       (literals of one variable, or literals of one value for variables that are all different)
 *       defines r as {@code sum(b)}. A variable without a definition of its own is replaced by an
 *       equal variable that has one ({@code bool2int}, {@code bool_eq}, or a 0/1 variable x and the
 *       literal of x = 1).
 *   <li><b>Shifting.</b> For a set of 0/1 variables of which exactly one is 1 (a linear equation
 *       {@code sum(b) = 1}, or the literals {@code b_v <-> x = v} for every value v of a variable
 *       x), {@code sum(c_v * b_v) = m + sum((c_v - m) * b_v)} with m the smallest cost of the set
 *       (the largest when maximising). Bounds reasoning on the sum sees the 0/1 variables
 *       separately, so before the shift it takes the cost of the set at least {@code min(0, sum of
 *       negative c_v)}; after it at least m.
 * </ol>
 *
 * <p>The equation {@code objective = expanded and shifted expression} holds in every solution of
 * the model, since it is derived from the model's own equations, so imposing it keeps every
 * solution; it is useful with all solutions and with counting too. It is returned only when
 * shifting tightens the bound of the expression in the direction of optimisation. With the other
 * equations, exactly-one sets and counts it is equivalent to the equation defining the objective,
 * so the caller may drop that one ({@link #definitionVariables()}).
 *
 * <p>All variables are read at their current domains, which should be at a fixpoint.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class ObjectivePresolve implements Rule {

  /** Largest number of terms an expanded objective may have. */
  static final int MAX_TERMS = 100_000;

  /** Largest domain of a variable whose value literals form an exactly-one set. */
  static final int MAX_ENCODED_DOMAIN = 100_000;

  /** Largest span of a variable given a cost variable through an element constraint. */
  static final int MAX_COST_TABLE = 10_000;

  /** An equation {@code sum(coefs[i] * vars[i]) = rhs}; compared by identity. */
  private static final class Equation {
    private final IntVar[] vars;
    private final int[] coefs;
    private final int rhs;

    Equation(IntVar[] vars, int[] coefs, int rhs) {
      this.vars = vars;
      this.coefs = coefs;
      this.rhs = rhs;
    }

    IntVar[] vars() {
      return vars;
    }

    int[] coefs() {
      return coefs;
    }

    int rhs() {
      return rhs;
    }
  }

  private final IntVar objective;
  private final boolean minimize;

  private final List<Equation> equations = new ArrayList<>();
  private final Map<IntVar, Equation> definitions = new IdentityHashMap<>();
  private final List<IntVar[]> exactlyOnes = new ArrayList<>();
  private final Map<IntVar, Map<Integer, IntVar>> encodings = new LinkedHashMap<>();
  private final List<Count> counts = new ArrayList<>();
  private final List<Element> elements = new ArrayList<>();
  private final List<Or> ors = new ArrayList<>();
  private final List<IntVar[]> allDifferents = new ArrayList<>();
  private final Map<IntVar, List<IntVar>> equals = new IdentityHashMap<>();

  /**
   * An element {@code y = values[x - firstIndex]}, turned into an equation once all literals are
   * known.
   */
  private static final class Element {
    private final IntVar x;
    private final int[] values;
    private final int firstIndex;
    private final IntVar y;

    Element(IntVar x, int[] values, int firstIndex, IntVar y) {
      this.x = x;
      this.values = values.clone();
      this.firstIndex = firstIndex;
      this.y = y;
    }
  }

  /** A disjunction {@code r <-> or(literals)}. */
  private static final class Or {
    private final IntVar r;
    private final IntVar[] literals;

    Or(IntVar r, IntVar[] literals) {
      this.r = r;
      this.literals = literals.clone();
    }
  }

  /** A count {@code n = count(x, value)}, turned into an equation once all literals are known. */
  private static final class Count {
    private final IntVar[] x;
    private final int value;
    private final IntVar n;

    Count(IntVar[] x, int value, IntVar n) {
      this.x = x.clone();
      this.value = value;
      this.n = n;
    }
  }

  private int expanded;
  private int shifted;
  private LinearInt imposed;
  private IntVar[] definitionVariables;
  private final List<IntVar> costVariables = new ArrayList<>();

  /**
   * Starts an objective presolve.
   *
   * @param objective the variable of the objective.
   * @param minimize true when the objective is minimised, false when it is maximised.
   */
  public ObjectivePresolve(IntVar objective, boolean minimize) {
    this.objective = objective;
    this.minimize = minimize;
  }

  /**
   * Adds an equation {@code sum(coefs[i] * vars[i]) = rhs} that holds in every solution of the
   * model.
   *
   * @param vars the variables; a variable may occur more than once and may be fixed.
   * @param coefs the coefficients.
   * @param rhs the right-hand side.
   * @param defined the variable the equation defines (FlatZinc's {@code defines_var}), or null. A
   *     defined variable with coefficient +1 or -1 is replaced by the rest of the equation when the
   *     objective is expanded.
   */
  public void addEquation(IntVar[] vars, int[] coefs, int rhs, IntVar defined) {
    if (vars.length != coefs.length) {
      throw new IllegalArgumentException("vars and coefs differ in length");
    }
    Equation e = new Equation(vars.clone(), coefs.clone(), rhs);
    equations.add(e);
    if (defined != null && Math.abs(coefficient(e, defined)) == 1) {
      definitions.putIfAbsent(defined, e);
    }
    if (Math.abs(rhs) == 1 && vars.length > 1) {
      boolean unit = true;
      for (int i = 0; i < vars.length && unit; i++) {
        unit = coefs[i] == rhs && vars[i].min() >= 0 && vars[i].max() <= 1;
      }
      if (unit) {
        exactlyOnes.add(vars.clone());
      }
    }
  }

  /**
   * Adds a value literal: {@code literal <-> x = value} holds in every solution of the model. When
   * every value of x has a literal, the literals of x form an exactly-one set.
   *
   * @param x the variable.
   * @param value the value.
   * @param literal the 0/1 variable that is 1 exactly when x takes the value.
   */
  public void addValueLiteral(IntVar x, int value, IntVar literal) {
    encodings.computeIfAbsent(x, k -> new LinkedHashMap<>()).putIfAbsent(value, literal);
    if (value == 1 && x.min() >= 0 && x.max() <= 1) {
      // a 0/1 variable is its own literal of the value 1
      addEquality(x, literal);
    }
  }

  /**
   * Adds an equality: {@code a = b} holds in every solution of the model. A variable of the
   * objective without a definition of its own is replaced by an equal variable that has one.
   *
   * @param a the first variable.
   * @param b the second variable.
   */
  public void addEquality(IntVar a, IntVar b) {
    if (a != b) {
      equals.computeIfAbsent(a, k -> new ArrayList<>()).add(b);
      equals.computeIfAbsent(b, k -> new ArrayList<>()).add(a);
    }
  }

  /**
   * Adds an element constraint {@code y = values[x - firstIndex]} of constants. When every value of
   * x has a value literal, it becomes the equation {@code y = sum(values[v - firstIndex] * (x =
   * v))} that defines y, unless another equation defines y already.
   *
   * @param x the index variable.
   * @param values the constants.
   * @param firstIndex the index of the first constant.
   * @param y the value variable.
   */
  public void addElement(IntVar x, int[] values, int firstIndex, IntVar y) {
    elements.add(new Element(x, values, firstIndex, y));
  }

  /**
   * Adds a disjunction {@code r <-> or(literals)} of 0/1 variables. When at most one of the
   * literals can be 1, it becomes the equation {@code r = sum(literals)} that defines r, unless
   * another equation defines r already. Literals that exclude each other are value literals of one
   * variable for different values, or of one value for different variables of an all-different
   * constraint ({@link #addAllDifferent(IntVar[])}).
   *
   * @param r the 0/1 variable that is 1 exactly when one of the literals is.
   * @param literals the literals.
   */
  public void addOr(IntVar r, IntVar[] literals) {
    ors.add(new Or(r, literals));
  }

  /**
   * Adds an all-different constraint: the variables take different values in every solution.
   *
   * @param x the variables.
   */
  public void addAllDifferent(IntVar[] x) {
    allDifferents.add(x.clone());
  }

  /**
   * Adds a count: {@code n} is the number of variables of x that take the value. When every
   * variable of x that can take the value has a value literal for it, the count becomes the
   * equation {@code n = sum(literals)} that defines n, unless another equation defines n already.
   *
   * @param x the counted variables; a variable may occur more than once.
   * @param value the counted value.
   * @param n the number of variables of x equal to the value.
   */
  public void addCount(IntVar[] x, int value, IntVar n) {
    counts.add(new Count(x, value, n));
  }

  /**
   * Returns the number of variables replaced by their definitions in the last {@link
   * #reformulate()}.
   *
   * @return the number of substitutions.
   */
  public int expanded() {
    return expanded;
  }

  /**
   * Returns the number of exactly-one sets shifted in the last {@link #reformulate()}.
   *
   * @return the number of shifts.
   */
  public int shifted() {
    return shifted;
  }

  /**
   * As a presolve rule, imposes the equation of {@link #reformulate()} once, in the first round in
   * which there is one; the domains narrowed by earlier rounds can complete a value encoding.
   *
   * @param context the derivation in progress.
   */
  @Override
  public void apply(Context context) {
    if (imposed == null) {
      imposed = reformulate();
      if (imposed != null) {
        context.impose(imposed);
      }
    }
  }

  /**
   * Returns the equation imposed by {@link #apply(Context)}.
   *
   * @return the equation, or null if the rule imposed none.
   */
  public LinearInt imposed() {
    return imposed;
  }

  /**
   * Returns the objective variable.
   *
   * @return the objective.
   */
  public IntVar objective() {
    return objective;
  }

  /**
   * Returns true when the objective is minimised.
   *
   * @return true for minimisation, false for maximisation.
   */
  public boolean minimize() {
    return minimize;
  }

  /**
   * Returns the cost variables made by the last {@link #reformulate(Store)}, one per variable
   * encoded by value literals with costs, in the order of the variables.
   *
   * @return the cost variables, empty if none were made.
   */
  public List<IntVar> costVariables() {
    return List.copyOf(costVariables);
  }

  /**
   * Returns the variables of the equation that defines the objective, as used by the last {@link
   * #reformulate()}. The reformulated equation, with the other equations, exactly-one sets and
   * counts of the model, implies this one, so a constraint posting it can be replaced by the
   * reformulated equation.
   *
   * @return the variables of the defining equation, or null if there is none.
   */
  public IntVar[] definitionVariables() {
    return definitionVariables == null ? null : definitionVariables.clone();
  }

  /**
   * Expands and shifts the objective.
   *
   * @return the equation {@code objective = expression} as a constraint to impose, or null if the
   *     objective has no linear definition or shifting does not tighten its bound.
   */
  public LinearInt reformulate() {
    return reformulate(null, null);
  }

  /**
   * Expands and shifts the objective, and gives each variable whose value literals carry costs a
   * cost variable: the terms {@code sum(c_v * (x = v))} of x become one variable {@code y = c[x]},
   * posed as an element constraint. The bound of the equation is the same, but bounds reasoning and
   * explanations of lazy clause generation see one cost per variable, not one 0/1 term per value.
   *
   * @param store the store of the cost variables.
   * @return the element constraints of the cost variables followed by the equation {@code objective
   *     = expression}, or an empty list if the objective has no linear definition or shifting does
   *     not tighten its bound.
   */
  public List<Constraint> reformulate(Store store) {
    List<Constraint> constraints = new ArrayList<>();
    LinearInt equation = reformulate(store, constraints);
    if (equation == null) {
      return List.of();
    }
    constraints.add(equation);
    return constraints;
  }

  private LinearInt reformulate(Store store, List<Constraint> elements) {
    expanded = 0;
    shifted = 0;
    definitionVariables = null;
    costVariables.clear();
    if (objective.singleton()) {
      return null;
    }
    addCountEquations();
    addElementEquations();
    addOrEquations();
    Equation definition = objectiveDefinition();
    if (definition == null) {
      return null;
    }
    definitionVariables = definition.vars().clone();

    // objective = constant + sum(expression)
    Map<IntVar, Long> expression = new LinkedHashMap<>();
    long[] constant = {0};
    long k = coefficient(definition, objective);
    // k * objective + rest = rhs, so objective = k * rhs - k * rest as k is +1 or -1
    if (!add(expression, constant, definition, objective, -k)) {
      return null;
    }
    constant[0] += k * definition.rhs();

    if (!expand(expression, constant)) {
      return null;
    }

    try {
      long before = bound(expression, constant[0]);
      for (IntVar[] set : exactlyOneSets()) {
        shift(expression, constant, set);
      }
      long after = bound(expression, constant[0]);
      if (shifted == 0 || (minimize ? after <= before : after >= before)) {
        return null;
      }
    } catch (ArithmeticException overflow) {
      return null;
    }
    if (store != null) {
      costVariables(expression, store, elements);
    }
    return equation(expression, constant[0]);
  }

  /**
   * Replaces the cost terms of the value literals of each encoded variable x by a cost variable y
   * and the constraint {@code y = c[x]}. Exactly one literal of x is 1, so {@code sum(c_v * (x =
   * v)) = c[x]}.
   */
  private void costVariables(Map<IntVar, Long> expression, Store store, List<Constraint> elements) {
    for (Map.Entry<IntVar, Map<Integer, IntVar>> e : encodings.entrySet()) {
      IntVar x = e.getKey();
      IntVar[] literals = literals(x, e.getValue());
      if (literals.length == 0 || (long) x.max() - x.min() + 1 > MAX_COST_TABLE) {
        continue;
      }
      int[] costs = new int[x.max() - x.min() + 1];
      IntDomain values = new IntervalDomain();
      Map<IntVar, Boolean> seen = new IdentityHashMap<>();
      boolean distinct = true;
      boolean fits = true;
      int i = 0;
      for (ValueEnumeration v = x.dom().valueEnumeration(); v.hasMoreElements(); i++) {
        int value = v.nextElement();
        IntVar b = literals[i];
        long c = expression.getOrDefault(b, 0L);
        distinct &= b != x && seen.put(b, Boolean.TRUE) == null;
        fits &= c >= IntDomain.MIN_INT && c <= IntDomain.MAX_INT;
        if (fits) {
          costs[value - x.min()] = (int) c;
          values.unionAdapt((int) c, (int) c);
        }
      }
      // a literal shared by two values, or x as its own literal, cannot be replaced, and a
      // constant cost needs no variable
      if (!distinct || !fits || values.getSize() < 2) {
        continue;
      }
      IntVar y = new IntVar(store, values);
      for (IntVar b : literals) {
        expression.remove(b);
      }
      expression.put(y, 1L);
      costVariables.add(y);
      elements.add(new ElementInteger(x, costs, y, x.min() - 1));
    }
  }

  /** Adds the equation {@code n - sum(literals) = constant} of each count that has all literals. */
  private void addCountEquations() {
    for (Count c : counts) {
      if (definitions.containsKey(c.n) || c.n.singleton()) {
        continue;
      }
      List<IntVar> literals = new ArrayList<>();
      int fixed = 0;
      boolean complete = true;
      for (int i = 0; i < c.x.length && complete; i++) {
        IntVar xi = c.x[i];
        if (xi.singleton(c.value)) {
          fixed++;
        } else if (xi.domain.contains(c.value)) {
          Map<Integer, IntVar> lits = encodings.get(xi);
          IntVar b = lits == null ? null : lits.get(c.value);
          complete = b != null && b != c.n && b.min() >= 0 && b.max() <= 1;
          literals.add(b);
        }
      }
      if (!complete || literals.size() + 1 > MAX_TERMS) {
        continue;
      }
      // n - sum(b) = fixed
      IntVar[] vars = new IntVar[literals.size() + 1];
      int[] coefs = new int[vars.length];
      vars[0] = c.n;
      coefs[0] = 1;
      for (int i = 0; i < literals.size(); i++) {
        vars[i + 1] = literals.get(i);
        coefs[i + 1] = -1;
      }
      addEquation(vars, coefs, fixed, c.n);
    }
    counts.clear();
  }

  /**
   * Adds the equation {@code y - sum(c_v * literal_v) = 0} of each element that has all literals.
   */
  private void addElementEquations() {
    for (Element e : elements) {
      if (definitions.containsKey(e.y) || e.y.singleton() || e.x.singleton()) {
        continue;
      }
      Map<Integer, IntVar> byValue = encodings.get(e.x);
      IntVar[] literals = byValue == null ? new IntVar[0] : literals(e.x, byValue);
      if (literals.length == 0 || literals.length + 1 > MAX_TERMS) {
        continue;
      }
      IntVar[] vars = new IntVar[literals.length + 1];
      int[] coefs = new int[vars.length];
      vars[0] = e.y;
      coefs[0] = 1;
      boolean inside = true;
      int i = 0;
      for (ValueEnumeration v = e.x.dom().valueEnumeration(); v.hasMoreElements() && inside; i++) {
        long index = (long) v.nextElement() - e.firstIndex;
        inside = index >= 0 && index < e.values.length && literals[i] != e.y;
        if (inside) {
          vars[i + 1] = literals[i];
          coefs[i + 1] = -e.values[(int) index];
        }
      }
      if (inside) {
        addEquation(vars, coefs, 0, e.y);
      }
    }
    elements.clear();
  }

  /** Adds the equation {@code r - sum(literals) = 0} of each disjunction of exclusive literals. */
  private void addOrEquations() {
    Map<IntVar, IntVar> variableOf = new IdentityHashMap<>();
    Map<IntVar, Integer> valueOf = new IdentityHashMap<>();
    for (Map.Entry<IntVar, Map<Integer, IntVar>> e : encodings.entrySet()) {
      for (Map.Entry<Integer, IntVar> lit : e.getValue().entrySet()) {
        if (variableOf.putIfAbsent(lit.getValue(), e.getKey()) == null) {
          valueOf.put(lit.getValue(), lit.getKey());
        }
      }
    }
    Map<IntVar, List<Integer>> groupsOf = new IdentityHashMap<>();
    for (int g = 0; g < allDifferents.size(); g++) {
      for (IntVar x : allDifferents.get(g)) {
        List<Integer> groups = groupsOf.computeIfAbsent(x, k -> new ArrayList<>());
        if (groups.isEmpty() || groups.getLast() != g) {
          groups.add(g);
        }
      }
    }
    for (Or or : ors) {
      if (definitions.containsKey(or.r)
          || or.r.singleton()
          || or.literals.length < 2
          || or.literals.length + 1 > MAX_TERMS
          || !exclusive(or, variableOf, valueOf, groupsOf)) {
        continue;
      }
      IntVar[] vars = new IntVar[or.literals.length + 1];
      int[] coefs = new int[vars.length];
      vars[0] = or.r;
      coefs[0] = 1;
      for (int i = 0; i < or.literals.length; i++) {
        vars[i + 1] = or.literals[i];
        coefs[i + 1] = -1;
      }
      addEquation(vars, coefs, 0, or.r);
    }
    ors.clear();
  }

  /**
   * True if the literals of the disjunction are distinct 0/1 variables and at most one can be 1.
   */
  private static boolean exclusive(
      Or or,
      Map<IntVar, IntVar> variableOf,
      Map<IntVar, Integer> valueOf,
      Map<IntVar, List<Integer>> groupsOf) {
    IntVar[] b = or.literals;
    for (int i = 0; i < b.length; i++) {
      IntVar xi = variableOf.get(b[i]);
      if (xi == null || b[i] == or.r || b[i].min() < 0 || b[i].max() > 1) {
        return false;
      }
      for (int j = 0; j < i; j++) {
        IntVar xj = variableOf.get(b[j]);
        boolean sameValue = valueOf.get(b[i]).equals(valueOf.get(b[j]));
        boolean excluded =
            b[i] != b[j] && (xi == xj ? !sameValue : sameValue && allDifferent(xi, xj, groupsOf));
        if (!excluded) {
          return false;
        }
      }
    }
    return true;
  }

  private static boolean allDifferent(IntVar x, IntVar y, Map<IntVar, List<Integer>> groupsOf) {
    List<Integer> gx = groupsOf.get(x);
    List<Integer> gy = groupsOf.get(y);
    if (gx == null || gy == null) {
      return false;
    }
    for (Integer g : gx) {
      if (gy.contains(g)) {
        return true;
      }
    }
    return false;
  }

  private Equation objectiveDefinition() {
    Equation d = definitions.get(objective);
    if (d != null) {
      return d;
    }
    // without a defines_var annotation, the only equation with the objective at coefficient +-1
    for (Equation e : equations) {
      long c = coefficient(e, objective);
      if (c != 0) {
        if (d != null || Math.abs(c) != 1) {
          return null;
        }
        d = e;
      }
    }
    return d;
  }

  private static long coefficient(Equation e, IntVar v) {
    long c = 0;
    for (int i = 0; i < e.vars().length; i++) {
      if (e.vars()[i] == v) {
        c += e.coefs()[i];
      }
    }
    return c;
  }

  /**
   * Adds {@code factor * (equation without the variable skip)} to the expression; fixed variables
   * go to the constant.
   */
  private static boolean add(
      Map<IntVar, Long> expression, long[] constant, Equation e, IntVar skip, long factor) {
    try {
      for (int i = 0; i < e.vars().length; i++) {
        IntVar v = e.vars()[i];
        if (v == skip) {
          continue;
        }
        long c = Math.multiplyExact(factor, (long) e.coefs()[i]);
        if (v.singleton()) {
          constant[0] = Math.addExact(constant[0], Math.multiplyExact(c, (long) v.value()));
        } else {
          long sum = Math.addExact(expression.getOrDefault(v, 0L), c);
          if (sum == 0) {
            expression.remove(v);
          } else {
            expression.put(v, sum);
          }
        }
      }
      return true;
    } catch (ArithmeticException overflow) {
      return false;
    }
  }

  /** Replaces defined variables by their definitions, each definition at most once. */
  private boolean expand(Map<IntVar, Long> expression, long[] constant) {
    Map<Equation, Boolean> used = new IdentityHashMap<>();
    boolean changed = true;
    while (changed) {
      changed = false;
      for (IntVar x : new ArrayList<>(expression.keySet())) {
        IntVar y;
        try {
          y = expandableVariable(expression, x, used);
        } catch (ArithmeticException overflow) {
          return false;
        }
        if (y == null) {
          continue;
        }
        Long cy = expression.get(y);
        if (cy == null) {
          // the equal variable cancelled the term
          changed = true;
          continue;
        }
        Equation d = definitions.get(y);
        if (expression.size() + d.vars().length > MAX_TERMS) {
          return true;
        }
        used.put(d, Boolean.TRUE);
        // ky * y + rest = rhs, so y = ky * rhs - ky * rest
        long ky = coefficient(d, y);
        expression.remove(y);
        try {
          constant[0] =
              Math.addExact(constant[0], Math.multiplyExact(cy, Math.multiplyExact(ky, d.rhs())));
        } catch (ArithmeticException overflow) {
          return false;
        }
        if (!add(expression, constant, d, y, -cy * ky)) {
          return false;
        }
        expanded++;
        changed = true;
      }
    }
    return true;
  }

  /**
   * The variable of the expression to expand for its term x: x itself if its definition is not used
   * yet, otherwise an equal variable with such a definition, which then takes over the term of x.
   * Null if there is none.
   */
  private IntVar expandableVariable(
      Map<IntVar, Long> expression, IntVar x, Map<Equation, Boolean> used) {
    Long cx = expression.get(x);
    if (cx == null) {
      return null;
    }
    if (expandable(definitions.get(x), used)) {
      return x;
    }
    IntVar z = equalWithDefinition(x, used);
    if (z != null) {
      expression.remove(x);
      long sum = Math.addExact(expression.getOrDefault(z, 0L), cx);
      if (sum == 0) {
        expression.remove(z);
      } else {
        expression.put(z, sum);
      }
    }
    return z;
  }

  private boolean expandable(Equation d, Map<Equation, Boolean> used) {
    return d != null && !used.containsKey(d) && coefficient(d, objective) == 0;
  }

  /** A variable equal to y, through a chain of equalities, whose definition is not used yet. */
  private IntVar equalWithDefinition(IntVar y, Map<Equation, Boolean> used) {
    if (!equals.containsKey(y)) {
      return null;
    }
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    List<IntVar> queue = new ArrayList<>();
    queue.add(y);
    seen.put(y, Boolean.TRUE);
    for (int i = 0; i < queue.size(); i++) {
      for (IntVar z : equals.getOrDefault(queue.get(i), List.of())) {
        if (seen.put(z, Boolean.TRUE) == null) {
          if (!z.singleton() && expandable(definitions.get(z), used)) {
            return z;
          }
          queue.add(z);
        }
      }
    }
    return null;
  }

  /** The explicit exactly-one sets, then the value literals of variables encoded on all values. */
  private List<IntVar[]> exactlyOneSets() {
    List<IntVar[]> sets = new ArrayList<>(exactlyOnes);
    for (Map.Entry<IntVar, Map<Integer, IntVar>> e : encodings.entrySet()) {
      IntVar[] literals = literals(e.getKey(), e.getValue());
      if (literals.length > 0) {
        sets.add(literals);
      }
    }
    return sets;
  }

  /**
   * The literals of the values of x in increasing order of the values, or an empty array if x is
   * fixed, its domain is too large or a value has no literal.
   */
  private static IntVar[] literals(IntVar x, Map<Integer, IntVar> byValue) {
    IntDomain d = x.dom();
    if (x.singleton() || d.getSize() > MAX_ENCODED_DOMAIN) {
      return new IntVar[0];
    }
    IntVar[] literals = new IntVar[d.getSize()];
    int i = 0;
    for (ValueEnumeration values = d.valueEnumeration(); values.hasMoreElements(); ) {
      IntVar b = byValue.get(values.nextElement());
      if (b == null) {
        return new IntVar[0];
      }
      literals[i++] = b;
    }
    return literals;
  }

  /**
   * Shifts the costs of an exactly-one set by its smallest cost (largest when maximising); a
   * literal outside the expression has cost 0. Fixed literals are left out: a set with a literal
   * fixed to 1 is skipped, and literals fixed to 0 do not take part.
   */
  private void shift(Map<IntVar, Long> expression, long[] constant, IntVar[] set) {
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    List<IntVar> free = new ArrayList<>();
    for (IntVar b : set) {
      if (b.min() < 0 || b.max() > 1 || seen.put(b, Boolean.TRUE) != null || b.min() == 1) {
        return;
      }
      if (!b.singleton()) {
        free.add(b);
      }
    }
    if (free.size() < 2) {
      return;
    }
    long m = minimize ? Long.MAX_VALUE : Long.MIN_VALUE;
    for (IntVar b : free) {
      long c = expression.getOrDefault(b, 0L);
      m = minimize ? Math.min(m, c) : Math.max(m, c);
    }
    if (m == 0) {
      return;
    }
    try {
      for (IntVar b : free) {
        long c = Math.subtractExact(expression.getOrDefault(b, 0L), m);
        if (c == 0) {
          expression.remove(b);
        } else {
          expression.put(b, c);
        }
      }
      constant[0] = Math.addExact(constant[0], m);
    } catch (ArithmeticException overflow) {
      return;
    }
    shifted++;
  }

  /**
   * The bound of the expression in the direction of optimisation: the minimum or the maximum.
   *
   * @throws ArithmeticException if it does not fit in a long.
   */
  private long bound(Map<IntVar, Long> expression, long constant) {
    long b = constant;
    for (Map.Entry<IntVar, Long> e : expression.entrySet()) {
      long c = e.getValue();
      IntVar v = e.getKey();
      int value = (c > 0) == minimize ? v.min() : v.max();
      b = Math.addExact(b, Math.multiplyExact(c, (long) value));
    }
    return b;
  }

  private LinearInt equation(Map<IntVar, Long> expression, long constant) {
    if (constant < Integer.MIN_VALUE || constant > Integer.MAX_VALUE) {
      return null;
    }
    // objective - sum(c * v) = constant
    IntVar[] vars = new IntVar[expression.size() + 1];
    int[] coefs = new int[vars.length];
    vars[0] = objective;
    coefs[0] = 1;
    int i = 1;
    for (Map.Entry<IntVar, Long> e : expression.entrySet()) {
      long c = -e.getValue();
      if (c < Integer.MIN_VALUE || c > Integer.MAX_VALUE) {
        return null;
      }
      vars[i] = e.getKey();
      coefs[i++] = (int) c;
    }
    return new LinearInt(vars, coefs, "==", (int) constant);
  }
}
