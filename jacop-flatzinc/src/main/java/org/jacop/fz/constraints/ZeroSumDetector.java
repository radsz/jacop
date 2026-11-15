/*
 * ZeroSumDetector.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.SumInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.Options;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Half-reified sums at their least value. A variable {@code s} defined by a sum {@code s = sum(i)
 * a[i] * x[i]} ({@code int_lin_eq}) and used otherwise only in half-reifications {@code b -> s = m}
 * or {@code b -> s <= m}, where {@code m} is the least value of the sum over the domains of x, gets
 * each such half-reification replaced by {@code b -> x[i] = v[i]} for every i, where {@code v[i]}
 * is the bound of x[i] at which its term is least. This is exact: the sum reaches its least value
 * only with every term at its least value. It is the rule of presolvers that a linear constraint at
 * its minimum activity fixes every term at its minimum (CP-SAT, Perron and Didier, OR-Tools {@code
 * cp_model_presolve.cc}), applied under the enforcement literal.
 *
 * <p>XCSP3 translations write {@code or(ne(x, v), eq(aux, 0))} with {@code aux} the sum of the
 * variables around x (SameQueensKnights: "no piece attacks another", one sum per cell and piece):
 * thousands of sums of a hundred terms each, every one woken by each change of every variable it
 * counts. After the rewrite the implications are binary clauses and the sum is dropped: an output
 * variable s gets its value from the terms when a solution is printed (under presolve the sum is
 * kept, woken only when one of its variables is fixed). A variable of the solve item is left as it
 * is.
 *
 * <p>On by default; {@code -Dorg.jacop.fz.zeroSum=false} turns it off. A sum with more than {@code
 * org.jacop.fz.zeroSum.maxTerms} (default 100,000) implications in all is left as it is.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ZeroSumDetector implements ParserTreeConstants {

  private static final int MAX_TERMS = Integer.getInteger("org.jacop.fz.zeroSum.maxTerms", 100_000);

  private static final long MAX_IMPLICATIONS = 20_000_000L;

  private final Support support;

  private final ConstraintFncs fncs;

  private final Set<SimpleNode> frozen;

  private int literals;

  private final Set<IntVar> kept;

  private final Set<IntVar> solveItem;

  /** A sum defining s: its node, the variables, their weights (as s = sum(w * x)) and m. */
  private record Definition(ASTConstElem node, IntVar s, IntVar[] x, int[] w, long least) {}

  /** A half-reification of s: its node, its control and the bound, with eq or le. */
  private record Use(ASTConstElem node, IntVar b, int value) {}

  private final Map<IntVar, Definition> definitions = new LinkedHashMap<>();

  private final Map<IntVar, List<Use>> uses = new IdentityHashMap<>();

  // variables of a definition that occur in some other constraint, or twice in definitions
  private final Set<IntVar> spoiled = Collections.newSetFromMap(new IdentityHashMap<>());

  private final Set<SimpleNode> replaced = new HashSet<>();

  private final Set<Var> dropped = Collections.newSetFromMap(new IdentityHashMap<>());

  private final OutputSums outputs = new OutputSums();

  /**
   * The output variables whose defining sums were dropped, with their terms: their values are
   * computed from the values of the terms when a solution is printed.
   */
  public static final class OutputSums {

    private final List<IntVar> sums = new ArrayList<>();
    private final List<IntVar[]> terms = new ArrayList<>();
    private final List<int[]> weights = new ArrayList<>();

    void add(IntVar s, IntVar[] x, int[] w) {
      sums.add(s);
      terms.add(x);
      weights.add(w);
    }

    /**
     * It tells if there are no variables.
     *
     * @return true if no sum was dropped.
     */
    public boolean isEmpty() {
      return sums.isEmpty();
    }

    /**
     * The variables that the sums define.
     *
     * @return the defined variables.
     */
    public List<IntVar> variables() {
      return Collections.unmodifiableList(sums);
    }

    /**
     * Adds the values of the defined variables in the current solution to the given map. A term
     * whose variable is in the map (eliminated by another reduction) takes its value from there;
     * the other terms are fixed in a solution.
     *
     * @param values the values of variables the model no longer has; the sums are added to it.
     */
    public void addValues(Map<Var, Integer> values) {
      for (int k = 0; k < sums.size(); k++) {
        IntVar[] x = terms.get(k);
        int[] w = weights.get(k);
        long value = 0;
        for (int i = 0; i < x.length; i++) {
          Integer known = values.get(x[i]);
          value += (long) w[i] * (known != null ? known : x[i].min());
        }
        values.put(sums.get(k), (int) value);
      }
    }

    /**
     * A copy over the variables of a copied store.
     *
     * @param map the variable map of the copy.
     * @return the copy.
     */
    public OutputSums copy(VarMap map) {
      OutputSums c = new OutputSums();
      for (int k = 0; k < sums.size(); k++) {
        c.add(map.get(sums.get(k)), map.get(terms.get(k)), weights.get(k));
      }
      return c;
    }
  }

  /**
   * The output variables whose sums were dropped, to be given values when a solution is printed.
   *
   * @return the sums, empty if none was dropped.
   */
  public OutputSums outputSums() {
    return outputs;
  }

  /**
   * It creates the detector.
   *
   * @param support the support of the FlatZinc front end.
   * @param fncs the constraint functions that post the clauses.
   * @param frozen constraint nodes that earlier detectors replaced; their variables count as used.
   * @param kept the output variables and the variables of the solve item.
   * @param solveItem the variables of the solve item.
   */
  public ZeroSumDetector(
      Support support,
      ConstraintFncs fncs,
      Set<SimpleNode> frozen,
      Set<IntVar> kept,
      Set<IntVar> solveItem) {
    this.support = support;
    this.fncs = fncs;
    this.frozen = frozen;
    this.kept = kept;
    this.solveItem = solveItem;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.zeroSum is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.zeroSum"));
  }

  /**
   * The constraint nodes that are not posted: the sums and their half-reifications.
   *
   * @return the replaced nodes.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * The defined variables whose sums were dropped: neither output nor solve item variables.
   *
   * @return the variables left without constraints.
   */
  public Set<Var> unconstrained() {
    return dropped;
  }

  /**
   * It scans the model and posts the implications and the sums.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    List<ASTConstElem> others = new ArrayList<>();
    support.forEachConstraint(
        astTree,
        node -> {
          if (frozen.contains(node) || !(definition(node) || use(node))) {
            others.add(node);
          }
        });
    if (definitions.isEmpty()) {
      return;
    }
    for (ASTConstElem node : others) {
      Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
      for (int k = 0; k < node.jjtGetNumChildren(); k++) {
        variables((SimpleNode) node.jjtGetChild(k), vars);
      }
      spoil(vars);
    }
    // a defined variable may be a control or a term of another definition only if it is spoiled
    Set<IntVar> inner = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Definition d : definitions.values()) {
      Collections.addAll(inner, d.x);
    }
    for (List<Use> us : uses.values()) {
      for (Use u : us) {
        inner.add(u.b);
      }
    }
    spoil(inner);
    long implications = 0;
    int rewritten = 0;
    int controls = 0;
    for (Definition d : definitions.values()) {
      List<Use> us = uses.get(d.s);
      if (spoiled.contains(d.s) || solveItem.contains(d.s) || us == null) {
        continue;
      }
      boolean least = true;
      for (Use u : us) {
        least &= u.value == d.least;
      }
      long more = (long) us.size() * d.x.length;
      if (!least || implications + more > MAX_IMPLICATIONS) {
        continue;
      }
      implications += more;
      rewritten++;
      for (Use u : us) {
        replaced.add(u.node);
        controls++;
        for (int i = 0; i < d.x.length; i++) {
          implication(u.b, d.x[i], d.w[i] > 0 ? d.x[i].min() : d.x[i].max());
        }
      }
      replaced.add(d.node);
      if (kept.contains(d.s) && support.options.presolve() != Options.Presolve.OFF) {
        // presolve may eliminate terms; the sum keeps the value of s right
        support.pose(groundSum(d));
      } else {
        // s is not constrained otherwise: its value follows from the terms when a solution is
        // printed
        dropped.add(d.s);
        if (kept.contains(d.s)) {
          outputs.add(d.s, d.x, d.w);
        }
      }
    }
    if ((support.options.debug() || support.options.searchStatistics()) && rewritten > 0) {
      FzConsole.println(
          "%%%mzn-stat: zeroSums="
              + rewritten
              + "\n%%%mzn-stat: zeroSumControls="
              + controls
              + "\n%%%mzn-stat: zeroSumImplications="
              + implications
              + "\n%%%mzn-stat: zeroSumLiterals="
              + literals);
    }
  }

  // the clause not b \/ (x = v), on x itself when it is 0/1, on the literal of x = v otherwise
  private void implication(IntVar b, IntVar x, int v) {
    if (x.min() >= 0 && x.max() <= 1) {
      if (v == 1) {
        fncs.poseClause(new IntVar[] {x}, new IntVar[] {b});
      } else {
        fncs.poseClause(new IntVar[0], new IntVar[] {b, x});
      }
      return;
    }
    fncs.poseClause(new IntVar[] {literal(x, v)}, new IntVar[] {b});
  }

  // the 0/1 variable of x = v: the one the model reifies, or a new one in the channel of x
  private IntVar literal(IntVar x, int v) {
    Map<Integer, IntVar> values = support.reif.cs.get(x);
    IntVar b = values == null ? null : values.get(v);
    if (b == null) {
      b = new IntVar(support.store, 0, 1);
      support.addReified(x, v, b);
      literals++;
    }
    return b;
  }

  private void spoil(Set<IntVar> vars) {
    for (IntVar v : vars) {
      if (definitions.containsKey(v)) {
        spoiled.add(v);
      }
    }
  }

  // s = sum(w * x), woken only when a variable of x is fixed: s is not constrained otherwise
  private Constraint groundSum(Definition d) {
    boolean unit = true;
    for (int w : d.w) {
      unit &= w == 1;
    }
    Constraint c;
    if (unit) {
      c = new SumInt(d.x, "==", d.s);
    } else {
      IntVar[] vars = new IntVar[d.x.length + 1];
      int[] weights = new int[d.x.length + 1];
      System.arraycopy(d.x, 0, vars, 0, d.x.length);
      System.arraycopy(d.w, 0, weights, 0, d.w.length);
      vars[d.x.length] = d.s;
      weights[d.x.length] = -1;
      c = new LinearInt(vars, weights, "==", 0);
    }
    for (IntVar x : d.x) {
      c.setConsistencyPruningEvent(x, IntDomain.GROUND);
    }
    return c;
  }

  // int_lin_eq(a, x, c) with c = 0, one variable s of weight -1 (or 1 with the others negated)
  private boolean definition(ASTConstElem node) {
    if (!"int_lin_eq".equals(node.getName()) || node.jjtGetNumChildren() < 3) {
      return false;
    }
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (a == null || x == null || a.length != x.length || x.length < 3 || x.length > MAX_TERMS) {
      return false;
    }
    if (support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) != 0) {
      return false;
    }
    // the defined variable: the only one with weight -1 among positive weights, or 1 among
    // negative ones
    int pos = 0;
    int neg = 0;
    for (int w : a) {
      pos += w > 0 ? 1 : 0;
      neg += w < 0 ? 1 : 0;
    }
    int sign = neg == 1 ? 1 : pos == 1 ? -1 : 0;
    if (sign == 0) {
      return false;
    }
    int at = -1;
    for (int k = 0; k < a.length; k++) {
      if (sign * a[k] < 0) {
        at = k;
      }
    }
    if (a[at] != -sign || x[at].singleton()) {
      return false;
    }
    IntVar s = x[at];
    IntVar[] terms = new IntVar[x.length - 1];
    int[] w = new int[x.length - 1];
    Set<IntVar> distinct = Collections.newSetFromMap(new IdentityHashMap<>());
    distinct.add(s);
    long least = 0;
    int t = 0;
    for (int k = 0; k < x.length; k++) {
      if (k == at) {
        continue;
      }
      if (x[k].singleton() || !distinct.add(x[k])) {
        return false;
      }
      terms[t] = x[k];
      w[t] = sign * a[k];
      least += (long) w[t] * (w[t] > 0 ? x[k].min() : x[k].max());
      t++;
    }
    if (least < Integer.MIN_VALUE || least > Integer.MAX_VALUE) {
      return false;
    }
    if (definitions.containsKey(s)) {
      spoiled.add(s);
      return false;
    }
    definitions.put(s, new Definition(node, s, terms, w, least));
    return true;
  }

  // int_eq_imp(s, m, b) or int_le_imp(s, m, b)
  private boolean use(ASTConstElem node) {
    String name = node.getName();
    if (!("int_eq_imp".equals(name) || "int_le_imp".equals(name))
        || node.jjtGetNumChildren() != 3) {
      return false;
    }
    IntVar s = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar m = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (s.singleton() || !m.singleton() || b.singleton() || b == s) {
      return false;
    }
    uses.computeIfAbsent(s, v -> new ArrayList<>()).add(new Use(node, b, m.value()));
    return true;
  }

  // the integer variables of an argument, constants left out
  private void variables(SimpleNode arg, Set<IntVar> out) {
    if (arg.getId() == JJTARRAYLITERAL) {
      for (int i = 0; i < arg.jjtGetNumChildren(); i++) {
        variables((SimpleNode) arg.jjtGetChild(i), out);
      }
      return;
    }
    if (arg.getId() != JJTSCALARFLATEXPR) {
      return;
    }
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) arg;
    if (e.getType() == 2) {
      IntVar[] array = support.dictionary.getVariableArray(e.getIdent());
      if (array != null) {
        Collections.addAll(out, array);
        return;
      }
      IntVar v = support.dictionary.getVariable(e.getIdent());
      if (v != null) {
        out.add(v);
      }
    } else if (e.getType() == 3 && support.dictionary.getVariableArray(e.getIdent()) != null) {
      out.add(support.getVariable(e));
    }
  }
}
