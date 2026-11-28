/*
 * RegularFlowDetector.java
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
import java.util.BitSet;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It finds a regular constraint whose sequence is counted by cardinality constraints over the
 * positions of one residue class each, modulo a period p, and posts the aggregated flow of the
 * automaton over the p classes. The rotating workforce scheduling model of the MiniZinc Challenge
 * (Musliu, Schutt and Stuckey, Solver independent rotating workforce scheduling, CPAIOR 2018) is
 * the case: one regular over the cyclic schedule of all weeks, and a global cardinality per day of
 * the week over the days of that weekday. An instance is infeasible when no week-by-week
 * arrangement exists, and the counts and the automaton together say so long before the search meets
 * it: 2019 Example1370, which CP-SAT proves infeasible in 38 s and JaCoP did not in 600 s, fails at
 * the root with the flow.
 *
 * <p>For a regular over x[0..N-1] with transition function delta, start state q0 and final states
 * F, number the positions from 0 and put position i in class i mod p. The variable f[c][q][s]
 * counts the positions i of class c whose state before x[i] is q and whose value is s; arcs that no
 * position of the class can use (by forward and backward reachability over the domains) are left
 * out. Two sets of linear equalities hold:
 *
 * <ul>
 *   <li>counts: sum over q of f[c][q][s] is the number of positions of class c with value s. A
 *       cardinality constraint over variables that all lie in class c gives its bounds; the
 *       positions of the class that no cardinality constraint covers, and second occurrences of a
 *       covered variable, enter as the literals x[i] = s;
 *   <li>flow: for the boundary between class c and class c' = (c + 1) mod p and each state q, the
 *       arcs of class c that end in q and the arcs of class c' that start in q are equal in number,
 *       except that class 0 also starts once in q0 and that, when N mod p = c', one path ends in
 *       the final state (a variable over F).
 * </ul>
 *
 * <p>Every solution gives the counts of its own state sequence, so the constraints are redundant:
 * an aggregated network flow relaxation of the layered graph of the automaton in the sense of the
 * flow formulations of regular by G. Pesant, A regular language membership constraint for finite
 * sequences of variables, CP 2004, and M.-C. Côté, B. Gendron and L.-M. Rousseau, Modeling the
 * regular constraint with integer programming, CPAIOR 2007, with the layers of one class merged.
 * The new variables are not searched: every assignment of the model's variables that satisfies the
 * regular constraint leaves its own flow feasible.
 *
 * <p>Setting the system property {@code org.jacop.fz.regularFlow} to false turns the detection off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class RegularFlowDetector {

  private static final Set<String> GATE_KINDS = Set.of("jacop_regular");

  // the most flow variables the detector creates for one regular constraint
  static final int MAX_ARCS = 50_000;

  // the least number of positions of a class
  static final int MIN_REPEATS = 3;

  private final Support support;

  private static final class Regular {
    final IntVar[] x;
    final int states;
    final int symbols;
    final int[] d;
    final int q0;
    final IntDomain f;
    final int min;

    Regular(IntVar[] x, int states, int symbols, int[] d, int q0, IntDomain f, int min) {
      this.x = x;
      this.states = states;
      this.symbols = symbols;
      this.d = d;
      this.q0 = q0;
      this.f = f;
      this.min = min;
    }
  }

  private static final class Count {
    final IntVar[] x;
    final int[] values;
    final int[] lb;
    final int[] ub;

    Count(IntVar[] x, int[] values, int[] lb, int[] ub) {
      this.x = x;
      this.values = values;
      this.lb = lb;
      this.ub = ub;
    }
  }

  private final List<Regular> regulars = new ArrayList<>();
  private final List<Count> counts = new ArrayList<>();

  // the literals x = v created here
  private final Map<IntVar, Map<Integer, IntVar>> own = new IdentityHashMap<>();

  private int posted;
  private int variables;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public RegularFlowDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.regularFlow is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.regularFlow"));
  }

  /**
   * It scans the constraint items of the model and posts the aggregated flows. It is called after
   * the constraints of the model are posted.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    // the flows are of regular constraints: a model without them is not read
    if (!support.hasConstraint(astTree, GATE_KINDS)) {
      return;
    }
    support.forEachConstraint(astTree, this::collect);
    if (regulars.isEmpty() || counts.isEmpty()) {
      return;
    }
    for (Regular r : regulars) {
      flow(r);
    }
    if (support.options.debug() && posted > 0) {
      FzConsole.println(
          "% regular flow: " + posted + " regular constraints, " + variables + " flow variables");
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_regular" ->
          regulars.add(
              new Regular(
                  support.getVarArray((SimpleNode) node.jjtGetChild(0)),
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1)),
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)),
                  support.getIntArray((SimpleNode) node.jjtGetChild(3)),
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(4)),
                  support.getSetLiteral(node, 5),
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(6))));
      case "jacop_count_values_bounds" -> {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        int[] values = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[] lb = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        int[] ub = support.getIntArray((SimpleNode) node.jjtGetChild(3));
        if (values != null
            && lb != null
            && ub != null
            && values.length == lb.length
            && values.length == ub.length) {
          counts.add(withoutConstants(x, values, lb, ub));
        }
      }
      default -> {
        // not read
      }
    }
  }

  // the count over the variables of x that are not fixed: a fixed value is counted beforehand
  private static Count withoutConstants(IntVar[] x, int[] values, int[] lb, int[] ub) {
    int[] low = lb.clone();
    int[] up = ub.clone();
    List<IntVar> vars = new ArrayList<>();
    for (IntVar v : x) {
      if (v.singleton()) {
        int k = indexOf(values, v.value());
        if (k >= 0) {
          low[k]--;
          up[k]--;
        }
      } else {
        vars.add(v);
      }
    }
    return new Count(vars.toArray(new IntVar[0]), values, low, up);
  }

  private static int gcd(int a, int b) {
    while (b != 0) {
      int t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  private void flow(Regular r) {
    IntVar[] x = r.x;
    int n = x.length;
    int states = r.states;
    int symbols = r.symbols;
    if (r.d == null || r.d.length != states * symbols || r.q0 < 1 || r.q0 > states) {
      return;
    }

    Map<IntVar, List<Integer>> positions = new IdentityHashMap<>();
    for (int i = 0; i < n; i++) {
      positions.computeIfAbsent(x[i], k -> new ArrayList<>()).add(i);
    }

    // the cardinality constraints over variables of x only, each variable once, with the gcd of
    // the differences of their positions
    List<Count> groups = new ArrayList<>();
    int period = 0;
    for (Count c : counts) {
      int first = -1;
      int g = 0;
      boolean inside = c.x.length >= 2;
      Map<IntVar, Boolean> seen = new IdentityHashMap<>();
      for (IntVar v : c.x) {
        List<Integer> ps = positions.get(v);
        if (ps == null || seen.put(v, Boolean.TRUE) != null) {
          inside = false;
          break;
        }
        for (int p : ps) {
          if (first < 0) {
            first = p;
          } else {
            g = gcd(g, Math.abs(p - first));
          }
        }
      }
      if (!inside || g < 2) {
        continue;
      }
      groups.add(c);
      period = gcd(period, g);
    }
    if (period < 2 || n < MIN_REPEATS * period) {
      return;
    }

    // the groups of each class, which must not share variables
    List<List<Count>> classGroups = new ArrayList<>();
    for (int c = 0; c < period; c++) {
      classGroups.add(new ArrayList<>());
    }
    Map<IntVar, Count> owner = new IdentityHashMap<>();
    for (Count c : groups) {
      int cls = positions.get(c.x[0]).getFirst() % period;
      boolean free = true;
      for (IntVar v : c.x) {
        if (owner.containsKey(v)) {
          free = false;
          break;
        }
      }
      if (!free) {
        continue;
      }
      for (IntVar v : c.x) {
        owner.put(v, c);
      }
      classGroups.get(cls).add(c);
    }
    for (List<Count> cg : classGroups) {
      if (cg.isEmpty()) {
        // a class without counts: the flow says little
        return;
      }
    }

    // states numbered from 0, -1 the failing state; symbols numbered from 0
    int[][] delta = new int[states][symbols];
    for (int q = 0; q < states; q++) {
      for (int s = 0; s < symbols; s++) {
        delta[q][s] = r.d[q * symbols + s] - 1;
      }
    }
    // allowed symbols at each position
    BitSet[] allowed = new BitSet[n];
    for (int i = 0; i < n; i++) {
      allowed[i] = new BitSet(symbols);
      for (ValueEnumeration e = x[i].domain.valueEnumeration(); e.hasMoreElements(); ) {
        int s = e.nextElement() - r.min;
        if (s >= 0 && s < symbols) {
          allowed[i].set(s);
        }
      }
    }
    // forward[i]: states before position i reachable from q0; backward[i]: states before position
    // i from which a final state is reachable
    BitSet[] forward = new BitSet[n + 1];
    forward[0] = new BitSet(states);
    forward[0].set(r.q0 - 1);
    for (int i = 0; i < n; i++) {
      forward[i + 1] = new BitSet(states);
      for (int q = forward[i].nextSetBit(0); q >= 0; q = forward[i].nextSetBit(q + 1)) {
        for (int s = allowed[i].nextSetBit(0); s >= 0; s = allowed[i].nextSetBit(s + 1)) {
          if (delta[q][s] >= 0) {
            forward[i + 1].set(delta[q][s]);
          }
        }
      }
    }
    BitSet[] backward = new BitSet[n + 1];
    backward[n] = new BitSet(states);
    for (ValueEnumeration e = r.f.valueEnumeration(); e.hasMoreElements(); ) {
      int q = e.nextElement() - 1;
      if (q >= 0 && q < states) {
        backward[n].set(q);
      }
    }
    backward[n].and(forward[n]);
    if (backward[n].isEmpty()) {
      // the regular constraint fails by itself
      return;
    }
    for (int i = n - 1; i >= 0; i--) {
      backward[i] = new BitSet(states);
      for (int q = forward[i].nextSetBit(0); q >= 0; q = forward[i].nextSetBit(q + 1)) {
        for (int s = allowed[i].nextSetBit(0); s >= 0; s = allowed[i].nextSetBit(s + 1)) {
          int t = delta[q][s];
          if (t >= 0 && backward[i + 1].get(t)) {
            backward[i].set(q);
            break;
          }
        }
      }
    }

    // arcs (q, s) of each class with the number of positions that can use them
    List<Map<Long, Integer>> arcs = new ArrayList<>();
    for (int c = 0; c < period; c++) {
      arcs.add(new LinkedHashMap<>());
    }
    int total = 0;
    for (int i = 0; i < n; i++) {
      Map<Long, Integer> a = arcs.get(i % period);
      for (int q = backward[i].nextSetBit(0); q >= 0; q = backward[i].nextSetBit(q + 1)) {
        for (int s = allowed[i].nextSetBit(0); s >= 0; s = allowed[i].nextSetBit(s + 1)) {
          int t = delta[q][s];
          if (t >= 0
              && backward[i + 1].get(t)
              && a.merge(((long) q << 32) | s, 1, Integer::sum) == 1) {
            total++;
          }
        }
      }
    }
    if (total > MAX_ARCS) {
      return;
    }

    // the flow variables
    List<Map<Long, IntVar>> f = new ArrayList<>();
    for (int c = 0; c < period; c++) {
      Map<Long, IntVar> fc = new LinkedHashMap<>();
      for (Map.Entry<Long, Integer> e : arcs.get(c).entrySet()) {
        fc.put(e.getKey(), new IntVar(support.store, 0, e.getValue()));
      }
      f.add(fc);
    }

    // counts per class and value
    for (int c = 0; c < period; c++) {
      Map<Integer, List<IntVar>> bySymbol = new HashMap<>();
      for (Map.Entry<Long, IntVar> e : f.get(c).entrySet()) {
        int s = (int) (e.getKey() & 0xffffffffL);
        bySymbol.computeIfAbsent(s, k -> new ArrayList<>()).add(e.getValue());
      }
      // positions of the class beyond the first occurrence of a covered variable
      List<IntVar> extra = new ArrayList<>();
      for (int i = c; i < n; i += period) {
        if (!owner.containsKey(x[i]) || positions.get(x[i]).getFirst() != i) {
          extra.add(x[i]);
        }
      }
      for (int s = 0; s < symbols; s++) {
        int v = s + r.min;
        List<IntVar> terms = bySymbol.getOrDefault(s, List.of());
        long lo = 0;
        long hi = 0;
        for (Count g : classGroups.get(c)) {
          int k = indexOf(g.values, v);
          if (k >= 0) {
            lo += Math.max(0, g.lb[k]);
            hi += Math.min(g.x.length, g.ub[k]);
          } else {
            hi += g.x.length;
          }
        }
        List<IntVar> vars = new ArrayList<>(terms);
        List<Integer> weights = new ArrayList<>();
        for (int j = 0; j < terms.size(); j++) {
          weights.add(1);
        }
        for (IntVar xi : extra) {
          if (xi.domain.contains(v)) {
            vars.add(literal(xi, v));
            weights.add(-1);
          }
        }
        if (vars.isEmpty()) {
          // no position of the class can take v: the counts fail it by themselves
          continue;
        }
        IntVar[] va = vars.toArray(new IntVar[0]);
        int[] wa = weights.stream().mapToInt(Integer::intValue).toArray();
        if (lo == hi) {
          support.pose(new LinearInt(va, wa, "==", (int) lo));
        } else {
          support.pose(new LinearInt(va, wa, ">=", (int) lo));
          support.pose(new LinearInt(va, wa, "<=", (int) hi));
        }
      }
    }

    // the final state
    IntVar last = null;
    if (backward[n].cardinality() > 1) {
      last = new IntVar(support.store);
      for (int q = backward[n].nextSetBit(0); q >= 0; q = backward[n].nextSetBit(q + 1)) {
        last.addDom(q, q);
      }
    }

    // flow conservation at the boundary between class c and class (c + 1) mod period
    for (int c = 0; c < period; c++) {
      int next = (c + 1) % period;
      Map<Integer, List<IntVar>> in = new HashMap<>();
      for (Map.Entry<Long, IntVar> e : f.get(c).entrySet()) {
        int q = (int) (e.getKey() >>> 32);
        int s = (int) (e.getKey() & 0xffffffffL);
        in.computeIfAbsent(delta[q][s], k -> new ArrayList<>()).add(e.getValue());
      }
      Map<Integer, List<IntVar>> out = new HashMap<>();
      for (Map.Entry<Long, IntVar> e : f.get(next).entrySet()) {
        int q = (int) (e.getKey() >>> 32);
        out.computeIfAbsent(q, k -> new ArrayList<>()).add(e.getValue());
      }
      BitSet all = new BitSet(states);
      in.keySet().forEach(all::set);
      out.keySet().forEach(all::set);
      boolean starts = next == 0;
      boolean ends = n % period == next;
      if (starts) {
        all.set(r.q0 - 1);
      }
      if (ends) {
        all.or(backward[n]);
      }
      for (int q = all.nextSetBit(0); q >= 0; q = all.nextSetBit(q + 1)) {
        // in - out + [start] - [end] = 0
        List<IntVar> vars = new ArrayList<>();
        List<Integer> weights = new ArrayList<>();
        for (IntVar v : in.getOrDefault(q, List.of())) {
          vars.add(v);
          weights.add(1);
        }
        for (IntVar v : out.getOrDefault(q, List.of())) {
          vars.add(v);
          weights.add(-1);
        }
        int rhs = 0;
        if (starts && q == r.q0 - 1) {
          rhs -= 1;
        }
        if (ends && backward[n].get(q)) {
          if (last == null) {
            rhs += 1;
          } else {
            vars.add(literal(last, q));
            weights.add(-1);
          }
        }
        IntVar[] va = vars.toArray(new IntVar[0]);
        int[] wa = weights.stream().mapToInt(Integer::intValue).toArray();
        support.pose(new LinearInt(va, wa, "==", rhs));
      }
    }
    posted++;
    variables += total;
  }

  private static int indexOf(int[] a, int v) {
    for (int i = 0; i < a.length; i++) {
      if (a[i] == v) {
        return i;
      }
    }
    return -1;
  }

  // the literal x = v: the one the model has or a new one
  private IntVar literal(IntVar x, int v) {
    if (x.singleton()) {
      return new IntVar(support.store, x.value() == v ? 1 : 0, x.value() == v ? 1 : 0);
    }
    Map<Integer, IntVar> values = support.reif.cs.get(x);
    IntVar b = values == null ? null : values.get(v);
    if (b != null) {
      return b;
    }
    Map<Integer, IntVar> mine = own.computeIfAbsent(x, k -> new HashMap<>());
    b = mine.get(v);
    if (b == null) {
      b = new IntVar(support.store, 0, 1);
      if (values != null && !values.isEmpty()) {
        support.addReified(x, v, b);
      } else {
        support.pose(support.fzXeqCreified(x, v, b));
      }
      mine.put(v, b);
    }
    return b;
  }
}
