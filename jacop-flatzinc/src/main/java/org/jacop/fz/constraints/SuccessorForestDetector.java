/*
 * SuccessorForestDetector.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.In;
import org.jacop.constraints.Linearizations;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.graph.Forest;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ASTSolveKind;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds successor variables whose arcs are acyclic because positions grow along them, the
 * Miller-Tucker-Zemlin formulation of a path or tour ({@code x[i] = j -> pos[j] = pos[i] + 1}), and
 * posts a redundant {@link Forest} over the arcs, so that the linear relaxation gets the
 * generalized subtour elimination cuts of {@link org.jacop.constraints.lp.TreeCuts}. The relaxation
 * of the model alone is the assignment relaxation, which closes the cheapest subtours: on the
 * prize-collecting path of the MiniZinc Challenge 2016 (instance 32-4-8-2) its bound is 172, and 94
 * with the cuts, for the optimum 92.
 *
 * <p>The candidates are an output array x of n variables and an array pos of n variables that an
 * element constraint indexes, from its first index f: the value f + j of x[i] stands for the arc
 * from node i to node j. Every arc is proved by probing at the root, after all constraints are
 * posted, so the result does not depend on how the model writes the relation:
 *
 * <ul>
 *   <li>an arc i -> j is kept when x[i] = f + j together with pos[j] &lt;= pos[i] fails by
 *       propagation; then pos grows along every selected arc, so the selected arcs have no cycle,
 *       and as each node has one successor they form a forest of the undirected graph;
 *   <li>node j is selected when x[j] takes none of the values that every kept arc into j removes
 *       from it by propagation (a node on the path has a successor or ends the path), nor one that
 *       is not an arc of its own; every kept arc thus has both its nodes selected.
 * </ul>
 *
 * <p>It runs for an optimization only, whose bound the cuts raise, and keeps one forest per
 * successor array, with at least as many arcs as nodes. It is off by default: on 32-4-8-2 the bound
 * after the root cuts is 102.5, yet the proof takes as long (13 s; it takes as long with {@code
 * objective <= 93} posted by hand), as the relaxation in search hits its pivot limit on nearly
 * every call. System property org.jacop.fz.successorForest=true turns it on;
 * org.jacop.fz.successorForestMs (default 1000) limits the time of its probes.
 *
 * <p>References: C. E. Miller, A. W. Tucker and R. A. Zemlin, Integer programming formulation of
 * traveling salesman problems, Journal of the ACM 7(4), 1960; A. Lucena and M. G. C. Resende,
 * Strong lower bounds for the prize collecting Steiner problem in graphs, Discrete Applied
 * Mathematics 141, 2004 (the generalized subtour elimination cuts); M. Fischetti, J. J.
 * Salazar-González and P. Toth, Solving the orienteering problem through branch-and-cut, INFORMS
 * Journal on Computing 10(2), 1998.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class SuccessorForestDetector implements ParserTreeConstants {

  private static final long TIME_MS = Long.getLong("org.jacop.fz.successorForestMs", 1000);

  // the most arcs probed for one pair of arrays
  private static final int MAX_ARCS = 20_000;

  // the arcs probed before a pair with none proved is given up
  private static final int SCREEN = 8;

  private final Support support;
  private final Store store;

  // the element lists by first index
  private final List<IntVar[]> lists = new ArrayList<>();
  private final List<Integer> firsts = new ArrayList<>();
  private boolean optimization;
  private long deadline;

  /** Statistics: the forests posted. */
  public int forests;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public SuccessorForestDetector(Support support) {
    this.support = support;
    this.store = support.store;
  }

  /**
   * It tells if the detection is on. It is off by default: the cuts raise the root bound, but on
   * the prize-collecting instance its proof took as long with them, since the relaxation in search
   * hits its pivot limit (see the class comment).
   *
   * @return true if the system property org.jacop.fz.successorForest is true.
   */
  public static boolean enabled() {
    return Boolean.getBoolean("org.jacop.fz.successorForest");
  }

  /**
   * It finds the successor arrays and posts their forests. The store must be at its root level and
   * consistent; it is consistent again after the forests are posted.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTMODELEND && node.jjtGetNumChildren() > 0) {
        SimpleNode item = (SimpleNode) node.jjtGetChild(0);
        SimpleNode last = (SimpleNode) item.jjtGetChild(item.jjtGetNumChildren() - 1);
        optimization = last instanceof ASTSolveKind kind && !"satisfy".equals(kind.getKind());
      }
    }
    if (!optimization) {
      return;
    }
    support.forEachConstraint(astTree, this::collect);
    if (lists.isEmpty()) {
      return;
    }
    long start = System.nanoTime();
    deadline = start + TIME_MS * 1_000_000;
    // under lazy clause generation the clauses of the model are kept for the SAT solver, outside
    // the store: the probes see them as constraints posted one level up
    List<IntVar[][]> clauses = support.sat.collectedClauses();
    List<Pair> pairs = new ArrayList<>();
    int base = store.level;
    store.setLevel(base + 1);
    try {
      boolean consistent = true;
      try {
        for (IntVar[][] c : clauses) {
          store.impose(new BoolClause(c[0], c[1]));
        }
        consistent = store.consistency();
      } catch (FailException _) {
        store.clearChanged();
        consistent = false;
      }
      if (consistent) {
        pairs = pairs();
      }
    } finally {
      store.removeLevel(base + 1);
      store.setLevel(base);
    }
    for (Pair p : pairs) {
      post(p.x(), p.arcs(), p.removed());
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% successor forests: "
              + forests
              + ", "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
  }

  // a successor array with its proved arcs and the values each node's in-arcs remove; a plain
  // class,
  // not a record, since the arrays are compared by identity
  private static final class Pair {
    private final IntVar[] x;
    private final List<int[]> arcs;
    private final IntDomain[] removed;

    Pair(IntVar[] x, List<int[]> arcs, IntDomain[] removed) {
      this.x = x;
      this.arcs = arcs;
      this.removed = removed;
    }

    IntVar[] x() {
      return x;
    }

    List<int[]> arcs() {
      return arcs;
    }

    IntDomain[] removed() {
      return removed;
    }
  }

  private List<Pair> pairs() {
    List<Pair> found = new ArrayList<>();
    Set<List<Object>> tried = new LinkedHashSet<>();
    for (Var[] array : support.dictionary.outputArrays()) {
      IntVar[] x = intVars(array);
      if (x == null || x.length < 3) {
        continue;
      }
      Pair best = null;
      for (int c = 0; c < lists.size() && System.nanoTime() < deadline; c++) {
        IntVar[] pos = lists.get(c);
        if (pos.length != x.length || Arrays.equals(pos, x)) {
          continue;
        }
        List<Object> key = new ArrayList<>(Arrays.asList(x));
        key.addAll(Arrays.asList(pos));
        key.add(firsts.get(c));
        if (tried.add(key)) {
          Pair p = tryPair(x, pos, firsts.get(c));
          if (p != null && (best == null || p.arcs().size() > best.arcs().size())) {
            best = p;
          }
        }
      }
      // one forest per successor array, and only for a successor structure: at least an arc per
      // node (other pairs of arrays have a few arcs that happen to be ordered, as the loads of
      // cvrp or the times of kidney-exchange, whose cuts only make the relaxation larger)
      if (best != null && best.arcs().size() >= x.length) {
        found.add(best);
      }
    }
    return found;
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "array_var_int_element", "array_var_bool_element" -> list(node, 1);
      case "jacop_array_var_int_element_nonshifted" ->
          list(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      default -> {
        // not an element
      }
    }
  }

  private void list(ASTConstElem node, int first) {
    SimpleNode array = (SimpleNode) node.jjtGetChild(1);
    IntVar[] a = null;
    if (array.getId() == JJTARRAYLITERAL) {
      a = new IntVar[array.jjtGetNumChildren()];
      for (int i = 0; i < a.length; i++) {
        SimpleNode e = (SimpleNode) array.jjtGetChild(i);
        if (!(e instanceof ASTScalarFlatExpr s) || s.getType() != 2) {
          return;
        }
        a[i] = support.getVariable(s);
      }
    } else if (array.getId() == JJTSCALARFLATEXPR && ((ASTScalarFlatExpr) array).getType() == 2) {
      a = support.dictionary.getVariableArray(((ASTScalarFlatExpr) array).getIdent());
    }
    if (a == null || a.length < 3) {
      return;
    }
    for (int k = 0; k < lists.size(); k++) {
      if (firsts.get(k) == first && Arrays.equals(lists.get(k), a)) {
        return;
      }
    }
    lists.add(a);
    firsts.add(first);
  }

  private static IntVar[] intVars(Var[] array) {
    IntVar[] x = new IntVar[array.length];
    for (int i = 0; i < x.length; i++) {
      if (!(array[i] instanceof IntVar v)) {
        return null;
      }
      x[i] = v;
    }
    return x;
  }

  // the arcs of x over the nodes of pos, proved by probing, and their forest when there are any
  private Pair tryPair(IntVar[] x, IntVar[] pos, int first) {
    int n = x.length;
    List<int[]> candidates = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      if (x[i].singleton() || x[i] == pos[i]) {
        continue;
      }
      for (ValueEnumeration e = x[i].dom().valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        long j = (long) v - first;
        if (j >= 0 && j < n && j != i) {
          candidates.add(new int[] {i, (int) j, v});
        }
      }
    }
    if (candidates.size() < 2 || candidates.size() > MAX_ARCS) {
      return null;
    }
    // the values of x[j] that every kept arc into j removes, null before the first such arc
    IntDomain[] removed = new IntDomain[n];
    List<int[]> arcs = new ArrayList<>();
    int level = store.level;
    int probed = 0;
    for (int[] a : candidates) {
      if (System.nanoTime() > deadline) {
        return null;
      }
      if (probed >= SCREEN && arcs.isEmpty()) {
        return null;
      }
      probed++;
      int i = a[0];
      int j = a[1];
      IntDomain left = probe(x[i], a[2], x[j], pos[j], pos[i], level);
      if (left != null) {
        arcs.add(a);
        IntDomain gone = x[j].dom().subtract(left);
        removed[j] = removed[j] == null ? gone : removed[j].intersect(gone);
      }
    }
    if (arcs.size() < 2) {
      return null;
    }
    return new Pair(x, arcs, removed);
  }

  // probes x = v: null when it fails or when pos[j] <= pos[i] does not fail with it; otherwise
  // the domain of head (x[j]) under x = v
  private IntDomain probe(IntVar x, int v, IntVar head, IntVar posJ, IntVar posI, int level) {
    IntDomain left = null;
    store.setLevel(level + 1);
    try {
      x.domain.in(store.level, x, v, v);
      if (store.consistency()) {
        IntDomain headDomain = head.dom().cloneLight();
        store.setLevel(level + 2);
        boolean refuted;
        try {
          store.impose(new XlteqY(posJ, posI));
          refuted = !store.consistency();
        } catch (FailException _) {
          store.clearChanged();
          refuted = true;
        } finally {
          store.removeLevel(level + 2);
          store.setLevel(level + 1);
        }
        left = refuted ? headDomain : null;
      }
    } catch (FailException _) {
      store.clearChanged();
    } finally {
      store.removeLevel(level + 1);
      store.setLevel(level);
    }
    return left;
  }

  // the forest of the arcs; node j is selected when x[j] avoids the values all arcs into j remove
  private void post(IntVar[] x, List<int[]> arcs, IntDomain[] removed) {
    int n = x.length;
    IntDomain[] own = new IntDomain[n];
    for (int[] a : arcs) {
      int i = a[0];
      own[i] = own[i] == null ? new IntervalDomain(a[2], a[2]) : own[i].union(a[2]);
    }
    Collection<Constraint> near = new LinkedHashSet<>();
    for (IntVar v : x) {
      near.addAll(v.dom().constraints());
    }
    Map<IntVar, Map<Integer, IntVar>> given = Linearizations.valueBooleans(near);
    List<Constraint> posted = new ArrayList<>();
    List<IntVar> literals = new ArrayList<>();
    IntVar[] nodes = new IntVar[n];
    for (int j = 0; j < n; j++) {
      // the values that leave j out: all its values that are not arcs of its own when no arc
      // enters j, else those every arc into j removes
      IntDomain out =
          removed[j] == null ? x[j].dom().cloneLight() : removed[j].intersect(x[j].dom());
      if (own[j] != null) {
        out = out.subtract(own[j]);
      }
      if (out.isEmpty()) {
        nodes[j] = new IntVar(store, 1, 1);
      } else if (out.getSize() == x[j].getSize()) {
        nodes[j] = new IntVar(store, 0, 0);
      } else {
        BooleanVar y = new BooleanVar(store);
        literals.add(y);
        nodes[j] = y;
        posted.add(
            out.getSize() == 1
                ? new Reified(new XneqC(x[j], out.min()), y)
                : new Reified(new In(x[j], x[j].dom().subtract(out)), y));
      }
    }
    IntVar[] edges = new IntVar[arcs.size()];
    int[] tail = new int[arcs.size()];
    int[] head = new int[arcs.size()];
    Map<IntVar, List<Integer>> missing = new LinkedHashMap<>();
    for (int e = 0; e < edges.length; e++) {
      int[] a = arcs.get(e);
      tail[e] = a[0];
      head[e] = a[1];
      IntVar b = given.getOrDefault(x[a[0]], Map.of()).get(a[2]);
      if (b == null) {
        missing.computeIfAbsent(x[a[0]], k -> new ArrayList<>()).add(e);
      }
      edges[e] = b;
    }
    for (Map.Entry<IntVar, List<Integer>> m : missing.entrySet()) {
      List<Integer> es = m.getValue();
      IntVar[] bs = new IntVar[es.size()];
      int[] values = new int[es.size()];
      for (int k = 0; k < bs.length; k++) {
        int e = es.get(k);
        bs[k] = new BooleanVar(store);
        values[k] = arcs.get(e)[2];
        edges[e] = bs[k];
        literals.add(bs[k]);
      }
      posted.add(new ChannelReif(m.getKey(), bs, values));
    }
    Forest forest = new Forest(nodes, edges, tail, head);
    forest.setDegreeWeight(0);
    posted.add(forest);
    for (Constraint c : posted) {
      store.impose(c);
    }
    support.dictionary.addAuxiliaryVariables(literals);
    if (!store.consistency()) {
      throw Store.failException;
    }
    forests++;
    if (support.options.debug()) {
      FzConsole.println(
          "% successor forest: "
              + n
              + " nodes, "
              + arcs.size()
              + " arcs, "
              + missing.size()
              + " successors without value Booleans");
    }
  }
}
