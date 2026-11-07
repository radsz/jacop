/*
 * SequenceDetector.java
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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Sequence;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.fz.ASTAnnotation;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.Node;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds sliding-window cardinality constraints that a model states window by window and posts
 * them as one {@link Sequence} global. A window is a linear constraint {@code sum(y[i..i+q-1]) <=
 * c} ({@code >= c}, {@code = c}) with unit coefficients over 0/1 variables; windows with the same q
 * and bound whose variables are shifted by one position form a chain, and a chain of at least
 * {@code jacop.fz.sequenceWindows} (default 3) windows is the constraint {@code sequence(y, {1}, q,
 * min, max)}. Chains over the same list with a lower and an upper bound become one constraint.
 *
 * <p>When every y[i] is the 0/1 value {@code A[x[i]]} of an element constraint over one constant
 * array A, as in car sequencing (CSPLib prob001; the option of the class of the car at each step),
 * the constraint is posted over the x[i] instead, with the set of the indices v where A[v] = 1.
 * This is the model of Régin and Puget (CP 1997) and of the constraint-based local search of Comet
 * (Van Hentenryck and Michel, "Constraint-Based Local Search", MIT Press 2005): the sequence of
 * classes is counted directly, and {@link org.jacop.constraints.AmongSeq} reaches domain
 * consistency over the whole sequence (van Hoeve, Pesant, Rousseau and Sabharwal, CP 2006; Brand,
 * Narodytska, Quimper, Stuckey and Walsh, CP 2007), which the windows do not.
 *
 * <p>The window constraints are still posted. The system property {@code org.jacop.fz.sequence} set
 * to false turns the detection off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class SequenceDetector implements ParserTreeConstants {

  static final int MIN_WINDOWS = Integer.getInteger("jacop.fz.sequenceWindows", 3);

  static final boolean LIFT = Boolean.getBoolean("jacop.fz.sequenceLift");

  private final Support support;

  /** Statistics: the sequence constraints posted, and those over the indices of elements. */
  int posted;

  int lifted;

  int windowsCovered;

  // one window: its variables, its kind and its bound
  private static final class Window {
    private final IntVar[] y;
    private final int kind;
    private final int bound;
    // the row, or null if it defines a variable and so is not implied by the sequence alone
    private final SimpleNode row;

    Window(IntVar[] y, int kind, int bound, SimpleNode row) {
      this.y = y;
      this.kind = kind;
      this.bound = bound;
      this.row = row;
    }

    IntVar[] y() {
      return y;
    }

    int kind() {
      return kind;
    }

    int bound() {
      return bound;
    }
  }

  private static final int AT_MOST = 0;
  private static final int AT_LEAST = 1;
  private static final int EXACTLY = 2;

  // one element over a constant 0/1 array: y = array[x - first]
  private static final class Channel {
    private final IntVar x;
    private final int[] array;
    private final int first;

    Channel(IntVar x, int[] array, int first) {
      this.x = x;
      this.array = array;
      this.first = first;
    }

    IntVar x() {
      return x;
    }

    int[] array() {
      return array;
    }

    int first() {
      return first;
    }
  }

  private final List<Window> windows = new ArrayList<>();
  private final Set<SimpleNode> impliedRows = Collections.newSetFromMap(new IdentityHashMap<>());
  private final Map<IntVar, Channel> channels = new IdentityHashMap<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public SequenceDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.sequence is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.sequence"));
  }

  /**
   * It reads the window constraints of the model and posts their sequence constraints.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (windows.size() < MIN_WINDOWS) {
      return;
    }
    // the bounds of each list: min and max by the list of the chain
    Map<List<IntVar>, int[]> bounds = new LinkedHashMap<>();
    Map<List<IntVar>, List<SimpleNode>> rows = new HashMap<>();
    for (List<Window> chain : chains()) {
      if (chain.size() < MIN_WINDOWS) {
        continue;
      }
      Window first = chain.get(0);
      int q = first.y().length;
      IntVar[] list = Arrays.copyOf(first.y(), q + chain.size() - 1);
      for (int k = 1; k < chain.size(); k++) {
        list[q + k - 1] = chain.get(k).y()[q - 1];
      }
      IdentityList key = new IdentityList(list);
      int[] b = bounds.computeIfAbsent(key, k -> new int[] {0, q, q, 0});
      if (b[2] != q) {
        continue;
      }
      List<SimpleNode> chainRows = rows.computeIfAbsent(key, k -> new ArrayList<>());
      for (Window w : chain) {
        if (w.row != null) {
          chainRows.add(w.row);
        }
      }
      if (first.kind() != AT_LEAST) {
        b[1] = Math.min(b[1], first.bound());
      }
      if (first.kind() != AT_MOST) {
        b[0] = Math.max(b[0], first.bound());
      }
      b[3] += chain.size();
    }
    for (Map.Entry<List<IntVar>, int[]> e : bounds.entrySet()) {
      int[] b = e.getValue();
      if (b[0] <= 0 && b[1] >= b[2]) {
        continue;
      }
      post(e.getKey().toArray(new IntVar[0]), b[2], b[0], b[1]);
      windowsCovered += b[3];
      impliedRows.addAll(rows.get(e.getKey()));
    }
    if (support.options.debug() && posted > 0) {
      FzConsole.println(
          "% sequence detector: "
              + posted
              + " sequences ("
              + lifted
              + " over element indices) of "
              + windowsCovered
              + " windows");
    }
  }

  /**
   * It returns the window rows that the posted sequences imply. Each is the constraint element of a
   * constraint item; the rows are still posted, but local search need not evaluate them, as it
   * evaluates the sequence.
   *
   * @return the implied rows, compared by identity.
   */
  public Set<SimpleNode> impliedRows() {
    return impliedRows;
  }

  private void post(IntVar[] y, int q, int min, int max) {
    IntVar[] list = y;
    IntervalDomain set = new IntervalDomain(1, 1);
    Channel c0 = LIFT ? channels.get(y[0]) : null;
    if (c0 != null) {
      IntVar[] x = new IntVar[y.length];
      for (int i = 0; i < y.length && x != null; i++) {
        Channel c = channels.get(y[i]);
        if (c == null || c.first() != c0.first() || !Arrays.equals(c.array(), c0.array())) {
          x = null;
        } else {
          x[i] = c.x();
        }
      }
      if (x != null) {
        list = x;
        set = new IntervalDomain();
        for (int k = 0; k < c0.array().length; k++) {
          if (c0.array()[k] == 1) {
            set.unionAdapt(c0.first() + k, c0.first() + k);
          }
        }
        lifted++;
      }
    }
    Sequence sequence = Sequence.builder().list(list).set(set).q(q).min(min).max(max).build();
    for (Constraint c : sequence.decompose(support.store)) {
      // redundant: it does not add to the degrees that variable selection reads
      c.setDegreeWeight(0);
      support.pose(c);
    }
    posted++;
  }

  // the chains of windows, each window followed by the one shifted by one position
  private List<List<Window>> chains() {
    Map<Object, Window> byHead = new HashMap<>();
    Set<Object> tails = new HashSet<>();
    for (Window w : windows) {
      byHead.putIfAbsent(key(w, Arrays.copyOf(w.y(), w.y().length - 1)), w);
      tails.add(key(w, Arrays.copyOfRange(w.y(), 1, w.y().length)));
    }
    List<List<Window>> result = new ArrayList<>();
    Set<Window> used = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Window w : windows) {
      if (used.contains(w) || tails.contains(key(w, Arrays.copyOf(w.y(), w.y().length - 1)))) {
        continue;
      }
      List<Window> chain = new ArrayList<>();
      Window cur = w;
      while (cur != null && used.add(cur)) {
        chain.add(cur);
        cur = byHead.get(key(cur, Arrays.copyOfRange(cur.y(), 1, cur.y().length)));
      }
      result.add(chain);
    }
    return result;
  }

  private static Object key(Window w, IntVar[] part) {
    return List.of(w.kind(), w.bound(), new IdentityList(part));
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "int_lin_le", "int_lin_eq" -> window(node, "int_lin_eq".equals(node.getName()));
      case "array_int_element", "array_var_int_element" -> channel(node, 1);
      case "jacop_array_var_int_element_nonshifted" ->
          channel(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      default -> {
        // not a window or a channel
      }
    }
  }

  private void window(ASTConstElem node, boolean equation) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    if (a.length < 2 || Math.abs(a[0]) != 1) {
      return;
    }
    for (int c : a) {
      if (c != a[0]) {
        return;
      }
    }
    IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (y.length != a.length) {
      return;
    }
    for (IntVar v : y) {
      if (v.min() < 0 || v.max() > 1) {
        return;
      }
    }
    int rhs = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int kind;
    int bound;
    if (equation) {
      kind = EXACTLY;
      bound = a[0] * rhs;
    } else if (a[0] == 1) {
      kind = AT_MOST;
      bound = rhs;
    } else {
      kind = AT_LEAST;
      bound = -rhs;
    }
    windows.add(new Window(y.clone(), kind, bound, definesVariable(node) ? null : node));
  }

  // the annotations are children of the constraint item, the parent of the element
  private static boolean definesVariable(ASTConstElem node) {
    Node item = node.jjtGetParent();
    for (int i = 0; item != null && i < item.jjtGetNumChildren(); i++) {
      if (item.jjtGetChild(i) instanceof ASTAnnotation ann
          && "defines_var".equals(ann.getAnnId())) {
        return true;
      }
    }
    return false;
  }

  private void channel(ASTConstElem node, int first) {
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    if (index.singleton()) {
      return;
    }
    IntVar[] vars = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int[] array = new int[vars.length];
    for (int k = 0; k < vars.length; k++) {
      if (!vars[k].singleton() || vars[k].value() < 0 || vars[k].value() > 1) {
        return;
      }
      array[k] = vars[k].value();
    }
    IntVar value = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (!value.singleton()) {
      channels.putIfAbsent(value, new Channel(index, array, first));
    }
  }

  /** A list of variables compared by the identity of its elements. */
  private static final class IdentityList extends java.util.AbstractList<IntVar> {
    private final IntVar[] items;

    IdentityList(IntVar[] items) {
      this.items = items;
    }

    @Override
    public IntVar get(int i) {
      return items[i];
    }

    @Override
    public int size() {
      return items.length;
    }

    @Override
    public boolean equals(Object o) {
      if (!(o instanceof IdentityList other) || other.items.length != items.length) {
        return false;
      }
      for (int i = 0; i < items.length; i++) {
        if (items[i] != other.items[i]) {
          return false;
        }
      }
      return true;
    }

    @Override
    public int hashCode() {
      int h = 1;
      for (IntVar v : items) {
        h = 31 * h + System.identityHashCode(v);
      }
      return h;
    }
  }
}
