/*
 * Linearizations.java
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import org.jacop.constraints.lp.LpColumn;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.ValueIndicator;

/**
 * Linear rows implied by constraints that are not linear relations themselves, for the linear
 * relaxation: big-M rows of reified and half-reified linear relations, the product rows of Boolean
 * and/or, McCormick rows of products, the lower side of max and min, |x|, the sum bounds of
 * all-different, and value encodings ({@code x = sum v b_v} with {@code sum b_v = 1}) from channels
 * and from reified equalities. Each row holds for every solution of its constraint within the
 * bounds the variables have when the rows are made, so the rows must be made at the root, and they
 * hold for the whole search.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class Linearizations {

  private Linearizations() {}

  /**
   * Returns the rows of a constraint, or an empty list when it has none here (also for the linear
   * relations that {@link LinearForms#of} reads).
   *
   * @param c the constraint
   * @return the rows
   */
  public static List<LinearForm> of(Constraint c) {
    List<LinearForm> out = new ArrayList<>();
    try {
      rows(c, out);
    } catch (ArithmeticException overflow) {
      out.clear();
    }
    return out;
  }

  /**
   * Returns the value encodings of the variables in the constraints: for each variable x with
   * Booleans {@code b_v <-> x = v} (from {@link #valueBooleans}) for two or more values, {@code sum
   * b_v <= 1}, and when the values cover the domain of x, {@code sum b_v = 1} and {@code x = sum v
   * b_v}; then also {@code y = sum a[v] b_v} for each {@link ElementInteger} {@code y = a[x]}.
   *
   * @param constraints the constraints
   * @return the rows
   */
  public static List<LinearForm> encodings(Collection<Constraint> constraints) {
    Map<IntVar, Map<Integer, IntVar>> byVar = valueBooleans(constraints);
    List<LinearForm> out = new ArrayList<>();
    Map<IntVar, Map<Integer, IntVar>> covering = new IdentityHashMap<>();
    for (Map.Entry<IntVar, Map<Integer, IntVar>> e : byVar.entrySet()) {
      IntVar x = e.getKey();
      Map<Integer, IntVar> m = e.getValue();
      // values outside the domain have their Boolean false
      m.keySet().removeIf(v -> !x.domain.contains(v));
      if (m.size() < 2 || m.containsValue(x)) {
        continue;
      }
      boolean covers = true;
      for (ValueEnumeration en = x.domain.valueEnumeration(); en.hasMoreElements(); ) {
        if (!m.containsKey(en.nextElement())) {
          covers = false;
          break;
        }
      }
      int k = m.size();
      IntVar[] bs = m.values().toArray(new IntVar[0]);
      long[] ones = new long[k];
      Arrays.fill(ones, 1);
      out.add(new LinearForm(bs, ones, 1, covers ? LinearForm.EQ : LinearForm.LE));
      if (covers) {
        IntVar[] vars = Arrays.copyOf(bs, k + 1);
        long[] w = new long[k + 1];
        int i = 0;
        for (int v : m.keySet()) {
          w[i++] = v;
        }
        vars[k] = x;
        w[k] = -1;
        out.add(new LinearForm(vars, w, 0, LinearForm.EQ));
        covering.put(x, m);
      }
    }
    // value = list[index - offset] over an encoded index: value = sum list[v - offset] b_v
    for (Constraint c : constraints) {
      if (c.getClass() != ElementInteger.class) {
        continue;
      }
      ElementInteger el = (ElementInteger) c;
      Map<Integer, IntVar> m = covering.get(el.index);
      if (m == null || m.containsValue(el.value) || el.value == el.index) {
        continue;
      }
      int k = m.size();
      IntVar[] vars = new IntVar[k + 1];
      long[] w = new long[k + 1];
      int i = 0;
      boolean inList = true;
      for (Map.Entry<Integer, IntVar> v : m.entrySet()) {
        int position = v.getKey() - el.indexOffset - 1;
        if (position < 0 || position >= el.list.length) {
          inList = false;
          break;
        }
        vars[i] = v.getValue();
        w[i++] = el.list[position];
      }
      if (inList) {
        vars[k] = el.value;
        w[k] = -1;
        out.add(new LinearForm(vars, w, 0, LinearForm.EQ));
      }
    }
    return out;
  }

  // value encodings over LP-only columns: on or off, the largest domain encoded, and the most
  // columns made for a model
  private static final boolean VALUE_COLUMNS =
      !"false".equals(System.getProperty("org.jacop.lp.valueColumns"));
  private static final int VALUE_COLUMNS_DOMAIN =
      Integer.getInteger("org.jacop.lp.valueColumnsDomain", 128);
  private static final int VALUE_COLUMNS_MAX =
      Integer.getInteger("org.jacop.lp.valueColumnsMax", 20_000);

  /**
   * Returns the value encodings of the variables of all-different-except constraints over auxiliary
   * columns of the relaxation ({@link LpColumn}), the rows that make the constraints per value, and
   * the rows that tie the reified comparisons of those variables with constants to the encodings.
   *
   * <p>Each variable x gets a column {@code x_v = [x = v]} for each value v of its domain other
   * than 0 (the Boolean of the model when it has one, from {@link #valueBooleans}), with {@code sum
   * x_v <= 1} (or {@code = 1} when 0 is not in the domain) and {@code x = sum v x_v}. Each
   * constraint gets {@code sum x_v <= 1} over its variables for each value v it does not exempt.
   * Each {@code b <-> x op c} (and {@code b -> x op c}) gets {@code b = sum x_v} ({@code b <= sum
   * x_v}) over the values v of the domain that satisfy it, or {@code b = 1 - sum x_v} over those
   * that do not when 0 satisfies it. These are the rows of the assignment model of a MIP, such as
   * the per-hall interval-clique rows of the capacitated concert hall problem, which the model
   * variables alone cannot state. The rows hold for every solution with the columns at the
   * indicators of its values; they are made at the root and hold for the whole search.
   *
   * <p>Only variables with at most {@code org.jacop.lp.valueColumnsDomain} (128) values are
   * encoded, and at most {@code org.jacop.lp.valueColumnsMax} (20,000) columns are made; {@code
   * -Dorg.jacop.lp.valueColumns=false} turns the rows off.
   *
   * @param constraints the constraints
   * @return the rows, empty when no constraint qualifies
   */
  public static List<LinearForm> valueColumns(Collection<Constraint> constraints) {
    if (!VALUE_COLUMNS) {
      return List.of();
    }
    List<AlldifferentExcept> lists = new ArrayList<>();
    for (Constraint c : constraints) {
      if ((c.getClass() == AlldifferentExcept.class || c.getClass() == AlldifferentExceptZero.class)
          && encodable((AlldifferentExcept) c)) {
        lists.add((AlldifferentExcept) c);
      }
    }
    if (lists.isEmpty()) {
      return List.of();
    }
    Map<IntVar, Map<Integer, IntVar>> given = valueBooleans(constraints);
    // the columns of each encoded variable by value; 0 is left implicit
    Map<IntVar, Map<Integer, IntVar>> encoded = new LinkedHashMap<>();
    List<LinearForm> out = new ArrayList<>();
    int made = 0;
    for (AlldifferentExcept a : lists) {
      for (IntVar x : a.list) {
        if (x.singleton() || encoded.containsKey(x)) {
          continue;
        }
        Map<Integer, IntVar> booleans = given.getOrDefault(x, Map.of());
        int fresh = 0;
        for (ValueEnumeration en = x.domain.valueEnumeration(); en.hasMoreElements(); ) {
          int v = en.nextElement();
          fresh += v != 0 && !booleans.containsKey(v) ? 1 : 0;
        }
        if (made + fresh > VALUE_COLUMNS_MAX) {
          continue;
        }
        made += fresh;
        Map<Integer, IntVar> m = new LinkedHashMap<>();
        for (ValueEnumeration en = x.domain.valueEnumeration(); en.hasMoreElements(); ) {
          int v = en.nextElement();
          IntVar b = booleans.get(v);
          if (b == null && v != 0) {
            b = new LpColumn(x, v);
          }
          if (b != null) {
            m.put(v, b);
          }
        }
        encoded.put(x, m);
        encode(x, m, out);
      }
    }
    for (AlldifferentExcept a : lists) {
      perValue(a, encoded, out);
    }
    for (Constraint c : constraints) {
      if (c instanceof AbstractReifiedConstraint r
          && (c.getClass() == Reified.class || c.getClass() == Implies.class)
          && r.c instanceof AbstractXcompC cmp
          && comparison(cmp)
          && boolean01(r.b)) {
        Map<Integer, IntVar> m = encoded.get(cmp.x);
        if (m != null && m.get(cmp.c) != r.b) {
          link(cmp, r.b, c.getClass() == Reified.class, m, out);
        }
      }
    }
    return out;
  }

  // a list of distinct variables with small domains
  private static boolean encodable(AlldifferentExcept a) {
    if (a.list.length < 2 || Arrays.stream(a.list).distinct().count() != a.list.length) {
      return false;
    }
    for (IntVar x : a.list) {
      if (x.getSize() > VALUE_COLUMNS_DOMAIN) {
        return false;
      }
    }
    return true;
  }

  // sum x_v <= 1 (= 1 without the value 0) and x = sum v x_v
  private static void encode(IntVar x, Map<Integer, IntVar> m, List<LinearForm> out) {
    int k = m.size();
    if (k == 0) {
      return;
    }
    boolean zero = x.domain.contains(0) && !m.containsKey(0);
    IntVar[] bs = m.values().toArray(new IntVar[0]);
    long[] ones = new long[k];
    Arrays.fill(ones, 1);
    out.add(new LinearForm(bs, ones, 1, zero ? LinearForm.LE : LinearForm.EQ));
    IntVar[] vars = Arrays.copyOf(bs, k + 1);
    long[] w = new long[k + 1];
    int i = 0;
    for (int v : m.keySet()) {
      w[i++] = v;
    }
    vars[k] = x;
    w[k] = -1;
    out.add(new LinearForm(vars, w, 0, LinearForm.EQ));
  }

  // sum x_v <= 1 over the variables of the constraint, for each value it does not exempt
  private static void perValue(
      AlldifferentExcept a, Map<IntVar, Map<Integer, IntVar>> encoded, List<LinearForm> out) {
    Map<Integer, List<IntVar>> byValue = new TreeMap<>();
    for (IntVar x : a.list) {
      Map<Integer, IntVar> m = encoded.get(x);
      if (m == null) {
        continue;
      }
      for (Map.Entry<Integer, IntVar> e : m.entrySet()) {
        if (!a.s.contains(e.getKey())) {
          byValue.computeIfAbsent(e.getKey(), k -> new ArrayList<>()).add(e.getValue());
        }
      }
    }
    for (List<IntVar> bs : byValue.values()) {
      if (bs.size() >= 2) {
        long[] ones = new long[bs.size()];
        Arrays.fill(ones, 1);
        out.add(new LinearForm(bs.toArray(new IntVar[0]), ones, 1, LinearForm.LE));
      }
    }
  }

  // b <-> x op c (or b -> x op c) over the encoding of x: b = sum x_v over the values v that
  // satisfy it, or b = 1 - sum x_v over those that do not when the implicit value 0 satisfies it
  private static void link(
      AbstractXcompC cmp, IntVar b, boolean both, Map<Integer, IntVar> m, List<LinearForm> out) {
    IntVar x = cmp.x;
    boolean zeroHolds = false;
    List<IntVar> in = new ArrayList<>();
    List<IntVar> notIn = new ArrayList<>();
    for (ValueEnumeration en = x.domain.valueEnumeration(); en.hasMoreElements(); ) {
      int v = en.nextElement();
      boolean holds = holds(cmp, v);
      IntVar xv = m.get(v);
      if (xv == null) {
        zeroHolds = holds; // the implicit value 0
      } else {
        (holds ? in : notIn).add(xv);
      }
    }
    // b - sum_in x_v = 0 (b <= sum_in), or b + sum_notIn x_v = 1 (b + sum_notIn <= 1)
    List<IntVar> side = zeroHolds ? notIn : in;
    IntVar[] vars = new IntVar[side.size() + 1];
    long[] w = new long[vars.length];
    vars[0] = b;
    w[0] = 1;
    for (int k = 0; k < side.size(); k++) {
      vars[k + 1] = side.get(k);
      w[k + 1] = zeroHolds ? 1 : -1;
    }
    int relation = both ? LinearForm.EQ : LinearForm.LE;
    out.add(new LinearForm(vars, w, zeroHolds ? 1 : 0, relation));
  }

  private static boolean comparison(AbstractXcompC cmp) {
    Class<?> k = cmp.getClass();
    return k == XeqC.class
        || k == XneqC.class
        || k == XltC.class
        || k == XlteqC.class
        || k == XgtC.class
        || k == XgteqC.class;
  }

  private static boolean holds(AbstractXcompC cmp, int v) {
    int c = cmp.c;
    Class<?> k = cmp.getClass();
    if (k == XeqC.class) {
      return v == c;
    } else if (k == XneqC.class) {
      return v != c;
    } else if (k == XltC.class) {
      return v < c;
    } else if (k == XlteqC.class) {
      return v <= c;
    } else if (k == XgtC.class) {
      return v > c;
    } else if (k == XgteqC.class) {
      return v >= c;
    }
    throw new IllegalArgumentException(k.getName());
  }

  /**
   * Returns the Booleans {@code b_v <-> x = v} of the constraints, from {@link ChannelReif}, {@link
   * Reified} {@link XeqC} and {@link ValueIndicator} equivalences, by variable and value, in the
   * order of the constraints (so that rows made from them do not depend on identity hash codes);
   * the first Boolean of a value wins.
   *
   * @param constraints the constraints
   * @return the Booleans of each variable by value
   */
  public static Map<IntVar, Map<Integer, IntVar>> valueBooleans(
      Collection<Constraint> constraints) {
    Map<IntVar, Map<Integer, IntVar>> byVar = new LinkedHashMap<>();
    for (Constraint c : constraints) {
      if (c.getClass() == ChannelReif.class) {
        ChannelReif ch = (ChannelReif) c;
        Map<Integer, IntVar> m = byVar.computeIfAbsent(ch.x, k -> new LinkedHashMap<>());
        for (AbstractChannel.Item it : ch.item) {
          m.putIfAbsent(it.value(), it.b());
        }
      } else if (c.getClass() == Reified.class
          && ((Reified) c).c.getClass() == XeqC.class
          && boolean01(((Reified) c).b)) {
        XeqC e = (XeqC) ((Reified) c).c;
        byVar.computeIfAbsent(e.x, k -> new LinkedHashMap<>()).putIfAbsent(e.c, ((Reified) c).b);
      } else if (c instanceof ValueIndicator vi
          && vi.indicator() != null
          && boolean01(vi.indicator())) {
        byVar
            .computeIfAbsent(vi.variable(), k -> new LinkedHashMap<>())
            .putIfAbsent(vi.value(), vi.indicator());
      }
    }
    return byVar;
  }

  private static void rows(Constraint c, List<LinearForm> out) {
    if (c instanceof Relaxable r) {
      out.addAll(r.relaxation());
      return;
    }
    Class<?> k = c.getClass();
    if (k == Reified.class && ((Reified) c).c.getClass() == In.class) {
      In in = (In) ((Reified) c).c;
      inSet(in.x, in.dom, ((Reified) c).b, out);
    } else if (k == Reified.class) {
      Reified r = (Reified) c;
      reified(LinearForms.of(r.c), r.b, true, out);
    } else if (k == Implies.class) {
      Implies r = (Implies) c;
      reified(LinearForms.of(r.c), r.b, false, out);
    } else if (k == XplusClteqZImplied.class) {
      // b -> x + c <= z
      XplusClteqZImplied r = (XplusClteqZImplied) c;
      reified(
          new LinearForm(new IntVar[] {r.x, r.z}, new long[] {1, -1}, -r.c, LinearForm.LE),
          r.b,
          false,
          out);
    } else if (k == AndBoolSimple.class || k == OrBoolSimple.class) {
      AbstractBoolSimple s = (AbstractBoolSimple) c;
      andOr(new IntVar[] {s.a, s.b}, s.result, k == AndBoolSimple.class, out);
    } else if (k == AndBoolVector.class || k == OrBoolVector.class) {
      AbstractBoolVector v = (AbstractBoolVector) c;
      andOr(v.list, v.result, k == AndBoolVector.class, out);
    } else if (k == XmulYeqZ.class) {
      XmulYeqZ m = (XmulYeqZ) c;
      product(m.x, m.y, m.z, out);
    } else if (k == Max.class || k == Min.class) {
      AbstractMinMax m = (AbstractMinMax) c;
      for (IntVar x : m.list) {
        bound(x, m.target, k == Max.class, out);
      }
    } else if (k == MaxSimple.class) {
      MaxSimple m = (MaxSimple) c;
      bound(m.x1, m.max, true, out);
      bound(m.x2, m.max, true, out);
    } else if (k == MinSimple.class) {
      MinSimple m = (MinSimple) c;
      bound(m.x1, m.min, false, out);
      bound(m.x2, m.min, false, out);
    } else if (k == AbsXeqY.class) {
      abs(((AbsXeqY) c).x, ((AbsXeqY) c).y, out);
    } else if (k == Alldistinct.class) {
      alldifferent(((Alldistinct) c).list, out);
    } else if (k == Alldiff.class || k == Alldifferent.class) {
      alldifferent(((Alldifferent) c).list, out);
    } else if (k == ElementInteger.class) {
      ElementInteger e = (ElementInteger) c;
      elementHull(e.index, e.list, e.indexOffset, e.value, out);
    } else if (k == ElementIntegerFast.class) {
      ElementIntegerFast e = (ElementIntegerFast) c;
      elementHull(e.index, e.list, e.indexOffset, e.value, out);
    } else if (k == XdivYeqZ.class) {
      XdivYeqZ d = (XdivYeqZ) c;
      if (d.y().singleton()) {
        divide(d.x(), d.y().value(), d.z(), out);
      }
    } else if (k == ConditionalSelect.class) {
      ConditionalSelect s = (ConditionalSelect) c;
      select(s.b, s.x, s.y, out);
    } else if (k == ChannelImply.class) {
      // b_v -> x = v: at most one of the Booleans
      AbstractChannel ch = (AbstractChannel) c;
      List<IntVar> bs = new ArrayList<>();
      for (AbstractChannel.Item it : ch.item) {
        if (ch.x.domain.contains(it.value())) {
          bs.add(it.b());
        }
      }
      if (bs.size() >= 2) {
        long[] ones = new long[bs.size()];
        Arrays.fill(ones, 1);
        out.add(new LinearForm(bs.toArray(new IntVar[0]), ones, 1, LinearForm.LE));
      }
    }
  }

  /**
   * Returns the big-M rows of {@code b -> x = c} and, when reified, of {@code !b -> x != c}, which
   * is linear when c is a bound of x ({@code x <= c - 1} or {@code x >= c + 1}). With {@code equal}
   * false, the rows of {@code b -> x != c} (or {@code b <-> x != c}).
   *
   * @param x the variable
   * @param c the value
   * @param b the 0/1 control variable
   * @param both whether b is equivalent to the relation, not only implies it
   * @param equal whether the relation is {@code x = c}, not {@code x != c}
   * @return the rows
   */
  public static List<LinearForm> valueRows(IntVar x, int c, IntVar b, boolean both, boolean equal) {
    List<LinearForm> out = new ArrayList<>();
    if (x == b || x.singleton() || !x.domain.contains(c)) {
      return out; // b is fixed by propagation
    }
    try {
      int relation;
      long bound;
      if (c == x.max()) {
        // x = c is x >= c, x != c is x <= c - 1
        relation = equal ? LinearForm.GE : LinearForm.LE;
        bound = equal ? c : c - 1L;
      } else if (c == x.min()) {
        relation = equal ? LinearForm.LE : LinearForm.GE;
        bound = equal ? c : c + 1L;
      } else {
        relation = equal ? LinearForm.EQ : LinearForm.NE;
        bound = c;
      }
      reified(new LinearForm(new IntVar[] {x}, new long[] {1}, bound, relation), b, both, out);
    } catch (ArithmeticException overflow) {
      out.clear();
    }
    return out;
  }

  /**
   * Returns the big-M rows of {@code b -> f} and, for {@code both}, of {@code !b -> !f} where that
   * is linear.
   *
   * @param f the linear relation
   * @param b the 0/1 control variable
   * @param both whether b is equivalent to f, not only implies it
   * @return the rows
   */
  public static List<LinearForm> implied(LinearForm f, IntVar b, boolean both) {
    List<LinearForm> out = new ArrayList<>();
    try {
      reified(f, b, both, out);
    } catch (ArithmeticException overflow) {
      out.clear();
    }
    return out;
  }

  // b <-> x in dom, for dom an interval [l, u]: b -> l <= x <= u; !b -> x > u when l <= min(x),
  // !b -> x < l when u >= max(x)
  private static void inSet(IntVar x, IntDomain dom, IntVar b, List<LinearForm> out) {
    if (dom.isEmpty() || dom.getSize() != dom.max() - dom.min() + 1L) {
      return;
    }
    long l = dom.min();
    long u = dom.max();
    IntVar[] xs = {x};
    long[] one = {1};
    if (l <= x.min()) {
      reified(new LinearForm(xs, one, u, LinearForm.LE), b, true, out);
    } else if (u >= x.max()) {
      reified(new LinearForm(xs, one, l, LinearForm.GE), b, true, out);
    } else {
      reified(new LinearForm(xs, one, l, LinearForm.GE), b, false, out);
      reified(new LinearForm(xs, one, u, LinearForm.LE), b, false, out);
    }
  }

  // the most hull edges of an element made into rows on each side
  private static final int HULL_ROWS = 64;

  // value = list[index - offset - 1] for a constant list: the rows of the convex hull of the points
  // (i, list[i - offset - 1]) over the domain of index, below and above
  private static void elementHull(
      IntVar index, int[] list, int offset, IntVar value, List<LinearForm> out) {
    if (index == value || index.singleton() || index.getSize() > 100_000) {
      return;
    }
    List<long[]> points = new ArrayList<>();
    for (ValueEnumeration en = index.domain.valueEnumeration(); en.hasMoreElements(); ) {
      int i = en.nextElement();
      long position = (long) i - offset - 1;
      if (position >= 0 && position < list.length) {
        points.add(new long[] {i, list[(int) position]});
      }
    }
    if (points.size() < 2) {
      return;
    }
    hullRows(points, index, value, true, out);
    hullRows(points, index, value, false, out);
  }

  // the lower (or upper) hull of points sorted by x, by the monotone chain; each edge from (x1, y1)
  // to (x2, y2) gives (x2 - x1) value - (y2 - y1) index >= (x2 - x1) y1 - (y2 - y1) x1 (<= above);
  // an edge that the bound of value already gives (flat at the bound) is left out
  private static void hullRows(
      List<long[]> points, IntVar index, IntVar value, boolean lower, List<LinearForm> out) {
    List<long[]> hull = new ArrayList<>();
    for (long[] p : points) {
      while (hull.size() >= 2) {
        long[] a = hull.get(hull.size() - 2);
        long[] o = hull.get(hull.size() - 1);
        long cross =
            Math.subtractExact(
                Math.multiplyExact(o[0] - a[0], p[1] - a[1]),
                Math.multiplyExact(o[1] - a[1], p[0] - a[0]));
        if (lower ? cross <= 0 : cross >= 0) {
          hull.remove(hull.size() - 1);
        } else {
          break;
        }
      }
      hull.add(p);
    }
    if (hull.size() - 1 > HULL_ROWS) {
      return;
    }
    long bound = lower ? value.min() : value.max();
    for (int i = 0; i + 1 < hull.size(); i++) {
      long[] p = hull.get(i);
      long[] q = hull.get(i + 1);
      long dx = q[0] - p[0];
      long dy = q[1] - p[1];
      if (dy == 0 && (lower ? p[1] <= bound : p[1] >= bound)) {
        continue;
      }
      long c = Math.subtractExact(Math.multiplyExact(dx, p[1]), Math.multiplyExact(dy, p[0]));
      out.add(
          new LinearForm(
              new IntVar[] {value, index},
              new long[] {dx, -dy},
              c,
              lower ? LinearForm.GE : LinearForm.LE));
    }
  }

  // z = x div d, rounding towards zero, for a constant d != 0: the remainder r = x - d z has the
  // sign of x and |r| <= |d| - 1
  private static void divide(IntVar x, int d, IntVar z, List<LinearForm> out) {
    if (d == 0 || x == z) {
      return;
    }
    long m = Math.abs((long) d) - 1;
    long low = x.min() >= 0 ? 0 : -m;
    long high = x.max() <= 0 ? 0 : m;
    IntVar[] vars = {x, z};
    long[] w = {1, -(long) d};
    if (low == high) {
      out.add(new LinearForm(vars, w, low, LinearForm.EQ));
      return;
    }
    out.add(new LinearForm(vars, w, low, LinearForm.GE));
    out.add(new LinearForm(vars, w, high, LinearForm.LE));
  }

  // the most branches of an if-then-else made into rows (each row of branch k has k + 3 terms)
  private static final int SELECT_BRANCHES = 32;

  // y = x[k] for the first k with b[k] = 1: branch k is selected when b[k] = 1 and b[j] = 0 for j <
  // k, so y - x[k] <= M (1 - b[k] + sum_{j<k} b[j]) and y - x[k] >= -M' (1 - b[k] + sum_{j<k}
  // b[j]), with M and M' from the bounds; the conditions fixed to 0 drop out, a condition fixed to
  // 1
  // ends the branches
  private static void select(IntVar[] b, IntVar[] x, IntVar y, List<LinearForm> out) {
    if (b.length > SELECT_BRANCHES) {
      return;
    }
    for (IntVar v : b) {
      if (v == y || !boolean01(v)) {
        return;
      }
    }
    List<IntVar> before = new ArrayList<>();
    for (int k = 0; k < b.length; k++) {
      if (b[k].max() == 0 || before.contains(b[k])) {
        continue; // not selected
      }
      boolean last = b[k].min() == 1;
      if (x[k] != y && !before.contains(x[k]) && x[k] != b[k]) {
        long up = Math.subtractExact((long) y.max(), x[k].min());
        long down = Math.subtractExact((long) x[k].max(), y.min());
        if (up > 0) {
          out.add(selectRow(y, x[k], last ? null : b[k], before, up, LinearForm.LE));
        }
        if (down > 0) {
          out.add(selectRow(y, x[k], last ? null : b[k], before, -down, LinearForm.GE));
        }
      }
      if (last) {
        return;
      }
      before.add(b[k]);
    }
  }

  // y - x + big bk - big sum before <= big (relation LE, big > 0), or the same with big < 0 and GE;
  // without bk (fixed to 1) the right side is 0
  private static LinearForm selectRow(
      IntVar y, IntVar x, IntVar bk, List<IntVar> before, long big, int relation) {
    int n = 2 + (bk == null ? 0 : 1) + before.size();
    IntVar[] vars = new IntVar[n];
    long[] w = new long[n];
    vars[0] = y;
    w[0] = 1;
    vars[1] = x;
    w[1] = -1;
    int i = 2;
    if (bk != null) {
      vars[i] = bk;
      w[i++] = big;
    }
    for (IntVar v : before) {
      vars[i] = v;
      w[i++] = -big;
    }
    return new LinearForm(vars, w, bk == null ? 0 : big, relation);
  }

  private static boolean boolean01(IntVar b) {
    return b.min() >= 0 && b.max() <= 1;
  }

  /**
   * The big-M rows of {@code b -> f} and, for a reified relation, of {@code !b -> !f}, with M from
   * the bounds of the variables. A relation over b itself, or that cannot be broken or met within
   * the bounds, gives no row.
   */
  private static void reified(LinearForm f, IntVar b, boolean both, List<LinearForm> out) {
    if (f == null || !boolean01(b) || f.vars().length == 0) {
      return;
    }
    for (IntVar v : f.vars()) {
      if (v == b) {
        return;
      }
    }
    long least = 0;
    long most = 0;
    for (int i = 0; i < f.vars().length; i++) {
      long w = f.weights()[i];
      IntVar v = f.vars()[i];
      least = Math.addExact(least, Math.multiplyExact(w, w > 0 ? v.min() : v.max()));
      most = Math.addExact(most, Math.multiplyExact(w, w > 0 ? v.max() : v.min()));
    }
    long c = f.c();
    switch (f.relation()) {
      case LinearForm.LE -> {
        implyLe(f, b, 1, c, most, out);
        if (both) {
          implyGe(f, b, 0, Math.addExact(c, 1), least, out);
        }
      }
      case LinearForm.GE -> {
        implyGe(f, b, 1, c, least, out);
        if (both) {
          implyLe(f, b, 0, Math.subtractExact(c, 1), most, out);
        }
      }
      case LinearForm.EQ -> {
        implyLe(f, b, 1, c, most, out);
        implyGe(f, b, 1, c, least, out);
      }
      default -> {
        // x != c: only the negation is linear
        if (both) {
          implyLe(f, b, 0, c, most, out);
          implyGe(f, b, 0, c, least, out);
        }
      }
    }
  }

  // b = when -> sum w x <= c: sum w x + M b <= c + M, or sum w x - M b <= c, with M = most - c
  private static void implyLe(
      LinearForm f, IntVar b, int when, long c, long most, List<LinearForm> out) {
    long big = Math.subtractExact(most, c);
    if (big <= 0) {
      return; // holds anyway
    }
    out.add(
        withB(f, b, when == 1 ? big : -big, when == 1 ? Math.addExact(c, big) : c, LinearForm.LE));
  }

  // b = when -> sum w x >= c: sum w x - M b >= c - M, or sum w x + M b >= c, with M = c - least
  private static void implyGe(
      LinearForm f, IntVar b, int when, long c, long least, List<LinearForm> out) {
    long big = Math.subtractExact(c, least);
    if (big <= 0) {
      return;
    }
    out.add(
        withB(
            f,
            b,
            when == 1 ? -big : big,
            when == 1 ? Math.subtractExact(c, big) : c,
            LinearForm.GE));
  }

  private static LinearForm withB(LinearForm f, IntVar b, long wb, long c, int relation) {
    int n = f.vars().length;
    IntVar[] vars = Arrays.copyOf(f.vars(), n + 1);
    long[] w = Arrays.copyOf(f.weights(), n + 1);
    vars[n] = b;
    w[n] = wb;
    return new LinearForm(vars, w, c, relation);
  }

  // r = and(xs): r <= x_i, sum x - r <= n - 1; r = or(xs): r >= x_i, r <= sum x
  private static void andOr(IntVar[] list, IntVar r, boolean and, List<LinearForm> out) {
    if (r.singleton() || !boolean01(r)) {
      return; // LinearForms reads a fixed result
    }
    // the vector constraints keep their Booleans in an order that follows identity hash codes;
    // the rows are made in the order of the names, so that the relaxation is the same every run
    IntVar[] xs = list.clone();
    Arrays.sort(xs, Comparator.comparing(IntVar::id));
    for (IntVar x : xs) {
      if (x == r || !boolean01(x)) {
        return;
      }
    }
    for (IntVar x : xs) {
      out.add(
          new LinearForm(
              new IntVar[] {r, x}, new long[] {1, -1}, 0, and ? LinearForm.LE : LinearForm.GE));
    }
    int n = xs.length;
    IntVar[] vars = Arrays.copyOf(xs, n + 1);
    long[] w = new long[n + 1];
    Arrays.fill(w, 1);
    vars[n] = r;
    w[n] = -1;
    out.add(
        and
            ? new LinearForm(vars, w, n - 1L, LinearForm.LE)
            : new LinearForm(vars, w, 0, LinearForm.GE));
  }

  // McCormick: z = x y over the boxes of x and y
  private static void product(IntVar x, IntVar y, IntVar z, List<LinearForm> out) {
    long xl = x.min();
    long xu = x.max();
    long yl = y.min();
    long yu = y.max();
    IntVar[] vars = {z, x, y};
    // z >= yl x + xl y - xl yl, z >= yu x + xu y - xu yu
    out.add(
        new LinearForm(
            vars,
            new long[] {1, -yl, -xl},
            Math.negateExact(Math.multiplyExact(xl, yl)),
            LinearForm.GE));
    out.add(
        new LinearForm(
            vars,
            new long[] {1, -yu, -xu},
            Math.negateExact(Math.multiplyExact(xu, yu)),
            LinearForm.GE));
    // z <= yl x + xu y - xu yl, z <= yu x + xl y - xl yu
    out.add(
        new LinearForm(
            vars,
            new long[] {1, -yl, -xu},
            Math.negateExact(Math.multiplyExact(xu, yl)),
            LinearForm.LE));
    out.add(
        new LinearForm(
            vars,
            new long[] {1, -yu, -xl},
            Math.negateExact(Math.multiplyExact(xl, yu)),
            LinearForm.LE));
  }

  // max >= x, or min <= x
  private static void bound(IntVar x, IntVar target, boolean max, List<LinearForm> out) {
    if (x == target) {
      return;
    }
    out.add(
        new LinearForm(
            new IntVar[] {target, x}, new long[] {1, -1}, 0, max ? LinearForm.GE : LinearForm.LE));
  }

  // y = |x|: y >= x, y >= -x, and y = x or y = -x when the sign of x is known
  private static void abs(IntVar x, IntVar y, List<LinearForm> out) {
    if (x == y) {
      return;
    }
    if (x.min() >= 0 || x.max() <= 0) {
      long s = x.min() >= 0 ? -1 : 1;
      out.add(new LinearForm(new IntVar[] {y, x}, new long[] {1, s}, 0, LinearForm.EQ));
      return;
    }
    out.add(new LinearForm(new IntVar[] {y, x}, new long[] {1, -1}, 0, LinearForm.GE));
    out.add(new LinearForm(new IntVar[] {y, x}, new long[] {1, 1}, 0, LinearForm.GE));
  }

  // sum x between the sums of the n smallest and the n largest values of the union of the domains
  private static void alldifferent(IntVar[] list, List<LinearForm> out) {
    int n = list.length;
    if (n < 2 || Arrays.stream(list).distinct().count() != n) {
      return;
    }
    long size = 0;
    for (IntVar x : list) {
      size += x.getSize();
    }
    TreeSet<Integer> values = new TreeSet<>();
    if (size <= 100_000) {
      for (IntVar x : list) {
        for (ValueEnumeration en = x.domain.valueEnumeration(); en.hasMoreElements(); ) {
          values.add(en.nextElement());
        }
      }
    } else {
      return;
    }
    if (values.size() < n) {
      return; // no solution; the constraint itself fails
    }
    long low = 0;
    long high = 0;
    var up = values.iterator();
    var down = values.descendingIterator();
    for (int i = 0; i < n; i++) {
      low = Math.addExact(low, up.next());
      high = Math.addExact(high, down.next());
    }
    long[] ones = new long[n];
    Arrays.fill(ones, 1);
    if (low == high) {
      out.add(new LinearForm(list, ones, low, LinearForm.EQ));
      return;
    }
    long least = 0;
    long most = 0;
    for (IntVar x : list) {
      least += x.min();
      most += x.max();
    }
    // only the sides the bounds of the variables do not give already
    if (low > least) {
      out.add(new LinearForm(list, ones, low, LinearForm.GE));
    }
    if (high < most) {
      out.add(new LinearForm(list, ones, high, LinearForm.LE));
    }
  }

  /** A constraint outside this package that gives its own rows. */
  public interface Relaxable {

    /**
     * Returns rows that hold for every solution of the constraint within the current bounds.
     *
     * @return the rows
     */
    List<LinearForm> relaxation();
  }
}
