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
import java.util.TreeSet;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.LinearForm;

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
   * Booleans {@code b_v <-> x = v} (from {@link ChannelReif} or {@link Reified} {@link XeqC}) for
   * two or more values, {@code sum b_v <= 1}, and when the values cover the domain of x, {@code sum
   * b_v = 1} and {@code x = sum v b_v}; then also {@code y = sum a[v] b_v} for each {@link
   * ElementInteger} {@code y = a[x]}.
   *
   * @param constraints the constraints
   * @return the rows
   */
  public static List<LinearForm> encodings(Collection<Constraint> constraints) {
    // in the order of the constraints, so that the rows do not depend on identity hash codes
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
      }
    }
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

  private static void rows(Constraint c, List<LinearForm> out) {
    if (c instanceof Relaxable r) {
      out.addAll(r.relaxation());
      return;
    }
    Class<?> k = c.getClass();
    if (k == Reified.class) {
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
    } else if (k == Alldiff.class
        || k == Alldifferent.class
        || k == Circuit.class
        || k == Subcircuit.class) {
      // the successors of a circuit or a subcircuit are a permutation
      alldifferent(((Alldifferent) c).list, out);
    } else if (k == ElementInteger.class) {
      ElementInteger el = (ElementInteger) c;
      hull(el.index, el.list, el.indexOffset, el.value, out);
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

  // the most rows of each side of the hull of an element
  private static final int MAX_HULL = 32;

  /**
   * The facets of the convex hull of the points {@code (v, a[v - offset - 1])} for the values v of
   * the index, as rows over the index and the value: {@code y >= } the lower hull and {@code y <=}
   * the upper hull. Each facet through {@code (x1, y1)} and {@code (x2, y2)} is {@code (x2 - x1) y
   * - (y2 - y1) x >= (x2 - x1) y1 - (y2 - y1) x1}, in integers.
   */
  private static void hull(IntVar x, int[] a, int offset, IntVar y, List<LinearForm> out) {
    if (x == y || x.singleton()) {
      return;
    }
    List<long[]> points = new ArrayList<>();
    for (ValueEnumeration e = x.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int v = e.nextElement();
      int position = v - offset - 1;
      if (position < 0 || position >= a.length) {
        return; // the constraint fails on such values; its propagation removes them first
      }
      points.add(new long[] {v, a[position]});
      if (points.size() > 100_000) {
        return;
      }
    }
    if (points.size() < 2) {
      return;
    }
    // points by increasing x; the facets of the lower hull turn left, those of the upper right
    for (boolean lower : new boolean[] {true, false}) {
      List<long[]> h = new ArrayList<>();
      for (long[] p : points) {
        while (h.size() >= 2 && !turns(h.get(h.size() - 2), h.get(h.size() - 1), p, lower)) {
          h.remove(h.size() - 1);
        }
        h.add(p);
      }
      if (h.size() - 1 > MAX_HULL) {
        continue; // too many facets; the bounds of y stand in for them
      }
      for (int q = 0; q + 1 < h.size(); q++) {
        long dx = h.get(q + 1)[0] - h.get(q)[0];
        long dy = h.get(q + 1)[1] - h.get(q)[1];
        if (dy == 0) {
          continue; // a flat facet is a bound of y
        }
        long side =
            Math.subtractExact(
                Math.multiplyExact(dx, h.get(q)[1]), Math.multiplyExact(dy, h.get(q)[0]));
        out.add(
            new LinearForm(
                new IntVar[] {y, x},
                new long[] {dx, -dy},
                side,
                lower ? LinearForm.GE : LinearForm.LE));
      }
    }
  }

  // whether o, p, q turn left (lower hull) or right (upper hull), strictly
  private static boolean turns(long[] o, long[] p, long[] q, boolean lower) {
    long cross =
        Math.subtractExact(
            Math.multiplyExact(p[0] - o[0], q[1] - o[1]),
            Math.multiplyExact(p[1] - o[1], q[0] - o[0]));
    return lower ? cross > 0 : cross < 0;
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
