/*
 * Lin.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in material modified versions of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.xcsp;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * A linear integer expression {@code sum a[i] * v[i] + c} over integer FlatZinc variables, with
 * each variable at most once and no zero coefficient. Mutable while it is built.
 */
final class Lin {

  FznVar[] v;
  long[] a;
  int n;
  long c;

  // position of a variable, built for long sums only
  private Map<FznVar, Integer> index;

  Lin() {
    v = new FznVar[2];
    a = new long[2];
  }

  static Lin constant(long c) {
    Lin l = new Lin();
    l.c = c;
    return l;
  }

  static Lin of(FznVar x) {
    Lin l = new Lin();
    l.add(x, 1);
    return l;
  }

  boolean isConstant() {
    return n == 0;
  }

  /** Whether the expression is one variable with coefficient 1 and no constant. */
  boolean isVariable() {
    return n == 1 && a[0] == 1 && c == 0;
  }

  void add(FznVar x, long k) {
    if (k == 0) {
      return;
    }
    if (x.bool) {
      throw new IllegalStateException("Boolean variable in a linear expression: " + x);
    }
    int i = find(x);
    if (i >= 0) {
      a[i] = Math.addExact(a[i], k);
      if (a[i] == 0) {
        remove(i);
      }
      return;
    }
    if (n == v.length) {
      v = Arrays.copyOf(v, 2 * n);
      a = Arrays.copyOf(a, 2 * n);
    }
    v[n] = x;
    a[n] = k;
    if (index != null) {
      index.put(x, n);
    }
    n++;
    if (index == null && n > 16) {
      index = new HashMap<>();
      for (int j = 0; j < n; j++) {
        index.put(v[j], j);
      }
    }
  }

  private int find(FznVar x) {
    if (index != null) {
      Integer i = index.get(x);
      return i == null ? -1 : i;
    }
    for (int i = 0; i < n; i++) {
      if (v[i] == x) {
        return i;
      }
    }
    return -1;
  }

  private void remove(int i) {
    if (index != null) {
      index.remove(v[i]);
    }
    System.arraycopy(v, i + 1, v, i, n - i - 1);
    System.arraycopy(a, i + 1, a, i, n - i - 1);
    n--;
    v[n] = null;
    if (index != null) {
      for (int j = i; j < n; j++) {
        index.put(v[j], j);
      }
    }
  }

  void add(Lin o, long k) {
    for (int i = 0; i < o.n; i++) {
      add(o.v[i], Math.multiplyExact(o.a[i], k));
    }
    c = Math.addExact(c, Math.multiplyExact(o.c, k));
  }

  Lin copy() {
    Lin l = new Lin();
    l.add(this, 1);
    return l;
  }

  Lin negate() {
    Lin l = new Lin();
    l.add(this, -1);
    return l;
  }

  long min() {
    long s = c;
    for (int i = 0; i < n; i++) {
      s = Bounds.add(s, Bounds.mul(a[i], a[i] > 0 ? v[i].min() : v[i].max()));
    }
    return s;
  }

  long max() {
    long s = c;
    for (int i = 0; i < n; i++) {
      s = Bounds.add(s, Bounds.mul(a[i], a[i] > 0 ? v[i].max() : v[i].min()));
    }
    return s;
  }

  /** The greatest common divisor of the coefficients (1 for a constant). */
  long gcd() {
    long g = 0;
    for (int i = 0; i < n; i++) {
      g = gcd(g, Math.abs(a[i]));
    }
    return g == 0 ? 1 : g;
  }

  static long gcd(long x, long y) {
    while (y != 0) {
      long t = x % y;
      x = y;
      y = t;
    }
    return x;
  }

  /** A key of the expression that does not depend on the order of its terms. */
  String key() {
    Integer[] order = new Integer[n];
    for (int i = 0; i < n; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (x, y) -> Integer.compare(v[x].id, v[y].id));
    StringBuilder s = new StringBuilder();
    for (Integer i : order) {
      s.append(a[i]).append('*').append(v[i].id).append('+');
    }
    return s.append(c).toString();
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    for (int i = 0; i < n; i++) {
      s.append(a[i]).append('*').append(v[i].name).append(" + ");
    }
    return s.append(c).toString();
  }
}
