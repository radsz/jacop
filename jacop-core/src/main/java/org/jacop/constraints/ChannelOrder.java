/*
 * ChannelOrder.java
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Channels the order literals of an integer variable: {@code b[i] <=> (x <= t[i])}, or {@code b[i]
 * <=> (x > t[i])} for a negated item. It does what one reified comparison of x with a constant per
 * item does, with one propagator: the items are sorted by threshold, so a bound change of x fixes
 * the 0/1 variables of the thresholds it passes, and a fixed 0/1 variable moves a bound of x.
 *
 * <p>Presolve posts it for the {@code int_le_reif}, {@code int_lt_reif}, {@code int_ge_reif} and
 * {@code int_gt_reif} constraints of one variable with constants, the order counterpart of what
 * {@link ChannelReif} does for {@code int_eq_reif}.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class ChannelOrder extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent, Explainable, Copyable<ChannelOrder> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar x;

  // the items sorted by threshold: b[i] <=> (x <= t[i]) if atMost[i], b[i] <=> (x > t[i]) otherwise
  final IntVar[] b;
  final int[] t;
  final boolean[] atMost;

  // the items of each 0/1 variable; one variable may stand for several items
  private final Map<Var, int[]> itemsOf = new IdentityHashMap<>();

  // items below lo have t < min(x), so x <= t is false; items from hi on have t >= max(x)
  private TimeStamp<Integer> lo;
  private TimeStamp<Integer> hi;

  // 0/1 variables changed since the last consistency call; consistency appends its own changes
  private final List<Var> queue = new ArrayList<>();

  /**
   * Constructs b[i] {@literal <=>} (x {@literal <=} t[i]) if atMost[i], and b[i] {@literal <=>} (x
   * {@literal >} t[i]) otherwise.
   *
   * @param x the integer variable.
   * @param b the 0/1 variables.
   * @param t the thresholds.
   * @param atMost for each item, whether b stands for x {@literal <=} t or for x {@literal >} t.
   */
  public ChannelOrder(IntVar x, IntVar[] b, int[] t, boolean[] atMost) {
    checkInputForNullness(new String[] {"x", "b"}, new Object[] {x}, b);
    checkInputForNullness(new String[] {"t", "atMost"}, new Object[] {t, atMost});
    if (b.length != t.length || b.length != atMost.length) {
      throw new IllegalArgumentException(
          "ChannelOrder: b, t and atMost have different lengths "
              + b.length
              + ", "
              + t.length
              + ", "
              + atMost.length);
    }
    for (IntVar bi : b) {
      if (bi == x) {
        throw new IllegalArgumentException("ChannelOrder: x is also a 0/1 variable");
      }
      if (bi.min() < 0 || bi.max() > 1) {
        throw new IllegalArgumentException(
            "ChannelOrder: variable " + bi + " must have a domain within 0..1");
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 0;
    this.x = x;
    int n = b.length;
    Integer[] order = new Integer[n];
    for (int i = 0; i < n; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (i, j) -> Integer.compare(t[i], t[j]));
    this.b = new IntVar[n];
    this.t = new int[n];
    this.atMost = new boolean[n];
    for (int i = 0; i < n; i++) {
      this.b[i] = b[order[i]];
      this.t[i] = t[order[i]];
      this.atMost[i] = atMost[order[i]];
    }
    for (int i = 0; i < n; i++) {
      int[] old = itemsOf.get(this.b[i]);
      int[] items = old == null ? new int[1] : Arrays.copyOf(old, old.length + 1);
      items[items.length - 1] = i;
      itemsOf.put(this.b[i], items);
    }

    setScope(Stream.concat(Stream.of(x), Arrays.stream(b)));
  }

  @Override
  public void impose(Store store) {
    lo = new TimeStamp<>(store, 0);
    hi = new TimeStamp<>(store, t.length);
    super.impose(store);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    Integer event = getConsistencyPruningEventFromMap(v);
    if (event != null) {
      return event;
    }
    return v == x ? IntDomain.BOUND : IntDomain.GROUND;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (v != x) {
      queue.add(v);
    }
  }

  @Override
  public void removeLevel(int level) {
    queue.clear();
  }

  @Override
  public void consistency(Store store) {
    int l = lo.value();
    int h = hi.value();
    try {
      int next = 0;
      do {
        // a fixed 0/1 variable moves a bound of x
        while (next < queue.size()) {
          int[] items = itemsOf.get(queue.get(next++));
          if (items == null) {
            continue;
          }
          for (int i : items) {
            if (i >= l && i < h && b[i].singleton()) {
              if ((b[i].value() == 1) == atMost[i]) {
                x.domain.inMax(store.level, x, t[i]);
              } else if (t[i] == Integer.MAX_VALUE) {
                throw Store.failException;
              } else {
                x.domain.inMin(store.level, x, t[i] + 1);
              }
            }
          }
        }
        // the bounds of x fix the items they pass; fixing a 0/1 variable queues it again
        int min = x.min();
        int max = x.max();
        while (l < h && t[l] < min) {
          int v = atMost[l] ? 0 : 1;
          b[l].domain.in(store.level, b[l], v, v);
          l++;
        }
        while (h > l && t[h - 1] >= max) {
          int v = atMost[h - 1] ? 1 : 0;
          b[h - 1].domain.in(store.level, b[h - 1], v, v);
          h--;
        }
      } while (next < queue.size());
    } finally {
      queue.clear();
    }
    lo.update(l);
    hi.update(h);
    if (l == h) {
      removeConstraint();
    }
  }

  @Override
  public boolean satisfied() {
    int min = x.min();
    int max = x.max();
    for (int i = 0; i < t.length; i++) {
      if (!b[i].singleton()) {
        return false;
      }
      boolean le;
      if (t[i] >= max) {
        le = true;
      } else if (t[i] < min) {
        le = false;
      } else {
        return false;
      }
      if ((b[i].value() == 1) != (le == atMost[i])) {
        return false;
      }
    }
    return true;
  }

  // 1 if x <= t[i] holds before the trail position by the 0/1 variable, 0 if it fails, -1 if open
  private int literalBefore(AtomicTrail trail, int i, int position) {
    int bv;
    if (trail.minBefore(b[i], position) >= 1) {
      bv = 1;
    } else if (trail.maxBefore(b[i], position) <= 0) {
      bv = 0;
    } else {
      return -1;
    }
    return (bv == 1) == atMost[i] ? 1 : 0;
  }

  private void addLiteral(AtomicTrail trail, int i, int position, EntryList out) {
    if (trail.minBefore(b[i], position) >= 1) {
      trail.addLowerBound(b[i], position, out);
    } else {
      trail.addUpperBound(b[i], position, out);
    }
  }

  /**
   * Explains a bound of x by the 0/1 variable of the closest threshold, and a 0/1 variable by the
   * weakest bound of x that fixes its literal.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    int a = trail.value(entry);
    if (y == x) {
      if (kind == AtomicTrail.LE) {
        // x <= a by the largest threshold t <= a whose literal is true, or by the smallest one
        // above a and the holes of x between a and t
        int above = -1;
        for (int i = t.length - 1; i >= 0; i--) {
          if (literalBefore(trail, i, entry) == 1) {
            if (t[i] <= a) {
              addLiteral(trail, i, entry, out);
              return true;
            }
            above = i;
          }
        }
        if (above >= 0) {
          addLiteral(trail, above, entry, out);
          trail.addSkippedHoles(entry, t[above], out);
          return true;
        }
      } else if (kind == AtomicTrail.GE) {
        // x >= a by the smallest threshold t >= a - 1 whose literal is false, or by the largest one
        // below and the holes of x between t + 1 and a
        int below = -1;
        for (int i = 0; i < t.length; i++) {
          if (literalBefore(trail, i, entry) == 0) {
            if ((long) t[i] + 1 >= a) {
              addLiteral(trail, i, entry, out);
              return true;
            }
            below = i;
          }
        }
        if (below >= 0) {
          addLiteral(trail, below, entry, out);
          trail.addSkippedHoles(entry, t[below] + 1, out);
          return true;
        }
      }
      return false;
    }
    int[] items = itemsOf.get(y);
    if (items == null) {
      return false;
    }
    boolean one = kind == AtomicTrail.GE || kind == AtomicTrail.NE && a == 0;
    for (int i : items) {
      boolean le = one == atMost[i];
      int e =
          le
              ? trail.earliestUpperBound(x, t[i], entry)
              : trail.earliestLowerBound(x, (long) t[i] + 1, entry);
      if (e != Integer.MAX_VALUE) {
        if (e >= 0) {
          out.add(e);
        }
        return true;
      }
    }
    return false;
  }

  /** Explains a failure by a lower and an upper bound of x, each from x or from a literal. */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int now = trail.size();
    long low = trail.minBefore(x, now);
    int lowItem = -1;
    long high = trail.maxBefore(x, now);
    int highItem = -1;
    for (int i = 0; i < t.length; i++) {
      int lit = literalBefore(trail, i, now);
      if (lit == 0 && (long) t[i] + 1 > low) {
        low = (long) t[i] + 1;
        lowItem = i;
      } else if (lit == 1 && t[i] < high) {
        high = t[i];
        highItem = i;
      }
    }
    if (low <= high) {
      return false;
    }
    if (lowItem >= 0) {
      addLiteral(trail, lowItem, now, out);
    } else {
      trail.addLowerBound(x, now, out);
    }
    if (highItem >= 0) {
      addLiteral(trail, highItem, now, out);
    } else {
      trail.addUpperBound(x, now, out);
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder(id()).append(" : ChannelOrder(").append(x).append(", [");
    for (int i = 0; i < t.length; i++) {
      s.append(i == 0 ? "" : ", ")
          .append(b[i])
          .append(atMost[i] ? " <=> x <= " : " <=> x > ")
          .append(t[i]);
    }
    return s.append("] )").toString();
  }

  @Override
  public ChannelOrder copy(VarMap map) {
    IntVar[] bs = new IntVar[b.length];
    for (int i = 0; i < b.length; i++) {
      bs[i] = map.get(b[i]);
    }
    return new ChannelOrder(map.get(x), bs, t, atMost);
  }
}
