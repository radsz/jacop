/*
 * SimpleTable.java
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

package org.jacop.constraints.table;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;

/**
 * SimpleTable implements the table constraint using a method presented in.
 *
 * <p>"Compact-Table: Efficient Filtering Table Constraints with Reversible Sparse Bit-Sets" Jordan
 * Demeulenaere, Renaud Hartert, Christophe Lecoutre, Guillaume Perez, Laurent Perron, Jean-Charles
 * Régin, Pierre Schaus. Proc. International Conference on Principles and Practice of Constraint
 * Programming, CP 2016. pp 207-223
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class SimpleTable extends AbstractTable implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** Main data structure for the constraint. */
  TimeStamp<Long> words;

  long mask;

  /**
   * Data specifying support tuples for each variable; static structure created once when constraint
   * is posed.
   */
  Map<Integer, Long>[] supports;

  /**
   * It constructs a table constraint.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the tuples which define alloed values.
   */
  public SimpleTable(IntVar[] list, int[][] tuples) {
    this(list, tuples, false);
  }

  /**
   * It constructs a table constraint.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the tuples which define allowed values.
   * @param reuseTupleArguments specifies if the tuples argument should be used directly without
   *     copying.
   */
  public SimpleTable(IntVar[] list, int[][] tuples, boolean reuseTupleArguments) {

    super(list, tuples, reuseTupleArguments);

    if (tuple.length > 64) {
      throw new IllegalArgumentException(
          "\nSimpleTable: number of tuples must be <= 64; is " + tuple.length);
    }

    numberId = idNumber.incrementAndGet();
    variableQueue = new LinkedHashSet<>();
  }

  @SuppressWarnings("unchecked")
  @Override
  public void impose(Store store) {
    this.store = store;

    super.impose(store);

    supports = new Map[x.length];
    int n = tuple.length;

    long wrds = 0;
    for (int i = 0; i < x.length; i++) {
      supports[i] = new HashMap<>();
      for (int j = 0; j < n; j++) {
        int v = tuple[j][i];
        if (validTuple(j)) {
          wrds |= 1L << j;
          if (supports[i].containsKey(v)) {
            long bs = supports[i].get(v);
            bs |= 1L << j;
            supports[i].put(v, bs);
          } else {
            long bs = 1L << j;
            supports[i].put(v, bs);
          }
        }
      }
    }
    words = new TimeStamp<>(store, wrds);
  }

  @Override
  void updateTable(Set<IntVar> fdvs) {

    for (IntVar v : fdvs) {

      // recent pruning
      IntDomain cd = v.dom();
      IntDomain pd = cd.getPreviousDomain();
      IntDomain rp;
      int delta;
      if (pd == null) {
        rp = cd;
        delta = cd.getSize();
      } else {
        rp = pd.subtract(cd);
        delta = rp.getSize();
        if (delta == 0) {
          continue;
        }
      }

      mask = 0; // clear mask
      int xIndex = varMap.get(v);

      Map<Integer, Long> xSupport = supports[xIndex];
      if (delta < cd.getSize()) { // incremental update
        ValueEnumeration e = rp.valueEnumeration();
        while (e.hasMoreElements()) {
          Long bs = xSupport.get(e.nextElement());
          if (bs != null) {
            mask |= bs;
          }
        }
        mask = ~mask;
      } else { // reset-based update
        Set<Map.Entry<Integer, Long>> xsEntry = xSupport.entrySet();
        if (cd.getSize() < xsEntry.size()) {
          // update based on the variable
          ValueEnumeration e = cd.valueEnumeration();
          while (e.hasMoreElements()) {
            Long bs = xSupport.get(e.nextElement());
            if (bs != null) {
              mask |= bs;
            }
          }
        } else {
          // updates based on table values
          for (Map.Entry<Integer, Long> e : xsEntry) {
            Integer val = e.getKey();
            Long bits = e.getValue();
            if (cd.contains(val)) {
              mask |= bits;
            }
          }
        }
      }

      boolean empty = intersectWithMask();
      if (empty) {
        throw Store.failException;
      }
    }
  }

  boolean intersectWithMask() {
    long w = words.value();
    long wOriginal = w;

    w &= mask;

    if (w != wOriginal) {
      words.update(w);
    }

    return w == 0; // empty
  }

  @Override
  void filterDomains() {

    noNoGround = 0;
    long wrds = words.value();
    for (int i = 0; i < x.length; i++) {
      IntVar xi = x[i];
      boolean xiSingleton = xi.singleton();
      if (!xiSingleton) {
        noNoGround++;
      }

      // check only for not assign variables and variables that become single value at this store
      // level
      if (!xiSingleton || xi.dom().stamp() == store.level) {

        Map<Integer, Long> xSupport = supports[i];

        Set<Map.Entry<Integer, Long>> xsEntry = xSupport.entrySet();
        if (xi.dom().getSize() <= xsEntry.size()) {
          // filter based on the variable
          ValueEnumeration e = xi.dom().valueEnumeration();
          while (e.hasMoreElements()) {
            int el = e.nextElement();

            Long bs = xSupport.get(el);
            if (bs != null) {
              if ((wrds & bs) == 0L) {
                xi.domain.inComplement(store.level, xi, el);
              }
            } else {
              xi.domain.inComplement(store.level, xi, el);
            }
          }
        } else {
          // filter based on the table values
          IntDomain xDom = new IntervalDomain();
          for (Map.Entry<Integer, Long> e : xsEntry) {
            Integer val = e.getKey();
            Long bits = e.getValue();
            if (xi.domain.contains(val) && (wrds & bits) != 0L) {
              xDom.unionAdapt(val);
            }
          }
          xi.domain.in(store.level, xi, xDom);
        }
      }
    }
  }

  @Override
  Set<IntVar> createVariableQueue() {
    return new LinkedHashSet<>();
  }

  @Override
  public boolean satisfied() {

    if (!grounded()) {
      return false;
    }

    long wrds = words.value();
    for (int i = 0; i < x.length; i++) {
      int el = x[i].value();
      Long bs = supports[i].get(el);
      if (bs != null) {
        if ((wrds & bs) == 0L) {
          return false;
        }
      } else {
        return false;
      }
    }

    return true;
  }

  @Override
  public String toString() {

    StringBuilder s = toStringBase("simpleTable");

    if (debug) {
      s.append("\n0:").append("0x%08X".formatted(words.value()));

      s.append("\nsupports: [");
      for (int i = 0; i < supports.length; i++) {
        s.append(i).append(": {");
        Map<Integer, Long> supi = supports[i];
        for (Map.Entry<Integer, Long> e : supi.entrySet()) {
          s.append(" ").append(e.getKey()).append("= [");
          Long localMask = e.getValue();
          s.append("0x%08X".formatted(localMask)).append(" ");
          s.append("]");
        }
        s.append("} ");
      }
      s.append("]");
    }
    return s.toString();
  }
}
