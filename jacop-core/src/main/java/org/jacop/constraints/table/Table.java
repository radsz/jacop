/*
 * Table.java
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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Table implements the table constraint using a method presented in.
 *
 * <p>"Compact-Table: Efficient Filtering Table Constraints with Reversible Sparse Bit-Sets" Jordan
 * Demeulenaere, Renaud Hartert, Christophe Lecoutre, Guillaume Perez, Laurent Perron, Jean-Charles
 * Régin, Pierre Schaus. Proc. International Conference on Principles and Practice of Constraint
 * Programming, CP 2016. pp 207-223
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class Table extends AbstractTable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** Main data structure for the constraint. */
  ReversibleSparseBitSet rbs;

  /**
   * Data specifying support tuples for each variable; static structure created once when constraint
   * is posed.
   */
  Map<Integer, long[]>[] supports;

  Map<Integer, Integer>[] residues;

  /**
   * It constructs a table constraint.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the tuples which define alloed values.
   */
  public Table(IntVar[] list, int[][] tuples) {
    this(list, tuples, false);
  }

  /**
   * It constructs a table constraint.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the tuples which define alloed values.
   * @param reuseTuplesArgument specifies if the table of tuples should be used directly without
   *     copying.
   */
  public Table(IntVar[] list, int[][] tuples, boolean reuseTuplesArgument) {

    super(list, tuples, reuseTuplesArgument);
    checkInputForDuplication("list", list);
    numberId = idNumber.incrementAndGet();
    variableQueue = new HashSet<>();
  }

  /**
   * Creates support structures and initializes word arrays for the reversible sparse bit set.
   *
   * @param nw the number of words needed for the bit set
   * @return the initialized word array
   */
  @SuppressWarnings("unchecked")
  long[] makeSupportAndWords(int nw) {
    supports = new HashMap[x.length];
    residues = new HashMap[x.length];
    int n = tuple.length;

    long[] words = new long[nw];
    for (int i = 0; i < x.length; i++) {
      supports[i] = new HashMap<>();
      residues[i] = new HashMap<>();
      for (int j = 0; j < n; j++) {
        int v = tuple[j][i];
        if (validTuple(j)) {
          residues[i].put(v, 0); // initialize last found support to 0
          setBit(j, words); // initialize words for ReversibleSparseBitSet

          if (supports[i].containsKey(v)) {
            long[] bs = supports[i].get(v);
            setBit(j, bs);
            supports[i].put(v, bs);
          } else {
            long[] bs = new long[nw];
            setBit(j, bs);
            supports[i].put(v, bs);
          }
        }
      }
    }
    return words;
  }

  private void setBit(int n, long[] a) {

    int l = n % 64;
    int m = n / 64;
    a[m] |= 1L << l;
  }

  @Override
  public void impose(Store store) {

    this.store = store;
    super.impose(store);

    int n = tuple.length;
    int lastWordSize = n % 64;
    int numberBitSets = n / 64 + (lastWordSize != 0 ? 1 : 0);

    rbs = new ReversibleSparseBitSet();

    long[] words = makeSupportAndWords(numberBitSets);

    rbs.init(this.store, words);
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

      rbs.clearMask();
      int xIndex = varMap.get(v);

      Map<Integer, long[]> xSupport = supports[xIndex];
      if (delta < cd.getSize()) { // incremental update
        ValueEnumeration e = rp.valueEnumeration();
        while (e.hasMoreElements()) {
          long[] bs = xSupport.get(e.nextElement());
          if (bs != null) {
            rbs.addToMask(bs);
          }
        }
        rbs.reverseMask();
      } else { // reset-based update
        Set<Map.Entry<Integer, long[]>> xsEntry = xSupport.entrySet();
        if (cd.getSize() < xsEntry.size()) {
          // update based on the variable
          ValueEnumeration e = cd.valueEnumeration();
          while (e.hasMoreElements()) {
            long[] bs = xSupport.get(e.nextElement());
            if (bs != null) {
              rbs.addToMask(bs);
            }
          }
        } else {
          // updates based on table values
          for (Map.Entry<Integer, long[]> e : xsEntry) {
            Integer val = e.getKey();
            long[] bits = e.getValue();
            if (cd.contains(val)) {
              rbs.addToMask(bits);
            }
          }
        }
      }

      rbs.intersectWithMask();
      if (rbs.isEmpty()) {
        throw Store.failException;
      }
    }
  }

  @Override
  void filterDomains() {

    noNoGround = 0;
    long[] wrds = rbs.words.value();
    for (int i = 0; i < x.length; i++) {
      IntVar xi = x[i];
      boolean xiSingleton = xi.singleton();
      if (!xiSingleton) {
        noNoGround++;
      }

      // check only for not assign variables and variables that become single value at this store
      // level
      if (!xiSingleton || xi.dom().stamp() == store.level) {

        Map<Integer, long[]> xSupport = supports[i];

        Set<Map.Entry<Integer, long[]>> xsEntry = xSupport.entrySet();
        if (xi.dom().getSize() <= xsEntry.size()) {
          // filter based on the variable
          ValueEnumeration e = xi.dom().valueEnumeration();
          while (e.hasMoreElements()) {
            int el = e.nextElement();

            long[] bs = xSupport.get(el);
            if (bs != null) {
              int index = residues[i].get(el);

              if ((wrds[index] & bs[index]) == 0L) {

                index = rbs.intersectIndex(bs);
                if (index == -1) {
                  xi.domain.inComplement(store.level, xi, el);
                } else {
                  residues[i].put(el, index);
                }
              }
            } else {
              xi.domain.inComplement(store.level, xi, el);
            }
          }
        } else {
          // filter based on the table values
          IntDomain xDom = new IntervalDomain();
          for (Map.Entry<Integer, long[]> e : xsEntry) {
            Integer el = e.getKey();
            long[] bs = e.getValue();

            if (xi.domain.contains(el) && bs != null) {
              int index = residues[i].get(el);

              xDom.unionAdapt(el, el);

              if ((wrds[index] & bs[index]) == 0L) {

                index = rbs.intersectIndex(bs);
                if (index == -1) {
                  xi.domain.inComplement(store.level, xi, el);
                } else {
                  residues[i].put(el, index);
                }
              }
            } else {
              xi.domain.inComplement(store.level, xi, el);
            }
          }
          xi.domain.in(store.level, xi, xDom);
        }
      }
    }
  }

  @Override
  Set<IntVar> createVariableQueue() {
    return new HashSet<>();
  }

  @Override
  public String toString() {

    StringBuilder s = toStringBase("table");

    if (DEBUG) {
      s.append("\n").append(rbs);

      s.append("\nsupports: [");
      for (int i = 0; i < supports.length; i++) {
        s.append(i).append(": {");
        Map<Integer, long[]> supi = supports[i];
        for (Map.Entry<Integer, long[]> e : supi.entrySet()) {
          s.append(" ").append(e.getKey()).append("= [");
          long[] mask = e.getValue();
          for (long l : mask) {
            s.append("0x%08X".formatted(l)).append(" ");
          }
          s.append("]");
        }
        s.append("} ");
      }
      s.append("]");
    }
    return s.toString();
  }
}
