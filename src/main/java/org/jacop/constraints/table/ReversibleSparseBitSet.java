/*
 * ReversibleSparseBitSet.java
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
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */


package org.jacop.constraints.table;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * ReversibleSparseBitSet implements the main data structure for table constraint.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class ReversibleSparseBitSet {

    TimeStamp<long[]> words;
    private int[] index;
    private TimeStamp<Integer> limit;
    private long[] mask;

    public ReversibleSparseBitSet() {
    }

    @SuppressWarnings("unchecked") public ReversibleSparseBitSet(Store store, IntVar[] x, int[][] tuple) {

        int n = tuple.length;
        int lastWordSize = n % 64;
        int numberBitSets = n / 64 + ((lastWordSize != 0) ? 1 : 0);

        long[] bs = new long[numberBitSets];
        for (int i = 0; i < n; i++)
            if (validTuple(x, tuple[i]))
                setBit(i, bs);

        init(store, bs);

    }

    void init(Store store, long[] w) {
        int n = w.length;

        limit = new TimeStamp<Integer>(store, n - 1);

        words = new TimeStamp<long[]>(store, w);

        index = new int[n];
        for (int i = 0; i < n; i++)
            index[i] = i;

        mask = new long[n];
    }

    private long[] setBit(int n, long[] a) {

        int l = n % 64;
        int m = n / 64;

        a[m] |= (1L << l);

        return a;
    }

    private boolean validTuple(IntVar[] x, int[] t) {

        int n = t.length;
        int i = 0;
        while (i < n) {
            if (!x[i].dom().contains(t[i]))
                return false;
            i++;
        }
        return true;
    }

    boolean isEmpty() {
        return limit.value() == -1;
    }

    void clearMask() {
        for (int i = 0; i < limit.value() + 1; i++) {
            int offset = index[i];
            mask[offset] = 0;
        }
    }

    void reverseMask() {
        for (int i = 0; i < limit.value() + 1; i++) {
            int offset = index[i];
            mask[offset] = ~mask[offset];
        }
    }

    void addToMask(long[] m) {
        for (int i = 0; i < limit.value() + 1; i++) {
            int offset = index[i];
            mask[offset] = mask[offset] | m[offset];
        }
    }

    void intersectWithMask() {

        int n = limit.value();
        long[] wrds = words.value();
        long[] ws = new long[wrds.length];
        boolean update = false;
        System.arraycopy(wrds, 0, ws, 0, wrds.length);
        int l = n;

        for (int i = n; i >= 0; i--) {
            int offset = index[i];
            long wOriginal = ws[offset];
            long w = wOriginal;

            w &= mask[offset];

            if (w != wOriginal) {
                ws[offset] = w;
                update = true;
                if (w == 0) {
                    index[i] = index[l];
                    index[l] = offset;
                    l--;
                }
            }
        }

        if (update) {
            words.update(ws);
            if (l < n)
                limit.update(l);
        }
    }

    int intersectIndex(long[] m) {

        long[] wrds = words.value();
        for (int i = 0; i < limit.value() + 1; i++) {
            int offset = index[i];
            long w = wrds[offset];

            w &= m[offset];
            if (w != 0)
                return offset;
        }
        return -1;
    }


    int noWords() {
        return index.length; //words.value().length;
    }

    public String toString() {
        StringBuffer s = new StringBuffer("words: ");

        long[] wrds = words.value();
        int n = limit.value() + 1;
        s.append("limit = " + (n - 1) + "\n");
        for (int i = 0; i < n; i++) {
            int offset = index[i];
            s.append(offset + ": ");
            s.append(String.format("0x%08X", wrds[offset]));
            if (i < n - 1)
                s.append(", ");
        }

        s.append("\nmask: ");
        for (int i = 0; i < mask.length; i++) {
            s.append(i + ": ");
            s.append(String.format("0x%08X", mask[i]) + ", ");
        }
        return s.toString();
    }
}
